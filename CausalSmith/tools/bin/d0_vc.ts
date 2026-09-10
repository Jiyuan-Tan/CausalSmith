#!/usr/bin/env -S npx tsx
/**
 * The D0 theorem graph under version control. `core.json` is the working copy:
 * edit it, then commit. Nothing is ever lost — every commit is kept, and a reset
 * is itself a commit.
 *
 *   d0_vc.ts <qid> <spec> migrate                          bring an existing run onto the store (idempotent; what --resume does itself)
 *   d0_vc.ts <qid> <spec> init [--from-core <core.json>]   initialize from a specific core file
 *   d0_vc.ts <qid> <spec> status                           diff core.json against main; stale proofs
 *   d0_vc.ts <qid> <spec> commit --note "<why>" [--check]  commit the edited core.json to main
 *   d0_vc.ts <qid> <spec> log [-n N]                       history of main
 *   d0_vc.ts <qid> <spec> show <commit> [--core <out>]     one commit (or write its rendered core)
 *   d0_vc.ts <qid> <spec> diff <a> <b>                     node-level diff between two commits
 *   d0_vc.ts <qid> <spec> reset <commit> --note "<why>"    make main render that commit's tree
 *   d0_vc.ts <qid> <spec> render                           rewrite core.json from main (drops edits)
 *   d0_vc.ts <qid> <spec> fsck                             verify every object, commit and ref
 *
 *   d0_vc.ts <qid> <spec> pr list                          open pull requests (solver rounds awaiting a verdict)
 *   d0_vc.ts <qid> <spec> pr show <pr>                     the diff, what needs approval, and why
 *   d0_vc.ts <qid> <spec> pr merge <pr> --accept all|<id,…> [--reject <id,…>] [--keep-main <id,…>] [--keep-pr <id,…>] --note "<why>"
 *   d0_vc.ts <qid> <spec> pr close <pr> --note "<why>"     discard the round (its head stays in history)
 *
 * A commit is refused, and nothing written, when the edited core fails the
 * structural gate; the message lists every violation. Proofs whose closure you
 * changed simply become to-prove at the next render (delete a proof to reopen it
 * by hand); nothing else needs to be told.
 */
import { existsSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { readTypedCore } from "../src/discovery/core/core_io.js";
import { coreJsonPath } from "../src/discovery/stages/d0_core.js";
import { formatViolations } from "../src/discovery/vcs/checks.js";
import { assertCoreRendersMain, commitGraph, coreMatchesGraph, headGraph, publishCore } from "../src/discovery/vcs/commit.js";
import { initStoreFromRun } from "../src/discovery/vcs/convert.js";
import { ensureStore } from "../src/discovery/vcs/round.js";
import { loadState, saveState } from "../src/state.js";
import { diffGraphs, isEmptyDiff, loadGraph, type GraphDiff } from "../src/discovery/vcs/graph.js";
import { graphFromCore, renderCore } from "../src/discovery/vcs/render.js";
import { MAIN_REF, VcsStore, type Commit } from "../src/discovery/vcs/store.js";
import { staleProofs, openStatements } from "../src/discovery/vcs/validity.js";
import { closePr, describePr, listPrs, mergePr, readPr, reapplyPr } from "../src/discovery/vcs/pr.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";

const USAGE = "usage: d0_vc.ts <qid> <spec> <migrate|init|status|commit|log|show|diff|reset|render|fsck|pr list|pr show|pr merge|pr reapply|pr close> [...]";

export function formatDiff(d: GraphDiff): string {
  const lines: string[] = [];
  for (const id of d.added) lines.push(`  + ${id}`);
  for (const id of d.removed) lines.push(`  - ${id}`);
  for (const c of d.changed) lines.push(`  ~ ${c.id}${c.content ? " [content]" : ""} (${c.fields.join(", ")})`);
  if (d.moved.length > 0) lines.push(`  ↕ ${d.moved.length} node(s) reordered`);
  return lines.length > 0 ? lines.join("\n") : "  (no changes)";
}

function formatCommit(c: Commit): string {
  const short = c.id.slice(0, 12);
  const parents = c.parents.map((p) => p.slice(0, 12)).join(" ") || "-";
  return `${short}  ${c.time}  ${c.kind.padEnd(7)}  ${c.author.padEnd(14)}  ${c.message}  (parents: ${parents})`;
}

export async function main(argv: string[] = process.argv.slice(2)): Promise<void> {
  const args = [...argv];
  const take = (flag: string): string | undefined => {
    const i = args.indexOf(flag);
    if (i === -1) return undefined;
    const value = args[i + 1];
    if (value === undefined || value.startsWith("--")) throw new Error(`${flag} requires a value`);
    args.splice(i, 2);
    return value;
  };
  const has = (flag: string): boolean => {
    const i = args.indexOf(flag);
    if (i === -1) return false;
    args.splice(i, 1);
    return true;
  };
  const note = take("--note");
  const fromCore = take("--from-core");
  const coreOut = take("--core");
  const limit = take("-n");
  const accept = take("--accept");
  const rejectList = take("--reject");
  const keepMain = take("--keep-main");
  const keepPr = take("--keep-pr");
  const checkOnly = has("--check");
  const [qid, spec, command, ...rest] = args;
  if (!qid || !spec || !command) throw new Error(USAGE);
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: false };
  const store = VcsStore.at(ctx);
  const out = (s: string): void => { console.log(s); };

  switch (command) {
    case "init": {
      await withRunHeartbeat(repoRoot, qid, spec, async () => {
        const source = fromCore !== undefined
          ? { core: await readTypedCore(fromCore), tombstones: [], origin: path.basename(fromCore) }
          : undefined;
        const { id, origin } = await initStoreFromRun(ctx, source);
        await publishCore(ctx, store);
        out(`initialized ${store.dir}\nmain = ${id}\nfrom ${origin}; core.json rendered`);
      });
      return;
    }
    case "migrate": {
      await withRunHeartbeat(repoRoot, qid, spec, async () => {
        const state = await loadState(repoRoot, qid, spec);
        const existed = store.exists();
        await ensureStore(ctx, state);
        await saveState(repoRoot, qid, spec, state);
        const head = await store.readRef(MAIN_REF);
        out(existed ? `already on the store; main = ${head}` : `migrated; main = ${head}; core.json rendered`);
      });
      return;
    }
    case "status": {
      await assertCoreRendersMain(ctx, store);
      const { head, graph } = await headGraph(store);
      out(`main = ${head}`);
      const recorded = (await store.readCommit(head)).meta?.violations;
      if (Array.isArray(recorded) && recorded.length > 0) {
        out(`main carries ${recorded.length} recorded check violation(s) from conversion — fix them in core.json and commit:\n${formatViolations(recorded as Parameters<typeof formatViolations>[0])}`);
      }
      const corePath = coreJsonPath(ctx);
      if (!existsSync(corePath)) { out("core.json is missing (run `render`)"); return; }
      const core = await readTypedCore(corePath);
      const matches = coreMatchesGraph(core, graph);
      const edited = graphFromCore(core, graph);
      const diff = diffGraphs(graph, edited);
      out(matches ? "core.json matches main" :
        `core.json differs from main:${isEmptyDiff(diff) ? "\n  working-copy change would be erased by graph normalization" : `\n${formatDiff(diff)}`}`);
      const stale = staleProofs(graph);
      if (stale.length > 0) out(`stale proofs on main:\n${stale.map((s) => `  ${s.id} (moved: ${s.stale.join(", ")})`).join("\n")}`);
      const open = openStatements(graph);
      out(`open statements on main: ${open.length === 0 ? "none" : open.join(", ")}`);
      return;
    }
    case "commit": {
      if (note === undefined) throw new Error('commit needs --note "<what and why>"');
      const run = async (): Promise<void> => {
        await assertCoreRendersMain(ctx, store);
        const { head, graph } = await headGraph(store);
        const core = await readTypedCore(coreJsonPath(ctx));
        if (coreMatchesGraph(core, graph)) { out("nothing to commit: core.json matches main"); return; }
        const edited = graphFromCore(core, graph);
        const diff = diffGraphs(graph, edited);
        if (isEmptyDiff(diff)) {
          out("REFUSED (nothing written): core.json differs from main, but graph normalization would erase the edit");
          process.exitCode = 1;
          return;
        }
        out(`changes:\n${formatDiff(diff)}`);
        const result = await commitGraph({
          store, graph: edited, parents: [head], author: "orchestrator", kind: "direct", message: note,
          expectedHead: head, detached: checkOnly,
        });
        if (!result.ok) {
          out(`REFUSED (nothing written):\n${formatViolations(result.violations)}`);
          process.exitCode = 1;
          return;
        }
        if (checkOnly) { out(`check passed (would commit ${result.id.slice(0, 12)}); main unchanged`); return; }
        await publishCore(ctx, store);
        const stale = staleProofs(result.graph);
        out(`committed ${result.id}\ncore.json re-rendered${stale.length > 0 ? `\nproofs now stale: ${stale.map((s) => s.id).join(", ")}` : ""}`);
      };
      if (checkOnly) await run(); else await withRunHeartbeat(repoRoot, qid, spec, run);
      return;
    }
    case "log": {
      const head = await store.readRef(MAIN_REF);
      if (head === null) throw new Error("no main commit");
      const n = limit !== undefined ? Number(limit) : 20;
      for (const c of await store.history(head, n)) out(formatCommit(c));
      return;
    }
    case "show": {
      const [ref] = rest;
      if (!ref) throw new Error("show needs a commit");
      const id = await store.resolve(ref);
      const commit = await store.readCommit(id);
      out(formatCommit(commit));
      if (commit.meta !== undefined) out(`meta: ${JSON.stringify(commit.meta)}`);
      const graph = await loadGraph(store, id);
      if (coreOut !== undefined) {
        await writeJsonAtomic(coreOut, renderCore(graph));
        out(`rendered core written to ${coreOut}`);
      } else {
        const counts = new Map<string, number>();
        for (const blob of graph.nodes.values()) counts.set(blob.node_type, (counts.get(blob.node_type) ?? 0) + 1);
        out([...counts].map(([t, n]) => `${t}: ${n}`).join(", "));
        out(`open statements: ${openStatements(graph).join(", ") || "none"}`);
      }
      return;
    }
    case "diff": {
      const [a, b] = rest;
      if (!a || !b) throw new Error("diff needs two commits");
      const ga = await loadGraph(store, a);
      const gb = await loadGraph(store, b);
      out(formatDiff(diffGraphs(ga, gb)));
      return;
    }
    case "reset": {
      const [ref] = rest;
      if (!ref) throw new Error("reset needs a commit");
      if (note === undefined) throw new Error('reset needs --note "<why>"');
      await withRunHeartbeat(repoRoot, qid, spec, async () => {
        const target = await store.resolve(ref);
        const { head } = await headGraph(store);
        const graph = await loadGraph(store, target);
        const result = await commitGraph({
          store, graph, parents: [head], author: "orchestrator", kind: "reset", message: note,
          expectedHead: head, meta: { target },
        });
        if (!result.ok) { out(`REFUSED:\n${formatViolations(result.violations)}`); process.exitCode = 1; return; }
        await publishCore(ctx, store);
        out(`main = ${result.id} (tree of ${target.slice(0, 12)}); core.json re-rendered`);
      });
      return;
    }
    case "render": {
      await withRunHeartbeat(repoRoot, qid, spec, async () => {
        const head = await publishCore(ctx, store);
        out(`core.json rendered from ${head}`);
      });
      return;
    }
    case "fsck": {
      const problems: string[] = [];
      for (const id of await store.listObjectIds()) {
        try { await store.readBlob(id); } catch (err) { problems.push(err instanceof Error ? err.message : String(err)); }
      }
      const commits = await store.listCommitIds();
      for (const id of commits) {
        try {
          const c = await store.readCommit(id);
          for (const p of c.parents) if (!store.hasCommit(p)) problems.push(`commit ${id} parent ${p} missing`);
          for (const [nodeId, e] of Object.entries(c.tree)) if (!store.hasBlob(e.blob)) problems.push(`commit ${id} node ${nodeId} object ${e.blob} missing`);
        } catch (err) { problems.push(err instanceof Error ? err.message : String(err)); }
      }
      const head = await store.readRef(MAIN_REF);
      if (head === null) problems.push("no main ref");
      else if (!store.hasCommit(head)) problems.push(`main points at missing commit ${head}`);
      out(problems.length === 0 ? `ok: ${commits.length} commit(s), main = ${head}` : `PROBLEMS:\n${problems.map((p) => `  ${p}`).join("\n")}`);
      if (problems.length > 0) process.exitCode = 1;
      return;
    }
    case "pr": {
      const [sub, ref] = rest;
      if (sub === "list") {
        const open = await listPrs(store, "open");
        if (open.length === 0) { out("no open pull requests"); return; }
        for (const pr of open) out(`${pr.id.slice(0, 12)}  round ${pr.round}  base ${pr.base.slice(0, 12)}  approval items: ${pr.approval.length}  (+${pr.summary.added.length} −${pr.summary.removed.length} ~${pr.summary.changed.length})`);
        return;
      }
      if (!ref) throw new Error("pr <show|merge|reapply|close> needs a PR id");
      const pr = await readPr(store, ref);
      if (sub === "show") {
        out(describePr(pr, await loadGraph(store, pr.base), await loadGraph(store, pr.id)));
        return;
      }
      if (sub === "reapply") {
        // Replay the round's raw solver outputs against the current main as a new PR
        // (the original is closed as superseded): the path after fixing on main what a
        // DID NOT LAND reason named.
        await withRunHeartbeat(repoRoot, qid, spec, async () => {
          const main = await store.resolve(MAIN_REF);
          const { pr: next, head } = await reapplyPr(store, pr, { base: main, ...(note !== undefined ? { note } : {}) });
          out(`reapplied PR ${pr.id.slice(0, 12)} as ${next.id.slice(0, 12)} on main ${main.slice(0, 12)}`);
          out(describePr(next, await loadGraph(store, next.base), head));
        });
        return;
      }
      if (sub === "close") {
        if (note === undefined) throw new Error('pr close needs --note "<why>"');
        await withRunHeartbeat(repoRoot, qid, spec, async () => { await closePr(store, pr, note); });
        out(`closed PR ${pr.id.slice(0, 12)}; main unchanged`);
        return;
      }
      if (sub === "merge") {
        if (note === undefined) throw new Error('pr merge needs --note "<why>"');
        if (accept === undefined) throw new Error("pr merge needs --accept all|<id,…> (and optionally --reject <id,…>)");
        const ids = (s: string | undefined): string[] => (s ?? "").split(",").map((x) => x.trim()).filter((x) => x.length > 0);
        await withRunHeartbeat(repoRoot, qid, spec, async () => {
          const conflicts: Record<string, "main" | "pr"> = {};
          for (const id of ids(keepMain)) conflicts[id] = "main";
          for (const id of ids(keepPr)) conflicts[id] = "pr";
          const result = await mergePr({
            store, ctx, pr,
            verdict: { accept: accept === "all" ? "all" : ids(accept), reject: ids(rejectList), conflicts, note, by: "adjudicator" },
          });
          if (!result.ok) {
            if (result.unresolved.length > 0) {
              const conflicts = result.unresolved.filter((u) => u.kind === "conflict");
              const checks = result.unresolved.filter((u) => u.kind === "check");
              out("REFUSED (nothing merged):");
              if (conflicts.length > 0) {
                out(`  ${conflicts.length} node(s) changed on main after this PR's base — decide per node with --keep-main <ids> / --keep-pr <ids>:`);
                for (const u of conflicts) {
                  out(`    ${u.id}: ${u.reason}`);
                  if (u.main) out(`        main: ${JSON.stringify(u.main.body).slice(0, 200)}`);
                  if (u.pr) out(`        pr:   ${JSON.stringify(u.pr.body).slice(0, 200)}`);
                }
              }
              if (checks.length > 0) {
                out(`  ${checks.length} node(s) do not stand with the chosen sides — merge them by hand on main (edit core.json, commit), then run this merge again with --keep-main for them:`);
                for (const u of checks) out(`    ${u.id}: ${u.reason}`);
              }
            } else {
              out(`REFUSED (nothing merged):\n${formatViolations(result.violations)}`);
            }
            process.exitCode = 1;
            return;
          }
          if (pr.journal_length !== undefined) {
            const state = await loadState(repoRoot, qid, spec);
            state.flags.d0_directives_consumed = Math.max(state.flags.d0_directives_consumed ?? 0, pr.journal_length);
            await saveState(repoRoot, qid, spec, state);
          }
          out(`merged PR ${pr.id.slice(0, 12)} as ${result.commit.slice(0, 12)}; core.json re-rendered` +
            (result.conflicts.length > 0 ? `\nconflicts dropped: ${result.conflicts.map((c) => `${c.id} (${c.reason})`).join("; ")}` : ""));
        });
        return;
      }
      throw new Error(`unknown pr subcommand '${sub}'`);
    }
    default:
      throw new Error(`unknown command '${command}'\n${USAGE}`);
  }
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main().catch((err: unknown) => {
    console.error(`d0_vc: ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  });
}
