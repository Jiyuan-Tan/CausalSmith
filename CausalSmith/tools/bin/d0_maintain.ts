#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only sanction: mark an assumption as MAINTAINED — a disclosed,
 * high-level condition the note is stated CONDITIONAL on and does not derive (the
 * legitimate slot for "proved under condition A, where verifying A is itself the
 * open object", cf. a DML nuisance-rate condition). D0.5 checks the condition's
 * soundness and separateness and caps the tier one notch.
 *
 * Writes one direct commit (the tag + an honest_scope disclosure), then a directive
 * requiring every proved consumer to be restated explicitly conditional, and pins
 * the run at D0.
 *
 * Usage: d0_maintain.ts <qid> <spec> --assumption ass:<id> --reason "..." --open-object "..." --separate-object "..." [--dry-run]
 */
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { appendEscalationLog } from "../src/discovery/escalation_log.js";
import { dependentsOf } from "../src/discovery/core/graph_walk.js";
import { loadState, saveState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { assertNoUncommittedEdits, commitGraph, headGraph, publishCore } from "../src/discovery/vcs/commit.js";
import { META_ID, blobId, type NodeBlob } from "../src/discovery/vcs/node.js";
import { renderCore } from "../src/discovery/vcs/render.js";
import { formatViolations } from "../src/discovery/vcs/checks.js";
import { VcsStore } from "../src/discovery/vcs/store.js";
import { deriveStatus } from "../src/discovery/vcs/validity.js";

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  const dryRun = args.includes("--dry-run");
  const assId = cli.value("--assumption");
  const reason = cli.value("--reason");
  const openObject = cli.value("--open-object");
  const separateObject = cli.value("--separate-object");
  const [qid, spec] = cli.positionals();
  if (!qid || !spec || !assId || !reason || !openObject || !separateObject) {
    console.error('Usage: d0_maintain.ts <qid> <spec> --assumption ass:<id> --reason "..." --open-object "..." --separate-object "..." [--dry-run]');
    process.exitCode = 1;
    return;
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: false };
  await withRunHeartbeat(repoRoot, qid, spec, async () => {
    const store = VcsStore.at(ctx);
    await assertNoUncommittedEdits(ctx, store);
    const { head, graph } = await headGraph(store);
    const ass = graph.nodes.get(assId);
    if (ass?.node_type !== "assumption") throw new Error(`Assumption ${assId} not found on main`);
    const meta = graph.nodes.get(META_ID);
    if (meta?.node_type !== "meta") throw new Error("graph has no meta node");
    const core = renderCore(graph);
    const affected = [...dependentsOf(core, [assId])].filter((id) => core.statements.some((s) => s.id === id) && deriveStatus(graph, id) === "proved");
    if (dryRun) {
      console.log(`[dry-run] would mark ${assId} maintained; honest_scope disclosure + conditional-restate directive.`);
      console.log(affected.length > 0 ? `[dry-run] would direct a re-derivation of ${affected.length} consuming proof(s): ${affected.join(", ")}` : `[dry-run] no proved statement consumes ${assId}.`);
      return;
    }
    const { standard: _s, novel: _n, ...rest } = ass.body;
    const tagged: NodeBlob = { node_type: "assumption", body: { ...rest, maintained: { flag: true, reason, open_object: openObject, separate_object: separateObject, sanctioned_by: "orchestrator" } } };
    const disclosure = `OPEN (maintained condition ${assId}): ${openObject}`;
    const honest = typeof meta.body.honest_scope === "string" && meta.body.honest_scope.trim().length > 0
      ? `${meta.body.honest_scope.trimEnd()} ${disclosure}` : disclosure;
    const metaNext: NodeBlob = { node_type: "meta", body: { ...meta.body, honest_scope: honest } };
    const nodes = new Map(graph.nodes);
    nodes.set(assId, tagged);
    nodes.set(META_ID, metaNext);
    const tree = { ...graph.tree, [assId]: { ...graph.tree[assId], blob: blobId(tagged) }, [META_ID]: { ...graph.tree[META_ID], blob: blobId(metaNext) } };
    const result = await commitGraph({
      store, graph: { tree, nodes }, parents: [head], author: "orchestrator", kind: "direct",
      message: `maintained sanction on ${assId}: ${reason}`, expectedHead: head,
    });
    if (!result.ok) throw new Error(`maintained sanction refused:\n${formatViolations(result.violations)}`);
    await publishCore(ctx, store);
    const state = await loadState(repoRoot, qid, spec);
    await appendEscalationLog(ctx, {
      round: state.flags.d0_loop_counters?.solve_rounds ?? 0,
      directive:
        `ORCHESTRATOR MAINTAINED SANCTION on ${assId}. It is now a MAINTAINED (disclosed, high-level) condition ` +
        `the note is stated CONDITIONAL on and does NOT derive (open object: "${openObject}"; separate object: "${separateObject}"). ` +
        `RESTATE every headline theorem that consumes ${assId} to read EXPLICITLY "under ${assId}, ..."; ensure ${assId} is ` +
        `surfaced in honest_scope and posed as an oeq. Do NOT try to derive ${assId} or re-classify it standard/novel — it is a ` +
        `granted maintained condition; the result is honestly CONDITIONAL on it (tier capped one notch).`,
      note: `orchestrator maintained-sanction: ${assId}`,
      ...(affected.length > 0 ? { required_core_targets: affected } : {}),
    });
    state.stage_completed = "-0.5";
    await saveState(repoRoot, qid, spec, state);
    console.log(`Marked ${assId} MAINTAINED (commit ${result.id.slice(0, 12)}); honest_scope disclosure + conditional-restate directive logged.`);
    console.log(affected.length > 0 ? `Directed a re-derivation of ${affected.length} consuming proof(s): ${affected.join(", ")}` : `No proved statement consumes ${assId}; the directive dispatches the whole paper.`);
    console.log(`Reset stage. Re-run: causalsmith research --resume ${qid} ${spec} --auto --stop-after D0.5`);
  });
}

main().catch((err: unknown) => {
  console.error(`d0_maintain: ${err instanceof Error ? err.message : String(err)}`);
  process.exitCode = 1;
});
