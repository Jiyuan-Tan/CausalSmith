// The versioned theorem graph: making a commit, and publishing the view.
//
// `commitGraph` is the single write path: normalize → check → write objects →
// write commit → move the ref by compare-and-swap. A refused tree writes nothing.
// `publishCore` renders `main` to `core.json` (the F stages' input and the
// orchestrator's working copy). Callers never touch the store directly.
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { writeJsonAtomic, writeTextAtomic } from "../../shared/json_atomic.js";
import { stableJson } from "../../shared/stable_json.js";
import type { Core } from "../core/schema.js";
import type { PipelineContext } from "../../types.js";
import { coreJsonPath } from "../stages/d0_core.js";
import { checkGraph, formatViolations, type Violation } from "./checks.js";
import { diffGraphs, isEmptyDiff, loadGraph, type Graph } from "./graph.js";
import { readTypedCore } from "../core/core_io.js";
import { graphFromCore, renderCore, normalizeGraph } from "./render.js";
import { MAIN_REF, VcsStore, type CommitKind } from "./store.js";

export interface CommitArgs {
  store: VcsStore;
  graph: Graph;
  parents: string[];
  author: string;
  kind: CommitKind;
  message: string;
  /** What `main` must hold for the move to be legal (null = store is empty). */
  expectedHead: string | null;
  meta?: Record<string, unknown>;
  /** Write the commit object but leave `main` where it is (a PR head). */
  detached?: boolean;
  /** Conversion only: a run whose published core already fails a check must still
   *  get a store, or it can never be resumed. The violations are recorded on the
   *  commit (`meta.violations`) and reported by `status`; the next commit fixes them. */
  recordViolations?: boolean;
}

export type CommitResult =
  | { ok: true; id: string; graph: Graph }
  | { ok: false; violations: Violation[] };

export async function commitGraph(args: CommitArgs): Promise<CommitResult> {
  const graph = normalizeGraph(args.graph);
  const check = checkGraph(graph);
  if (!check.ok && !(args.recordViolations && (args.kind === "initial" || args.kind === "reset"))) return { ok: false, violations: check.violations };
  const meta = { ...(args.meta ?? {}), ...(check.ok ? {} : { violations: check.violations }) };
  await args.store.init();
  for (const blob of graph.nodes.values()) await args.store.writeBlob(blob);
  const id = await args.store.writeCommit({
    parents: args.parents,
    tree: graph.tree,
    author: args.author,
    kind: args.kind,
    message: args.message,
    time: new Date().toISOString(),
    ...(Object.keys(meta).length > 0 ? { meta } : {}),
  });
  if (!args.detached) await args.store.updateRef(MAIN_REF, id, args.expectedHead, `${args.kind}: ${args.message}`);
  return { ok: true, id, graph };
}

export class CommitRefused extends Error {
  constructor(readonly violations: Violation[]) {
    super(`vcs: commit refused\n${formatViolations(violations)}`);
  }
}

export async function commitOrThrow(args: CommitArgs): Promise<{ id: string; graph: Graph }> {
  const result = await commitGraph(args);
  if (!result.ok) throw new CommitRefused(result.violations);
  return result;
}

/** Render `main` to `core.json`. Returns the commit rendered. */
export async function publishCore(ctx: PipelineContext, store: VcsStore = VcsStore.at(ctx)): Promise<string> {
  const head = await store.readRef(MAIN_REF);
  if (head === null) throw new Error("vcs: nothing to publish (no main commit)");
  const graph = await loadGraph(store, head);
  await writeJsonAtomic(coreJsonPath(ctx), renderCore(graph));
  // Which commit core.json renders. A crash between a ref move and the render leaves
  // the file behind main; every reader of core.json as a working copy checks this.
  await writeTextAtomic(renderedMainPath(store), `${head}\n`);
  return head;
}

export function renderedMainPath(store: VcsStore): string {
  return path.join(store.dir, "rendered_main");
}

/** The commit core.json was last rendered from, or null when unknown. */
export async function renderedMain(store: VcsStore): Promise<string | null> {
  const p = renderedMainPath(store);
  if (!existsSync(p)) return null;
  const value = (await readFile(p, "utf8")).trim();
  return /^[a-f0-9]{64}$/.test(value) ? value : null;
}

/** Compare the working Core view before graph normalization can erase an edit. */
export function coreMatchesGraph(core: Core, graph: Graph): boolean {
  return stableJson(core) === stableJson(renderCore(graph));
}

/** Refuse to treat core.json as a working copy when it does not render main. */
export async function assertCoreRendersMain(ctx: PipelineContext, store: VcsStore): Promise<string> {
  const head = await store.readRef(MAIN_REF);
  if (head === null) throw new Error("vcs: store has no main commit");
  const rendered = await renderedMain(store);
  if (rendered !== null && rendered !== head) {
    throw new Error(
      `core.json renders ${rendered.slice(0, 12)} but main is ${head.slice(0, 12)} (a render was interrupted): ` +
        `run \`d0_vc.ts ${ctx.qid} ${ctx.specialization} render\`, then re-apply your edit`,
    );
  }
  return head;
}

/** Refuse to overwrite an orchestrator's uncommitted edit of core.json: a writer that
 *  is about to commit its own change and re-render must find the working copy equal
 *  to main (or absent) first. */
export async function assertNoUncommittedEdits(ctx: PipelineContext, store: VcsStore): Promise<void> {
  const head = await assertCoreRendersMain(ctx, store);
  const corePath = coreJsonPath(ctx);
  if (!existsSync(corePath)) return;
  const graph = await loadGraph(store, head);
  const core = await readTypedCore(corePath);
  if (coreMatchesGraph(core, graph)) return;
  const edited = graphFromCore(core, graph);
  const diff = diffGraphs(graph, edited);
  throw new Error(
    `core.json carries uncommitted edits (${[...diff.added, ...diff.removed, ...diff.changed.map((c) => c.id)].join(", ") || "a change erased by graph normalization"}): ` +
      `commit them first (d0_vc.ts ${ctx.qid} ${ctx.specialization} commit --note "…") or discard them (render)`,
  );
}

export async function headGraph(store: VcsStore): Promise<{ head: string; graph: Graph }> {
  const head = await store.readRef(MAIN_REF);
  if (head === null) throw new Error("vcs: store has no main commit");
  return { head, graph: await loadGraph(store, head) };
}
