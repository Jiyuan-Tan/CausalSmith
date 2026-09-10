/** Typed, fail-closed completion of F→D0 rewind intents, on the graph store.
 *
 *   incremental_repair — the accepted paper is repaired in place: a directive.
 *   extension          — a new D-1.2 proposal revision extends the accepted paper:
 *                        every accepted node must survive unchanged; the new nodes
 *                        are committed onto main and opened for solving.
 *   replacement        — handled by the ordinary D-1.2 path (no carry).
 */
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import type { PipelineContext, StateJson } from "../../types.js";
import { coreNodeIds } from "../core/schema.js";
import { readTypedCore } from "../core/core_io.js";
import { coreJsonPath } from "./d0_core.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import { appendEscalationLog, readEscalationLog } from "../escalation_log.js";
import { proposalRevision } from "../proposal_revision.js";
import { commitGraph, headGraph, publishCore } from "../vcs/commit.js";
import { ensureStore } from "../vcs/round.js";
import { graphFromCore } from "../vcs/render.js";
import { formatViolations } from "../vcs/checks.js";
import { contentKey, nodeTypeOf } from "../vcs/node.js";

const sha256 = (text: string): string => createHash("sha256").update(text).digest("hex");

/**
 * Detect a pre-fix F→D state already parked at D-1.2. The old receipt records
 * only that `stage_0` was requested, not whether it meant repair, extension, or
 * replacement, so no conversion is logically justified.
 */
export function legacyCrossBoundaryRewindGuard(state: StateJson): string | null {
  if (
    state.stage_completed !== "-1.2" ||
    state.flags.rewound_from_stage0 === undefined ||
    state.flags.rewound_from_stage0 === null ||
    state.flags.d0_cross_boundary_rewind
  ) return null;
  const message =
    "legacy cross-boundary stage_0 rewind has no typed intent; refusing to review/edit the pre-D0 proto. " +
    "Classify it explicitly as incremental_repair, extension, or replacement before resuming.";
  state.flags.stage0_rewind_intent_required = message;
  return message;
}

/** Seal the accepted source before the extension author sees it. Idempotent on resume. */
export async function sealPendingExtensionSource(args: { ctx: PipelineContext; state: StateJson }): Promise<void> {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  if (!receipt || receipt.intent !== "extension" || receipt.status !== "pending") return;
  const revision = proposalRevision(args.state);
  if (revision !== receipt.source_revision) return; // already authored at least once
  const coreBytes = await readFile(coreJsonPath(args.ctx), "utf8");
  const core = await readTypedCore(coreJsonPath(args.ctx));
  const ids = [...coreNodeIds(core)].sort();
  if (receipt.source_core_sha256 && receipt.source_core_sha256 !== sha256(coreBytes)) {
    throw new Error("extension rewind source core changed after it was sealed");
  }
  if (receipt.source_ids && JSON.stringify(receipt.source_ids) !== JSON.stringify(ids)) {
    throw new Error("extension rewind source node set changed after it was sealed");
  }
  receipt.source_core_sha256 = sha256(coreBytes);
  receipt.source_ids = ids;
}

/** D-1.2's edit base: the first extension draft edits the accepted D0 core, never
 *  the stale pre-D0 proto; later revise rounds edit their prior extension proposal. */
export function extensionEditBasePath(args: { ctx: PipelineContext; state: StateJson; ordinaryProtoPath: string }): string {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  return receipt?.intent === "extension" && receipt.status === "pending" && proposalRevision(args.state) === receipt.source_revision
    ? coreJsonPath(args.ctx)
    : args.ordinaryProtoPath;
}

/** Consume an incremental repair as a D0 directive. */
export async function consumePendingIncrementalRewind(args: { ctx: PipelineContext; state: StateJson }): Promise<void> {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  if (!receipt || receipt.intent !== "incremental_repair" || receipt.status !== "pending") return;
  if (proposalRevision(args.state) !== receipt.source_revision) {
    throw new Error("incremental D0 rewind refuses a changed proposal revision");
  }
  const marker = `[CROSS-BOUNDARY D0 INCREMENTAL ${sha256(JSON.stringify(receipt)).slice(0, 16)}]`;
  const journal = await readEscalationLog(args.ctx);
  if (!journal.some((entry) => entry.directive?.includes(marker))) {
    await appendEscalationLog(args.ctx, {
      round: args.state.flags.d0_loop_counters?.solve_rounds ?? 0,
      directive:
        `${marker} Repair the accepted D0 paper in place; do not replace the accepted claim catalogue. ` +
        `Root-cause directive: ${receipt.reason}`,
    });
  }
  delete args.state.flags.d0_cross_boundary_rewind;
  args.state.flags.rewound_from_stage0 = null;
}

/**
 * Before the first D0 solve of an extension, commit the extension proposal's new
 * nodes onto main. Every accepted node must be present and content-identical in the
 * extension proto; omission or mutation aborts before main is touched.
 */
export async function finalizePendingExtensionRebase(args: { ctx: PipelineContext; state: StateJson }): Promise<void> {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  if (!receipt || receipt.intent !== "extension" || receipt.status !== "pending") return;
  const extensionRevision = proposalRevision(args.state);
  if (!extensionRevision || extensionRevision === receipt.source_revision) {
    throw new Error("extension D0 rewind reached solve before an extension proposal revision was authored");
  }
  const sourceCoreBytes = await readFile(coreJsonPath(args.ctx), "utf8");
  if (!receipt.source_core_sha256 || sha256(sourceCoreBytes) !== receipt.source_core_sha256) {
    throw new Error("extension D0 rewind accepted-core basis changed; refusing rebase");
  }
  const store = await ensureStore(args.ctx, args.state);
  const { head, graph: accepted } = await headGraph(store);
  const extension = graphFromCore(await readTypedCore(protoCoreJsonPath(args.ctx)), accepted);
  const missing: string[] = [];
  const mutated: string[] = [];
  for (const [id, blob] of accepted.nodes) {
    if (nodeTypeOf(id) === "meta" || nodeTypeOf(id) === "bib") continue;
    if (blob.node_type === "statement" && blob.body.resolved_by !== undefined) continue;
    const ext = extension.nodes.get(id);
    if (ext === undefined) missing.push(id);
    else if (contentKey(ext) !== contentKey(blob)) mutated.push(id);
  }
  if (missing.length > 0 || mutated.length > 0) {
    throw new Error(
      `extension D0 rewind refuses the extension proposal: ` +
        `${missing.length > 0 ? `accepted node(s) omitted: ${missing.join(", ")}` : ""}` +
        `${missing.length > 0 && mutated.length > 0 ? "; " : ""}` +
        `${mutated.length > 0 ? `accepted node(s) mutated: ${mutated.join(", ")}` : ""}`,
    );
  }
  // Accepted nodes keep their accepted versions (proofs included); everything else
  // comes from the extension proposal.
  const nodes = new Map(extension.nodes);
  const tree = { ...extension.tree };
  for (const [id, blob] of accepted.nodes) {
    if (nodes.has(id)) { nodes.set(id, blob); tree[id] = { ...tree[id], blob: accepted.tree[id].blob }; }
  }
  const added = [...nodes.keys()].filter((id) => !accepted.nodes.has(id));
  const result = await commitGraph({
    store, graph: { tree, nodes }, parents: [head], author: "pipeline", kind: "direct",
    message: `extension rebase: ${added.length} new node(s) onto the accepted paper — ${receipt.reason}`, expectedHead: head,
    meta: { added, extension_revision: extensionRevision, source_revision: receipt.source_revision },
  });
  if (!result.ok) throw new Error(`extension rebase refused:\n${formatViolations(result.violations)}`);
  await publishCore(args.ctx, store);
  delete args.state.flags.d0_cross_boundary_rewind;
  args.state.flags.rewound_from_stage0 = null;
  console.warn(`[D0] completed extension rebase ${result.id.slice(0, 12)}: preserved ${accepted.nodes.size}, added ${added.length}`);
}
