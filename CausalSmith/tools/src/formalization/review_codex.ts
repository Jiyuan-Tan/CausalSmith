// The F1.5 plan review (reuse soundness), run by codex.

import { readFile } from "node:fs/promises";
import { MODEL_PLAN } from "../constants.js";
import { type ReviewResult } from "../judgment.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { parseTypedCore } from "../discovery/core/core_io.js";
import type { Core } from "../discovery/core/schema.js";
import { formalizationCoreContextValue } from "./core_context.js";
import { buildF2RevisionContext } from "./f2_revision_context.js";
import { PlanSchema, type Plan } from "./plan/schema.js";
import {
  BEYOND_SCOPE_KEY,
  beyondScopeReported,
  coreChangeSeeds,
  movedBeyondNodes,
  nodeReferenceIndex,
  planChangeSeeds,
  readReviseBasis,
  reviseLookupBlock,
  writeReviseBasis,
  type ReviseBasis,
} from "./revise_scope.js";
import { appendPipelineLog } from "../log.js";
import { planReviewedPath } from "../paths.js";
import { parseJsonWithEscapeRepair } from "../shared/codex_json.js";
import type { PipelineContext, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  bookkeepingPolicyBlock,
  parseReview,
  readRequired,
  readPrompt,
  type StageDeps,
} from "../pipeline_support.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";

const PROMPT_NAME = "stage1_5_reuse_soundness.txt";

/**
 * The context of the review of a RE-PLAN (a plan F1.5 passed before, patched since): the plan
 * entries that changed since that pass and the users of a changed premise
 * (`buildF2RevisionContext`), their core records, and a reference line for every other node — not
 * the whole plan again. Null when there is no record of the passed plan, when nothing a review
 * covers moved, or when the change is one no entry carries (an S-block among them): the review
 * then reads everything. Pure.
 */
export function replanReviewContext(args: {
  basis: ReviseBasis | null;
  planRaw: unknown;
  plan: Plan;
  core: Core;
  paths: { plan: string; core: string };
}): { block: string; changed: string[]; shown: number } | null {
  if (!args.basis) return null;
  const replanned = planChangeSeeds(args.basis.plan, args.planRaw);
  const view = formalizationCoreContextValue(args.core);
  const moved = coreChangeSeeds(args.basis.core, view);
  // A citation, another plan-level field, a removed entry, an S-block, or a setting of the core: no entry carries it.
  if (replanned.envs.length > 0 || movedBeyondNodes(args.basis, args.planRaw, view)) return null;
  const changed = [...new Set([...replanned.nodes, ...moved.nodes])];
  if (changed.some((id) => !(id in args.plan.nodes))) return null;
  const packet = buildF2RevisionContext(args.core, args.plan, changed);
  if (!packet) return null;
  const shown = new Set(Object.keys(packet.plan.nodes as Record<string, unknown>));
  const total = Object.keys(args.plan.nodes).length;
  const block = [
    "=== REVIEW OF A RE-PLAN (scoped) ===",
    "This plan was reviewed and passed before; it has been patched since. Review ONLY the entries shown in full",
    `below: the ${changed.length} that changed since that pass and the entries that cite a changed premise.`,
    "Every other entry is as it passed — a reference line here, not under review. The deterministic gate ran on the WHOLE plan.",
    `Changed since the pass: ${changed.join(", ")}`,
    "=== END REVIEW OF A RE-PLAN ===",
    "",
    `Formalization plan — the entries under review (${shown.size} of ${total} nodes):`,
    JSON.stringify(packet.plan),
    "",
    "Typed core JSON — the records of those nodes and the symbols they use (structural ground truth; proof/publication prose omitted):",
    JSON.stringify(packet.core),
    "",
    reviseLookupBlock({
      index: nodeReferenceIndex(args.core, args.plan, shown),
      shown: shown.size,
      total,
      corePath: args.paths.core,
      planPath: args.paths.plan,
      replyField: `your \`notes\` (a pass) or \`verbatim_critique\` (a revise), written \`${BEYOND_SCOPE_KEY}: [<ids>]\``,
    }),
  ].join("\n");
  return { block, changed, shown: shown.size };
}

/** The F1.5 reuse-soundness review: the formalization plan against the typed core. Both are
 *  required inputs (a missing one throws; see `readRequired`). */
export async function reviewWithCodex(
  args: { ctx: PipelineContext; state: StateJson; deps: StageDeps },
): Promise<ReviewResult> {
  const paths = artifactPaths(args.ctx, args.state);
  /** The plan as parsed and the core view, recorded when the review passes. */
  let reviewed: ReviseBasis | null = null;
  let scoped: ReturnType<typeof replanReviewContext> = null;
  const reviewedPath = planReviewedPath(args.ctx.repoRoot, args.ctx.qid);
  const corePath = coreJsonPath(args.ctx);
  const planText = await readRequired(paths.plan, "F1.5 review");
  let coreRaw: string;
  try {
    coreRaw = await readFile(corePath, "utf8");
  } catch (err) {
    throw new Error(`F1.5 review: required typed core is unreadable at ${corePath}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const core = parseTypedCore(coreRaw, `F1.5 review: typed core ${corePath}`);
  const coreView = formalizationCoreContextValue(core);
  try {
    const planRaw = parseJsonWithEscapeRepair(planText);
    reviewed = { plan: planRaw, core: coreView };
    const parsedPlan = PlanSchema.safeParse(planRaw);
    if (parsedPlan.success) {
      scoped = replanReviewContext({
        basis: await readReviseBasis(reviewedPath),
        planRaw,
        plan: parsedPlan.data,
        core,
        paths: { plan: paths.plan, core: corePath },
      });
    }
  } catch (err) {
    console.warn(`[causalsmith] F1.5: scoped re-plan review unavailable, reviewing the whole plan: ${err instanceof Error ? err.message : String(err)}`);
  }
  const scopeLine = scoped
    ? `F1.5 re-plan review carries ${scoped.shown} plan entr${scoped.shown === 1 ? "y" : "ies"} (${scoped.changed.length} changed since the passed plan)`
    : "F1.5 review carries the whole plan";
  console.warn(`[causalsmith] ${scopeLine}`);
  await appendPipelineLog(args.ctx, { stage: "1.5", status: "revise-scope", duration_ms: 0, message: scopeLine });
  const contextBlock = scoped?.block
    ?? `Formalization plan (plan.json — the subject of review):\n${planText}\n\nTyped core JSON (structural ground truth; proof/publication prose omitted):\n${JSON.stringify(coreView)}\n`;
  const noveltyHeader = args.ctx.noveltyTarget
    ? `novelty_target: ${args.ctx.noveltyTarget}\n`
    : "";
  // The shared bookkeeping policy keeps a regularity side-condition added by F1 from being
  // flagged as assumption-strengthening.
  const prompt = [
    (await readPrompt(args.ctx, PROMPT_NAME)) + `\n${bookkeepingPolicyBlock()}\n`,
    "",
    baseBrief(args.ctx, args.state),
    "",
    noveltyHeader + "Review the plan's per-node reuse decisions for type-fit and abstraction level.",
    "",
    "",
    "",
    "",
    contextBlock,
  ].join("\n");
  // lean-lsp is default-ON for every codex call (see shared/codex.ts) so the
  // reviewer's `lean_multi_attempt` vacuity probes are actually available.
  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "1.5",
    label: `F1.5 review (${PROMPT_NAME})`,
    prompt,
    promptSources: [PROMPT_NAME, "baseBrief", paths.plan, corePath],
    model: MODEL_PLAN.stage1_5.model,
    reasoningEffort: MODEL_PLAN.stage1_5.effort,
  });
  const review = parseReview(out.stdout);
  // The mechanical affected set under-reached: say where, so the rule can be widened.
  const beyond = scoped ? beyondScopeReported(out.stdout) : [];
  if (beyond.length > 0) {
    const message = `F1.5 re-plan review looked up ${beyond.length} node(s) beyond the affected set (${scoped!.shown}): ${beyond.join(", ")}`;
    await appendPipelineLog(args.ctx, { stage: "1.5", status: "revise-scope", duration_ms: 0, message });
    console.warn(`[causalsmith] ${message}`);
  }
  // The plan and core that passed: the review of the next re-plan covers what moved since.
  if (reviewed && (review.status === "pass" || review.status === "accept")) {
    await writeReviseBasis(reviewedPath, reviewed);
  }
  return review;
}
