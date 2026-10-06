// Cluster routing + setup-block loading for the D0 solve round (`vcs/round.ts`).
// Pure routing/prompt-assembly — no codex.

import type { PipelineContext, StateJson } from "../types.js";
import { readPrompt } from "../pipeline_support.js";

export type Cluster = "panel" | "exactid" | "partialid" | "stat" | "experimentation" | "scm";

export function clusterFor(ctx: PipelineContext, state: StateJson): Cluster | null {
  const fromState = state.proposed_from?.cluster;
  if (fromState === "panel" || fromState === "exactid" || fromState === "partialid" || fromState === "stat" || fromState === "experimentation" || fromState === "scm") return fromState;
  // Fallback: qid prefix convention.
  //   eid_*    → exactid
  //   pid_*    → partialid
  //   stat_*   → stat (estimation and inference theory of a causal estimand)
  //   panel_*  → panel (free-form panel kernel)
  const qid = ctx.qid.toLowerCase();
  if (qid.startsWith("eid_")) return "exactid";
  if (qid.startsWith("pid_")) return "partialid";
  if (qid.startsWith("stat_")) return "stat";
  if (qid.startsWith("exp_")) return "experimentation";
  if (qid.startsWith("scm_")) return "scm";
  if (qid.startsWith("panel_")) return "panel";
  return null;
}

/** The cluster setup block: the math setup a D-stage solver sees for its cluster.
 * D stages reason about the natural-language mathematics ONLY. These prompts must not
 * name Causalean/Mathlib paths, declarations, or "what the library already has" —
 * doing so once put a Lean declaration into a paper's prose proof (df458618d).
 * Formalization substrate is an F-stage concern. */
export async function loadClusterSetupBlock(
  ctx: PipelineContext,
  cluster: Cluster | null,
): Promise<string> {
  if (cluster === "panel") return readPrompt(ctx, "stage0_setup_panel.txt");
  if (cluster === "exactid") return readPrompt(ctx, "stage0_setup_exactid.txt");
  if (cluster === "partialid") return readPrompt(ctx, "stage0_setup_partialid.txt");
  if (cluster === "stat") return readPrompt(ctx, "stage0_setup_stat.txt");
  if (cluster === "experimentation") return readPrompt(ctx, "stage0_setup_experimentation.txt");
  if (cluster === "scm") return readPrompt(ctx, "stage0_setup_scm.txt");
  // Unknown cluster: inject all six so the model can pick from the locked-parameter tuple itself.
  const [a, b, c, d, e, f] = await Promise.all([
    readPrompt(ctx, "stage0_setup_panel.txt"),
    readPrompt(ctx, "stage0_setup_exactid.txt"),
    readPrompt(ctx, "stage0_setup_partialid.txt"),
    readPrompt(ctx, "stage0_setup_stat.txt"),
    readPrompt(ctx, "stage0_setup_experimentation.txt"),
    readPrompt(ctx, "stage0_setup_scm.txt"),
  ]);
  return [a, "", b, "", c, "", d, "", e, "", f].join("\n");
}
