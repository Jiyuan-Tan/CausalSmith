// F1.5 — the REUSE-SOUNDNESS review boundary.
//
// The deterministic plan gate (plan_gate.ts) owns one-to-one coverage / kind /
// member / hyp-closure / reuse-existence / module checks. F1.5 runs that gate as a
// pre-lint (a violation routes straight back to F1, no LLM spent), then an LLM
// reviews the judgment the gate cannot make: does each chosen reuse decl type-fit
// at the right abstraction level, and is each define-local justified.

import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import type { ReviewResult } from "../judgment.js";
import { type StageDeps, artifactPaths, readRequired } from "../pipeline_support.js";
import { reviewWithCodex } from "./review_codex.js";
import { runReviewBoundary } from "../shared/review_boundary.js";
import { runStage1 } from "./stage1.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { parseTypedCore } from "../discovery/core/core_io.js";
import { runPlanGate } from "../formalization/plan/plan_gate.js";
import { createRetrieval } from "../formalization/reuse_retrieval.js";
import { parseJsonWithEscapeRepair } from "../shared/codex_json.js";

/** Run the deterministic plan gate over the just-written plan. Returns a synthetic
 *  `revise` verdict (routing F1 to fix the mechanical violations) when it fails, or
 *  `null` when the plan is gate-clean. core.json is REQUIRED (throws via
 *  readRequired if missing/unparseable); a missing plan.json still routes back to
 *  F1 as a synthetic revise. */
export async function planGatePrelint(
  args: { ctx: PipelineContext; state: StateJson },
  planPath: string,
): Promise<ReviewResult | null> {
  const corePath = coreJsonPath(args.ctx);
  // The deterministic plan gate is the structural hard-fail; silently skipping it
  // when core.json is missing/unparseable let a plan advance ungated. Fail loud.
  const coreText = await readRequired(corePath, "F1.5 plan gate");
  let core;
  try {
    core = parseTypedCore(coreText, `F1.5 plan gate: core.json at ${corePath}`);
  } catch (err) {
    throw new Error(
      `F1.5 plan gate: core.json at ${corePath} failed to parse/validate: ${err instanceof Error ? err.message : String(err)} (legacy pre-typed-core run? re-run discovery (D0) to regenerate core.json)`,
    );
  }
  // A core exists but F1 wrote no plan → route back to F1 to author it.
  if (!existsSync(planPath)) {
    return {
      status: "revise",
      classification: "plan-gate",
      perItemFindings: [{ label: "plan.json", verdict: "FLAG-missing", one_line: `F1 did not write a plan at ${planPath}` }],
      verbatim_critique: `No plan.json found at ${planPath}. Author the formalization plan — one node entry per core node (assumptions ∪ definitions ∪ statements), plus the env S-block(s).`,
    };
  }
  let planObj: unknown;
  try {
    planObj = parseJsonWithEscapeRepair(await readFile(planPath, "utf8"));
  } catch (err) {
    return {
      status: "revise",
      classification: "plan-gate",
      perItemFindings: [{ label: "plan.json", verdict: "FLAG-parse", one_line: String(err) }],
      verbatim_critique: "plan.json is not valid JSON; re-emit it as a single well-formed object.",
    };
  }
  let knownDecls: Set<string> | undefined;
  try {
    const lib = createRetrieval(args.ctx.repoRoot).library;
    if (lib) knownDecls = new Set(lib.entries.map((e) => e.name));
  } catch {
    knownDecls = undefined;
  }
  if (!knownDecls) {
    console.warn(
      "[causalsmith] library index unavailable (doc/library_index.json missing/unreadable) — the P5 reuse-existence check is SKIPPED this pass; hallucinated reuse decls will surface only at compile. Run `lake build && lake exe library_index`.",
    );
  }
  const gate = runPlanGate(planObj, core, { knownDecls });
  if (gate.ok) return null;
  const shown = gate.violations.slice(0, 40);
  return {
    status: "revise",
    classification: "plan-gate",
    perItemFindings: shown.map((v) => ({ label: v.where, verdict: `FLAG-${v.code}`, one_line: v.message })),
    verbatim_critique:
      "The plan failed the deterministic gate (one-to-one coverage / kind / member / hyp-closure / reuse-existence / module). Fix these mechanical violations in plan.json, keeping every core node mapped exactly once:\n  - " +
      shown.map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  - "),
  };
}

export async function runStage1_5(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  return runReviewBoundary({
    ctx: args.ctx,
    boundary: "stage_1.5_to_1",
    stage: "1.5",
    cap: 3,
    // The F1 plan and its F1.5 review settle into ONE consolidated CKPT 1. Passed: the
    // orchestrator audits before F2 scaffolds. Not passed: it reroutes; F2 stays unreachable.
    checkpoint: {
      name: "CONSOLIDATED CKPT 1",
      passed: "Audit depth, reuse and statement-vs-math fidelity of the F1 plan before --resume into F2.",
    },
    producer: (prior, attempt) => runStage1({ ...args, priorReview: prior, attempt }),
    reviewer: async () => {
      const paths = artifactPaths(args.ctx, args.state);
      // 1. Deterministic gate pre-lint — must pass before the LLM runs.
      const gateReview = await planGatePrelint(args, paths.plan);
      if (gateReview) return gateReview;
      // 2. LLM reuse-soundness review over the gate-clean plan.
      return reviewWithCodex(args);
    },
  });
}
