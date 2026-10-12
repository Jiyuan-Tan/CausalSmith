import type { ReviewResult } from "../judgment.js";
import { appendReview } from "../pipeline_support.js";
import type { PipelineContext, Stage, StageResult, StateJson } from "../types.js";

/**
 * A producer/reviewer loop that settles into ONE checkpoint with two outcomes. Review, and on
 * `revise` let the producer retry, up to `cap` reviews. A pass completes the stage (`advance:
 * true`) with the checkpoint's `passed` message. A `reject`, or work still failing at the cap,
 * leaves the stage uncompleted (`advance: false`) with the `NOT PASSED` message, so a plain
 * resume reviews again and nothing downstream runs; the orchestrator reads the logged verdicts
 * and decides the reroute. This loop rewinds nothing itself.
 */
export async function runReviewBoundary(args: {
  ctx: PipelineContext;
  boundary: string;
  stage: Stage;
  cap: number;
  producer: (prior: ReviewResult, attempt: number) => Promise<StageResult>;
  reviewer: (attempt: number) => Promise<ReviewResult>;
  /** The checkpoint both outcomes halt at: its name, and what the orchestrator does after a pass. */
  checkpoint: { name: string; passed: string };
}): Promise<StageResult> {
  let prior: ReviewResult | null = null;
  for (let attempt = 1; attempt <= args.cap; attempt++) {
    if (prior) {
      const producerResult = await args.producer(prior, attempt);
      if (producerResult.status === "blocked") return producerResult;
    }
    const review = await args.reviewer(attempt);
    await appendReview(args.ctx, args.boundary, attempt, review);
    if (review.status === "pass" || review.status === "accept") {
      return {
        stage: args.stage,
        status: "checkpoint",
        advance: true,
        message: `${args.checkpoint.name} — PASSED. ${args.checkpoint.passed}`,
      };
    }
    prior = review;
    // A reject means another producer retry cannot help.
    if (review.status === "reject") break;
  }
  const last = prior!;
  const trigger = last.status === "reject" ? "rejected" : `still failing after ${args.cap} reviews`;
  const critique = (last.verbatim_critique ?? "").trim().slice(0, 600);
  return {
    stage: args.stage,
    status: "checkpoint",
    advance: false,
    message:
      `${args.checkpoint.name} — NOT PASSED (${trigger}; latest verdict ${last.status}/${last.classification ?? "unclassified"}): ` +
      `${critique || "see the review log"}`,
  };
}

/**
 * Grant the re-entered D phase a fresh loop budget when a LATER phase rewinds into it,
 * returning the spend that was carried in (`null` when there was none) so the caller can
 * report it rather than quietly discarding it.
 *
 * `d0_loop_counters` accumulate across resumes on purpose: within one solve attempt,
 * re-resuming a non-deterministic solver is a re-roll, not a retry. A cross-phase rewind
 * is the other thing. F3 refuting a step in Lean, or D0.5 rejecting the angle, is new
 * information that did not exist when those rounds were spent, and the re-entered D0
 * re-derives against a hard constraint it has never seen. Carrying the old count forward
 * conflates two different attempts: a run that used a typical 6-9 of the 15 solve rounds
 * would re-enter with under half a budget, and one that used 12+ would trip
 * `d0_loop_cap_hit` a round or two in — whose only escape (`--clear-gate d0_loop_cap_hit`)
 * resets everything anyway, so the leak buys no safety and costs the operator a manual
 * round-trip.
 *
 * This is not a cap evasion: the number of rewinds that can reach here is itself bounded
 * (`REDO_MATH_MAX` per refuted node, `NEG1_PIVOT_BUDGET` for angle pivots), so total D
 * work stays bounded. `d0_loop_cap_hit` is deliberately NOT cleared — a gate flag is
 * MAIN's to clear, and a run that has one set cannot have resumed far enough to be here.
 */
export function resetD0LoopCountersForRewind(state: StateJson): string | null {
  const prior = state.flags.d0_loop_counters;
  state.flags.d0_loop_counters = { solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 };
  if (!prior || (prior.solve_rounds === 0 && prior.revise_rounds === 0 && prior.consistency_heals === 0)) {
    return null;
  }
  return `D-phase budget reset for this rewind (carried in: ${prior.solve_rounds} solve, ` +
    `${prior.revise_rounds} revise, ${prior.consistency_heals} consistency-heal round(s))`;
}
