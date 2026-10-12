// `d0_loop_counters` accumulate across resumes on purpose — re-resuming a non-deterministic
// solver within one attempt is a re-roll, not a retry. A CROSS-PHASE rewind is the other
// thing: F3 refuting a step in Lean, or D0.5 rejecting the angle, is information that did
// not exist when those rounds were spent, and the re-entered D0 re-derives against a
// constraint it has never seen. Carrying the old count in conflated the two, so a run that
// spent a typical 6-9 of the 15 solve rounds re-entered with under half a budget and one
// that spent 12+ tripped `d0_loop_cap_hit` a round or two later — whose only escape resets
// every counter anyway. The leak bought no safety and cost a manual round-trip.

import { describe, it, expect } from "vitest";
import { resetD0LoopCountersForRewind } from "../src/shared/review_boundary.js";
import type { StateJson } from "../src/types.js";

function stateWithSpend(spend: { solve_rounds: number; revise_rounds: number; consistency_heals: number }): StateJson {
  return {
    stage_completed: "2",
    lean_subdir: "Stat/STAT_Budget_Research",
    design_decisions: {},
    added_assumptions: [],
    proposed_from: { topic: "t", novelty_target: "field", cluster: "stat", current_angle_index: 0, current_version: 1 },
    flags: { d0_loop_counters: { ...spend } },
  } as unknown as StateJson;
}

describe("resetD0LoopCountersForRewind", () => {
  it("zeroes the D-phase budget and names the spend it carried in", () => {
    const state = stateWithSpend({ solve_rounds: 12, revise_rounds: 2, consistency_heals: 1 });
    const note = resetD0LoopCountersForRewind(state);
    expect(state.flags.d0_loop_counters).toEqual({ solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 });
    expect(note).toMatch(/12 solve/);
    expect(note).toMatch(/2 revise/);
    expect(note).toMatch(/1 consistency-heal/);
  });

  it("reports nothing when there was nothing to carry, so a clean rewind stays quiet", () => {
    expect(resetD0LoopCountersForRewind(stateWithSpend({ solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 }))).toBeNull();
    const fresh = { flags: {} } as unknown as StateJson;
    expect(resetD0LoopCountersForRewind(fresh)).toBeNull();
    expect(fresh.flags.d0_loop_counters).toEqual({ solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 });
  });

  it("does NOT clear `d0_loop_cap_hit` — a gate flag is MAIN's to clear, never a stage's", () => {
    const state = stateWithSpend({ solve_rounds: 15, revise_rounds: 0, consistency_heals: 0 });
    state.flags.d0_loop_cap_hit = "D0 solve cap (15 rounds) exhausted";
    resetD0LoopCountersForRewind(state);
    expect(state.flags.d0_loop_cap_hit).toBe("D0 solve cap (15 rounds) exhausted");
  });
});
