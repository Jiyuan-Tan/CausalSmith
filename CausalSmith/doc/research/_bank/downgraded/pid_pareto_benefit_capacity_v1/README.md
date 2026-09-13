---
qid: pid_pareto_benefit_capacity
spec: v1
topic: "Sharp identification of individual-weighted strict Pareto benefit under multivariate response-pattern selection in cluster-randomized trials via a positive-stratum joint completion-and-cross-world LP, with compatibility onset, attained dual-certified bounds, nonrectangularity and majority-threshold results."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Delivered sharp observed-data identification LP but not the proposed min-cut algorithms, cluster-AIPW/tied-cut inference, finite-cluster validation, or PPACT analysis."
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "tier=incremental; meets_floor=false; salvageable=false; paper_score_ceiling=5.5; floor=field"
  - "The delivered work is a mathematically sound identification note, not the package still advertised in state.proposed_from.topic."
  - "It expressly proves no full missing-state min-cut representation, coupling-producing cut algorithms, cluster-AIPW estimator, tied-cut simultaneous inference, 106-cluster validation, or PPACT analysis."
reusable_artifacts:
  - "discovery/core.json — six fully discharged statements for the joint completion-and-cross-world LP"
  - "discovery/writeup.tex — sharpness embeddings, dual certificates, compatibility onset, and honest-scope caveats"
  - "discovery/solve_prop_nonrectangular_witness.json — finite nonrectangularity witness"
  - "discovery/proto_core_angle0_rejected.json — fixed-marginal transport angle and collision history"
  - "reviews/angle1_v4.json — accepted proposal-level novelty and verified comparator receipts"
seeds_burned:
  - index: 0
    one_liner: "seed:attained-pareto-capacity"
    reason: "The fixed-marginal Pareto-capacity angle was subsumed by existing transport results; the missing-state pivot yielded sound sharp identification but no inference or empirical package and remained incremental."
  - index: 5
    one_liner: "seed:missing-state-pareto-bounds"
    reason: "The fixed-marginal Pareto-capacity angle was subsumed by existing transport results; the missing-state pivot yielded sound sharp identification but no inference or empirical package and remained incremental."
proof_attempt_summary: |
  The initial fixed-marginal Pareto-capacity angle collided with classical and accepted-bank transport results, so discovery pivoted to overlapping response-pattern completion jointly with same-person Pareto coupling. That pivot produced a sound, fully discharged six-statement identification paper with attained LP bounds, dual certificates, a nonrectangularity witness, a majority threshold, and a joint-payoff corollary. It remained below the field floor because min-cut computation, cluster-level tied-cut inference, finite-cluster validation, and the PPACT application would require a separate statistics and empirical research program.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 47311849
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 47311849
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# pid_pareto_benefit_capacity / v1 — Downgraded

**Topic.** Sharp identification of individual-weighted strict Pareto benefit under multivariate response-pattern selection in cluster-randomized trials via a positive-stratum joint completion-and-cross-world LP, with compatibility onset, attained dual-certified bounds, nonrectangularity and majority-threshold results.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 BELOW NOVELTY FLOOR: tier=incremental < floor=field and not salvageable in scope; math review passed.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The D0.5 math review passed. A future re-raise should start from the tied-cut
whole-set inference seed and explicitly position the result against
`pid_slate_benefit_partialtransport_v1`; comparator prose alone is not enough
to lift the current identification-only package to field tier.
