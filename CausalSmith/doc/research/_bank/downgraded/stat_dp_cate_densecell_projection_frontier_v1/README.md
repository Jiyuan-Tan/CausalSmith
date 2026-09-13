---
qid: stat_dp_cate_densecell_projection_frontier
spec: v1
topic: "Revive stat_dp_cate_fiber_tmechanism_frontier with the occupancy-weighted full-class sparse-to-dense pure-DP pointwise-CATE frontier and the presolve capsule embedded in this queued entry."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The full-class estimator and matching upper frontier remain conditional on an unconstructed full-fiber sensitivity-one score family and a nuisance-dimension-free weighted-shell certificate."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The positioned unconditional converse is a real, usable lower-bound contribution, but the promised exact-uniform sparse-to-dense frontier has been replaced by an unconstructed score family and a conditional reduction, so no unconditional attaining estimator or upper frontier is delivered."
  - "The framing explicitly discloses this limitation rather than falsely claiming a match, but the missing estimator and nuisance-dimension control keep the contribution below a field-level contribution."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_full_class_lower_frontier.json
  - discovery/solve_tex/solve_thm_full_class_lower_frontier.tex
  - discovery/solve_lem_causal_identification.json
  - discovery/solve_tex/solve_lem_causal_identification.tex
seeds_burned: []
proof_attempt_summary: |
  The run proved an unconditional exact-uniform pure-DP CATE converse, including the sparse two-fiber distance certificate and its transfer to a Kennedy-Theorem-1 superclass slice; the math referee passed it without findings. The matching upper frontier remained conditional because no explicit full-fiber sensitivity-one score family or nuisance-dimension-free weighted-shell certificate was constructed. A future retry should reuse the audited converse and focus exclusively on that missing achievability object rather than re-deriving the lower bound.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 25721900
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 25721900
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_dp_cate_densecell_projection_frontier / v1 — Downgraded

**Topic.** Revive stat_dp_cate_fiber_tmechanism_frontier with the occupancy-weighted full-class sparse-to-dense pure-DP pointwise-CATE frontier and the presolve capsule embedded in this queued entry.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The positioned unconditional converse is a real, usable lower-bound contribution, but the promised exact-uniform sparse-to-dense frontier has been replaced by an unconstructed score family and a conditional reduction, so no unconditional attaining estimator or upper frontier is delivered.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
