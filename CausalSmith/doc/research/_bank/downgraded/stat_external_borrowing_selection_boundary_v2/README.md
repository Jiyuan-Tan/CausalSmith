---
qid: stat_external_borrowing_selection_boundary
spec: v2
topic: "Sharp selection-relevance modulus and tie-uniform inference for Yang–Li–Wu’s generated influence-ranked all-top-k external-control selector: define the sharp modulus omega*(delta) comparing root-n ATE-coordinate distance with leading MSE-criterion distance; prove exact-tie invariance and its sharp near-zero order or refute it with an explicit legal nested-prefix counterexample; translate the answer into the correct local-gap selected-estimator law and a computable multiplier interval uniformly valid across fixed, vanishing, and exact gaps. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Gaussian rigidity leaves diagonal or antidiagonal exact ties; the legal no-X Uniform model excludes the antidiagonal and gives omega*(delta) proportional to delta. UNRESOLVED BOTTLENECK: uniform prefix-EIF coercivity with generated ranking and covariates. EARLY KILL TEST: exact two/three-prefix covariance plus a sign-changing finite-support counterexample search."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The core proves separate rank-boundary and exact-tie obstructions plus a conditional transfer, but does not prove the promised selected-estimator law, sharp modulus, coverage/length guarantee, or computable tie-uniform interval."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The delivered result is a specialized warning rather than a field-tier inference contribution."
  - "It does not determine the sharp modulus beyond the lower statement omega*(0)>0, establish any law for the selected estimator, or construct a computable uniformly valid interval."
  - "The delivered core supplies only separate negative witnesses and a conditional transfer while expressly leaving the interval, coverage, length, and selected law open."
  - "Pointwise smooth score fitting, scalar score density, and Holder boundary moments do not imply differentiability of the fitted-score sublevel-set integral."
reusable_artifacts:
  - "discovery/core.json — final checked graph containing the generated-prefix rank-boundary obstruction, finite-support exact-tie witness, positive-prefix anchor witness, and conditional quadratic transfer."
  - "discovery/solve_tex/solve_thm_finite_support_tie_witness.tex — finite-support exact-risk-tie construction with nonvanishing ATE-coordinate separation."
  - "discovery/solve_tex/solve_thm_anchor_positive_prefix_tie_witness.tex — anchor-loss positive-prefix tie construction."
  - "discovery/writeup.tex — final derivation note and literature positioning for the obstruction boundary."
seeds_burned: []
proof_attempt_summary: |
  The run repaired and verified two separate anchor-relevant obstructions: a non-Gaussian generated-rank boundary term and an exact leading-risk tie with separated root-n ATE coordinates. A bounded positive-theory attempt isolated the missing fitted-score sublevel-set differentiability primitive; without it, the uniform all-prefix expansion and localization argument could not be derived. The sharp modulus, selected-estimator law, and computable tie-uniform interval therefore remain open, leaving a sound incremental warning below the field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 49032464
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# stat_external_borrowing_selection_boundary / v2 — Downgraded

**Topic.** Sharp selection-relevance modulus and tie-uniform inference for Yang–Li–Wu’s generated influence-ranked all-top-k external-control selector: define the sharp modulus omega*(delta) comparing root-n ATE-coordinate distance with leading MSE-criterion distance; prove exact-tie invariance and its sharp near-zero order or refute it with an explicit legal nested-prefix counterexample; translate the answer into the correct local-gap selected-estimator law and a computable multiplier interval uniformly valid across fixed, vanishing, and exact gaps. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Gaussian rigidity leaves diagonal or antidiagonal exact ties; the legal no-X Uniform model excludes the antidiagonal and gives omega*(delta) proportional to delta. UNRESOLVED BOTTLENECK: uniform prefix-EIF coercivity with generated ranking and covariates. EARLY KILL TEST: exact two/three-prefix covariance plus a sign-changing finite-support counterexample search.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered result is a specialized warning rather than a field-tier inference contribution; the selected law, sharp modulus, and computable uniformly valid interval remain open.

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
