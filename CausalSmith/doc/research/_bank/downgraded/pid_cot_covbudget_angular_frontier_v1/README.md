---
qid: pid_cot_covbudget_angular_frontier
spec: v1
topic: "Characterize the optimal dimension-free approximation frontier for selecting at most k pretreatment covariates to tighten the Gaussian conditional-optimal-transport sharp lower bound on mean squared individual treatment effects. In randomized binary-treatment data with unequal Gaussian arm scales, 2k-sparse covariate eigenvalues in [m,M], conditional residual floor σ_min², and outcome-variance ceiling V, derive the angular residual-information identity; prove γ_k≥(m/M)σ_min²/V and the induced greedy guarantee; construct legal unequal-scale families approaching k/[1+(k−1)(M/m)(V/σ_min²)] to establish both-factor sharpness and dimension-free optimality; and give independent-sample inference for the selected endpoint, with a conservative whole-class projection interval at equality. Credit generic greedy and post-selection inference as prior machinery rather than novelty. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The Gaussian endpoint increment is exactly a squared chordal distance between upper-hemisphere lifts of residualized arm-score vectors. A sparse Schur-complement frame bound and a hemisphere Lipschitz inequality give γ_k≥(m/M)σ_min²/V, stronger than the gated constant. A legal p=2k unequal-scale family has ratio tending to k/[1+(k−1)(M/m)(V/σ_min²)], proving both condition factors necessary and the dimension-free certificate optimal as k grows. The supplied p=4 witness, 43,280 randomized positive-denominator checks, derivative finite differences, and high-precision sharpness instances passed. Ji–Lei–Spector already cover generic selection-valid inference, so novelty is restricted to the sharp budget frontier; equality-boundary Wald failure is handled by a conservative moment-projection interval. UNRESOLVED BOTTLENECK: Determine whether the sharper fixed-k lower bound k/[1+(k−1)KR] is universal; this optional refinement is not needed for the proved dimension-free result. EARLY KILL TEST: Reconstruct the p=4,k=2 family at (K,R)=(1,100),(10,2),(10,100), verify all subset residual floors and the limit 2/(KR+1), then independently check the frame and hemisphere inequalities. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_cot_covbudget_angular_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The exact fixed-budget frontier is the flagship theorem, but its node-level justification compares only with earlier internal inequalities; add a precise comparison to the closest published weak-submodularity/conditional-transport result class stating why none gives this two-arm Gaussian finite-budget equality frontier."
  - "van der Vaart is cited as external substrate but has no relevance sentence in the related-work discussion; identify it there as the standard triangular-array CLT used only for the non-novel inference specialization."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_dimension_free_frontier.json
  - discovery/solve_prop_class_inclusion.json
  - discovery/solve_tex/solve_thm_dimension_free_frontier.tex
  - discovery/solve_tex/solve_prop_class_inclusion.tex
seeds_burned: []
proof_attempt_summary: |
  The run proved the piecewise exact fixed-budget submodularity-ratio frontier, its induced greedy certificate, the matching unequal-scale Gaussian infimal construction, and both k=1 and R=1 elbows; the final math review passed after lawful attestation of van der Vaart's Lindeberg--Feller theorem. The field-tier claim collapsed because this is not a sharp worst-case greedy-value ratio: the witness has vanishing endpoint contrast, the empirical guarantee is conditional on an unquantified uniform-error event, and the inference results provide coverage without interval-length or whole-class informativeness guarantees. A future re-raise needs a genuinely stronger result such as a nonvanishing-signal greedy-value converse, justified broader-class transfer, or integrated informative finite-sample selection and inference, while preserving the two unrepaired positioning findings above.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31160519
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31160519
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# pid_cot_covbudget_angular_frontier / v1 — Downgraded

**Topic.** Characterize the optimal dimension-free approximation frontier for selecting at most k pretreatment covariates to tighten the Gaussian conditional-optimal-transport sharp lower bound on mean squared individual treatment effects. In randomized binary-treatment data with unequal Gaussian arm scales, 2k-sparse covariate eigenvalues in [m,M], conditional residual floor σ_min², and outcome-variance ceiling V, derive the angular residual-information identity; prove γ_k≥(m/M)σ_min²/V and the induced greedy guarantee; construct legal unequal-scale families approaching k/[1+(k−1)(M/m)(V/σ_min²)] to establish both-factor sharpness and dimension-free optimality; and give independent-sample inference for the selected endpoint, with a conservative whole-class projection interval at equality. Credit generic greedy and post-selection inference as prior machinery rather than novelty. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The Gaussian endpoint increment is exactly a squared chordal distance between upper-hemisphere lifts of residualized arm-score vectors. A sparse Schur-complement frame bound and a hemisphere Lipschitz inequality give γ_k≥(m/M)σ_min²/V, stronger than the gated constant. A legal p=2k unequal-scale family has ratio tending to k/[1+(k−1)(M/m)(V/σ_min²)], proving both condition factors necessary and the dimension-free certificate optimal as k grows. The supplied p=4 witness, 43,280 randomized positive-denominator checks, derivative finite differences, and high-precision sharpness instances passed. Ji–Lei–Spector already cover generic selection-valid inference, so novelty is restricted to the sharp budget frontier; equality-boundary Wald failure is handled by a conservative moment-projection interval. UNRESOLVED BOTTLENECK: Determine whether the sharper fixed-k lower bound k/[1+(k−1)KR] is universal; this optional refinement is not needed for the proved dimension-free result. EARLY KILL TEST: Reconstruct the p=4,k=2 family at (K,R)=(1,100),(10,2),(10,100), verify all subset residual floors and the limit 2/(KR+1), then independently check the frame and hemisphere inequalities. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_cot_covbudget_angular_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The exact Gaussian fixed-budget submodularity-ratio frontier is mathematically sound and subfield-worthy, but its 6.8 ceiling is below the 7.2 field floor; bounded positioning and related-work repairs cannot supply the stronger greedy-value, fixed-signal, integrated inference, or broader-class result needed to clear field.

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
