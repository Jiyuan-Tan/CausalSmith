---
qid: panel_mnar_window_blockloo
spec: v1
topic: "Bias-corrected weak-signal inference for a growing-window ATT under serially dependent deterministic-MNAR panel completion. Fix exact known rank and dependence range, impose explicit normalized donor/pre restricted-Gram bounds, and let the treated cohort and consecutive post window grow. For Choi--Yuan's subgroup nuclear-norm estimator and rank-projection debiasing, derive the complete donor-window plus treated-pre minus donor-pre tangent score. Transfer neighborhood-noise-replaced auxiliary fits through the actual masked convex optimizer, derive the serial quadratic drift and a feasible Hessian--lag-covariance correction, and bound the corrected signed aggregate remainder at the oracle window standard-error scale on an explicit joint signal/window envelope polynomially weaker than strong-factor order. Prove an independent-row CLT, consistency of an influence-weighted finite-lag residual covariance estimator, and uniform Wald coverage for the realized cohort-window ATT. Credit Choi--Yuan arXiv:2402.05789 for fully observed leave-neighbor-out weak-factor analysis and Cen--Lam arXiv:2403.13153 for missing-factor residual HAC; do not claim event-time bands, unknown rank, or proportional-window inference at the noise boundary. Consumer: the SEC Tick Size Pilot sustained-liquidity-effect reanalysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact proximal identity Mtilde=SVT_lambda(P_Omega Y+P_missing Mtilde), the complete three-term local differential, and the rank-one projection quadratic map. For constant-factor MA(1) panels it derived a serial quadratic coefficient converging to -1/psi and an estimable Hessian--lag-covariance correction; a separate weak-signal block-mean case has exact remainder O_P(1/(n psi)) and oracle variance 36/n^2-64/n^3 versus iid 20/n^2. Hidden-block nonidentification, rank overprojection, window-growth boundaries, covariance degeneracy, residual contamination, and nearby literature were checked. UNRESOLVED BOTTLENECK: Prove uniform native-optimizer second-order transfer and plug-in stability, including centered quadratic aggregation and higher-order/regularization errors o(s), from primitive conditions. EARLY KILL TEST: At rank one with Gaussian MA(1), constant and positive alternating factors, H proportional to n, and psi=n^(4/5), reproduce the three-term derivative and exact quadratic coefficient, apply the fitted correction, and certify that n times the corrected native-optimizer remainder vanishes; a surviving interior term or strong-factor requirement forces pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_mnar_window_blockloo.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "the headline native-optimizer inference theorem is not proved"
  - "the neighborhood-coupling estimate (6), centered-aggregate equations (3)/(8), and fitted curvature/weight equations (5)/(9) lack checkable derivations"
  - "The calibration inherits the unproved transfer theorem and there is no completed reproducible application."
  - "On the results actually supported, this is a collection of useful setup lemmas rather than a field-level inference contribution"
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/proto_core.json
  - reviews/review_general.json
  - reviews/review_math.json
  - reviews/review_rubric.json
seeds_burned: []
proof_attempt_summary: |
  The discovery run derived the proximal fixed-point identity, the three-block first differential,
  auxiliary-fit measurability, and score-diffuseness, and it verified the two cited source theorems.
  The native masked-optimizer second-order transfer, centered higher-order aggregation, fitted
  Hessian/weight stability, and the resulting uniform Wald expansion were not reproduced at a
  checkable level, leaving only an incremental setup package below the field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 36001110
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 36001110
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# panel_mnar_window_blockloo / v1 — Downgraded

**Topic.** Bias-corrected weak-signal inference for a growing-window ATT under serially dependent deterministic-MNAR panel completion. Fix exact known rank and dependence range, impose explicit normalized donor/pre restricted-Gram bounds, and let the treated cohort and consecutive post window grow. For Choi--Yuan's subgroup nuclear-norm estimator and rank-projection debiasing, derive the complete donor-window plus treated-pre minus donor-pre tangent score. Transfer neighborhood-noise-replaced auxiliary fits through the actual masked convex optimizer, derive the serial quadratic drift and a feasible Hessian--lag-covariance correction, and bound the corrected signed aggregate remainder at the oracle window standard-error scale on an explicit joint signal/window envelope polynomially weaker than strong-factor order. Prove an independent-row CLT, consistency of an influence-weighted finite-lag residual covariance estimator, and uniform Wald coverage for the realized cohort-window ATT. Credit Choi--Yuan arXiv:2402.05789 for fully observed leave-neighbor-out weak-factor analysis and Cen--Lam arXiv:2403.13153 for missing-factor residual HAC; do not claim event-time bands, unknown rank, or proportional-window inference at the noise boundary. Consumer: the SEC Tick Size Pilot sustained-liquidity-effect reanalysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact proximal identity Mtilde=SVT_lambda(P_Omega Y+P_missing Mtilde), the complete three-term local differential, and the rank-one projection quadratic map. For constant-factor MA(1) panels it derived a serial quadratic coefficient converging to -1/psi and an estimable Hessian--lag-covariance correction; a separate weak-signal block-mean case has exact remainder O_P(1/(n psi)) and oracle variance 36/n^2-64/n^3 versus iid 20/n^2. Hidden-block nonidentification, rank overprojection, window-growth boundaries, covariance degeneracy, residual contamination, and nearby literature were checked. UNRESOLVED BOTTLENECK: Prove uniform native-optimizer second-order transfer and plug-in stability, including centered quadratic aggregation and higher-order/regularization errors o(s), from primitive conditions. EARLY KILL TEST: At rank one with Gaussian MA(1), constant and positive alternating factors, H proportional to n, and psi=n^(4/5), reproduce the three-term derivative and exact quadratic coefficient, apply the fitted correction, and certify that n times the corrected native-optimizer remainder vanishes; a surviving interior term or strong-factor requirement forces pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_mnar_window_blockloo.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: incremental, ceiling 3.2 below the field floor 7.4; the headline native-optimizer transfer and fitted-stability derivations remain unreproduced and the framing is not salvageable in scope.

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
