---
qid: stat_sparse_r3d_resolution_frontier
spec: v1
topic: "Two-resolution minimax and honest-band frontier for distribution-valued regression discontinuity under sparse within-unit sampling. Observe n independent aggregate units with a sharp cutoff treatment, a latent potential outcome distribution on [0,1], and m conditionally iid subunit draws. On the fixed beta-smooth latent-density, gamma-smooth scalar-pushforward, and s-smooth cutoff-regression class in the strongest-form draft, determine matching minimax sup-norm risk and all-honest simultaneous-band width for the local average quantile treatment-effect curve over every joint n,m regime: a positive bounded-m floor, the sharp intermediate frontier, and the smallest m_crit recovering dense-oracle R3D. Construct a cross-y-compatible estimator and bias-aware studentized simultaneous band. Consumer: R3D::r3d and the CPS state-income application. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The conditional Beta/order-statistic operator and a full/half-sample jackknife give bias O(m^{-r}), r=min((beta+1)/2,2), and the upper rate n^{-s/(2s+1)}+m^{-r}. Smooth moment-matched latent laws give exact complete-tuple equivalence for fixed m. A hidden-label spectral divergence calculation plus a beta=3/2 quantile cusp yields a candidate polynomial m^{-4-2gamma} floor; normalization, support-edge, signed-weight, covariance, and direct-collision checks found no fatal defect. UNRESOLVED BOTTLENECK: Prove a sharp complete-observation modulus matching an attainable compatible-estimator upper bound throughout the intermediate regimes. EARLY KILL TEST: Certify the gamma-normalized beta=3/2 cusp and complete-tuple divergence inside the fixed class constants; stop or pivot if no bounded replacement survives. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_sparse_r3d_resolution_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "iid R3D draws lack the stable marked decoder; no transfer theorem or real deployed marked-channel setting is named."
  - "Known, uniformly nonvanishing signals for conditionally independent binary probes of every coordinate of an infinite latent sequence are load-bearing, while the asserted questionnaire/instrument examples do not establish that this calibration model is realistic."
  - "A verbal centered ‘local-polynomial influence process’ does not define residuals, weights, variance estimation, or endpoints, while H requires exact all-n honest coverage."
reusable_artifacts:
  - discovery/proto_core.json  # bounded-m tuple nonidentification witness and half-sample order-statistic correction ideas only; do not reuse the marked-channel frontier
  - reviews/angle0_v3.json  # verified comparator locators for Van Dijcke, Peng et al., Berger–Hermann–Holzmann, and Cai–Hu
  - reviews/angle0_v4.json  # terminal kernel-substitution audit and omitted Zhou–Müller comparator
seeds_burned: []
proof_attempt_summary: |
  Four proposal revisions tried to turn the presolved sparse-within-unit R3D rate into a field-tier
  all-regime minimax and honest-band frontier. The final root change replaced the iid tuple-mixture
  experiment by calibrated marked binary probes and assumed the desired coefficient-tail rate, while
  explicitly leaving the true iid R3D exponent open; the validity gate therefore classified the result
  as kernel substitution. A future attempt would need a genuine complete-tuple observation modulus and
  matching estimator/band directly in the iid R3D experiment, not the marked-channel surrogate.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26598361
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26598361
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# stat_sparse_r3d_resolution_frontier / v1 — Failed

**Topic.** Two-resolution minimax and honest-band frontier for distribution-valued regression discontinuity under sparse within-unit sampling. Observe n independent aggregate units with a sharp cutoff treatment, a latent potential outcome distribution on [0,1], and m conditionally iid subunit draws. On the fixed beta-smooth latent-density, gamma-smooth scalar-pushforward, and s-smooth cutoff-regression class in the strongest-form draft, determine matching minimax sup-norm risk and all-honest simultaneous-band width for the local average quantile treatment-effect curve over every joint n,m regime: a positive bounded-m floor, the sharp intermediate frontier, and the smallest m_crit recovering dense-oracle R3D. Construct a cross-y-compatible estimator and bias-aware studentized simultaneous band. Consumer: R3D::r3d and the CPS state-income application. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The conditional Beta/order-statistic operator and a full/half-sample jackknife give bias O(m^{-r}), r=min((beta+1)/2,2), and the upper rate n^{-s/(2s+1)}+m^{-r}. Smooth moment-matched latent laws give exact complete-tuple equivalence for fixed m. A hidden-label spectral divergence calculation plus a beta=3/2 quantile cusp yields a candidate polynomial m^{-4-2gamma} floor; normalization, support-edge, signed-weight, covariance, and direct-collision checks found no fatal defect. UNRESOLVED BOTTLENECK: Prove a sharp complete-observation modulus matching an attainable compatible-estimator upper bound throughout the intermediate regimes. EARLY KILL TEST: Certify the gamma-normalized beta=3/2 cusp and complete-tuple divergence inside the fixed class constants; stop or pivot if no bounded replacement survives. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_sparse_r3d_resolution_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** iid R3D draws lack the stable marked decoder; no transfer theorem or real deployed marked-channel setting is named.

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
