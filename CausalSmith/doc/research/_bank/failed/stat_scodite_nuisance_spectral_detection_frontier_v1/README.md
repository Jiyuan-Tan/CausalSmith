---
qid: stat_scodite_nuisance_spectral_detection_frontier
spec: v1
topic: "All-tests nuisance-limited spectral detection frontier for conditional distributional treatment effects. In the iid binary-treatment unconfounded model with fixed overlap, bounded characteristic kernels, uniform continuous covariates, and explicit Holder classes for the propensity and conditional outcome laws, define the SCoDiTE RKHS norm separation problem and its answer-open minimax boundary over covariance eigen-decay and source classes. Derive the regime-wise equality or strict gap from the known-propensity experiment using paired fuzzy likelihood mixtures and procedures that include higher-order correction; characterize by an iff spectral criterion when the named SKCD-MMD or regularized SKCD-Wald test is optimal; and construct a jointly calibrated adaptive regularization-grid test. Consumer: the 401(k) conditional wealth-distribution analysis, where the theorem replaces heuristic whitening with a size-valid choice and identifies regimes in which whitening loses to MMD. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A bounded unbiased Hilbert-feature oracle test and matching root-n lower bound were derived. For source exponent at most one-half and total nuisance smoothness below half the dimension, legal continuous-covariate Bernoulli fuzzy mixtures satisfy the exact null, have identical one-record mixtures, and yield a slower all-tests separation lower bound; finite enumeration checked positivity, normalization, and cancellation. Checks also exposed that centered characteristic kernels may not make the RKHS null identical to conditional homogeneity, so the target interpretation must remain kernel-specific. UNRESOLVED BOTTLENECK: Match the SCoDiTE boundary under arbitrary bounded covariate density, determining whether the known-design low-smoothness radius is attainable or a larger occupancy obstruction governs the exact null. EARLY KILL TEST: In one dimension with a polynomial Fourier kernel and rough nuisance smoothness 0.2 per nuisance, audit an upper procedure at the predicted resolution and verify that rough-density null mixtures remain inside the exact SCoDiTE null; failure must pivot the design regime. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_scodite_nuisance_spectral_detection_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The arbitrary-density minimax upper/lower match, spectral optimality iff, and adaptive regularization-grid test remain open; recovering them requires solving the original flagship problem."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised all-tests rough-design frontier is still explicitly to-prove; the current core instead delivers only the high-smoothness root-n branch plus a uniform-design lower bound."
  - "It does not deliver the advertised rough arbitrary-density frontier: there is no matching upper bound, and the proposed occupancy radius remains conjectural."
  - "The spectral optimality iff and adaptive regularization-grid test are only construction handles and open questions."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_tex/solve_thm_fourier_null_iff.tex
  - discovery/solve_tex/solve_thm_high_smoothness_density_robustness.tex
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery repaired the fuzzy-mixture cell algebra, proved its legality/affinity spine, established the Fourier operator-null characterization, and derived a density-robust high-smoothness root-n construction plus a uniform-design rough lower bound. The attempt collapsed at the promised field-level centerpiece: no matched arbitrary bounded-density minimax frontier was proved, leaving the spectral iff and adaptive-grid test dependent open questions. A common-anchor U-statistic indexing error also remains, but fixing it would not restore the missing result or the field tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 27280618
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 27280618
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# stat_scodite_nuisance_spectral_detection_frontier / v1 — Failed

**Topic.** All-tests nuisance-limited spectral detection frontier for conditional distributional treatment effects. In the iid binary-treatment unconfounded model with fixed overlap, bounded characteristic kernels, uniform continuous covariates, and explicit Holder classes for the propensity and conditional outcome laws, define the SCoDiTE RKHS norm separation problem and its answer-open minimax boundary over covariance eigen-decay and source classes. Derive the regime-wise equality or strict gap from the known-propensity experiment using paired fuzzy likelihood mixtures and procedures that include higher-order correction; characterize by an iff spectral criterion when the named SKCD-MMD or regularized SKCD-Wald test is optimal; and construct a jointly calibrated adaptive regularization-grid test. Consumer: the 401(k) conditional wealth-distribution analysis, where the theorem replaces heuristic whitening with a size-valid choice and identifies regimes in which whitening loses to MMD. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A bounded unbiased Hilbert-feature oracle test and matching root-n lower bound were derived. For source exponent at most one-half and total nuisance smoothness below half the dimension, legal continuous-covariate Bernoulli fuzzy mixtures satisfy the exact null, have identical one-record mixtures, and yield a slower all-tests separation lower bound; finite enumeration checked positivity, normalization, and cancellation. Checks also exposed that centered characteristic kernels may not make the RKHS null identical to conditional homogeneity, so the target interpretation must remain kernel-specific. UNRESOLVED BOTTLENECK: Match the SCoDiTE boundary under arbitrary bounded covariate density, determining whether the known-design low-smoothness radius is attainable or a larger occupancy obstruction governs the exact null. EARLY KILL TEST: In one dimension with a polynomial Fourier kernel and rough nuisance smoothness 0.2 per nuisance, audit an upper procedure at the predicted resolution and verify that rough-density null mixtures remain inside the exact SCoDiTE null; failure must pivot the design regime. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_scodite_nuisance_spectral_detection_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted: the promised all-tests rough-design frontier remains to-prove; delivered branch is only high-smoothness plus uniform-design lower bound

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
