---
qid: stat_incremental_hardening_limit
spec: v1
topic: "Hardening frontier for binary incremental propensity interventions under weak overlap. Observe iid bounded-outcome data with binary treatment, consistency and exchangeability. On an explicit second-order regularly varying lower-propensity class with tail exponent strictly between zero and one, convergent treated boundary marks, and uniformly positive treated-residual variance, let the odds multiplier delta_n diverge and let a_n be the equivalent power normalizer or generalized inverse satisfying n E[e 1{e<=1/a_n}] asymptotically equal to one. For the incremental mean psi_delta, derive separated Gaussian, compensated marked infinitely-divisible, and residual-stable laws as h_n=delta_n/a_n tends to zero, a positive finite value, or infinity. The critical jump map must retain both the treated residual and propensity-path treatment contrast; prove the latter vanishes only at the stable endpoint. Construct cross-fitted local-polynomial or series nuisance fits, empirical tail/mark calibration with certified one-dimensional Levy inversion, regime-valid confidence procedures, and the pointwise ambient triangular-experiment efficiency bound in the Gaussian branch. Consumer: npcausal::ipsi and the Naimi et al. nuMoM2b vegetable-preeclampsia incremental-effect analysis, whose bounded-delta multiplier bands do not cover hardening odds shifts. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh derivations give the compensated critical jump map, an O(h_n^{-kappa}) hardening reduction to residual IPW, exact nuisance-bias and fitted-score envelopes, stable-tail nondegeneracy from residual separation, and a concrete C2 covariate class whose weighted local-linear rates support score replacement in all three regimes. Bernoulli/Beta quadrature verifies nonzero critical variance and skewness; fitted diagnostics at h=1/4,1,4 shrink on the predicted scale. Checks exclude deterministic-residual degeneracy, fixed-delta critical resampling, and recent fixed-tilt, continuous-exposure, and hard-trimming collisions. UNRESOLVED BOTTLENECK: Prove uniform plug-in quantile coverage by combining cross-fitted score replacement with empirical tail/mark and logarithmically sensitive normalizer rates plus certified inversion error over each separated regime. EARLY KILL TEST: On the explicit C2 class, prove the weighted local-fit information bound, fitted-score replacement, and empirical critical quantile consistency for h in {1/4,1,4} without oracle marks or an assumed final remainder; failure of any one forces a pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_incremental_hardening_limit.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "the delivered results give separated asymptotic branches and branchwise inference but no single data-driven procedure through either transition"
  - "feasible nuisance replacement/calibration is restricted to the one-dimensional smooth-boundary Bernoulli subclass while the broader marked regular-variation class is oracle-only"
  - "the ambient efficiency result is not class-intrinsic/minimax"
  - "the package lacks an implemented application or numerical calibration study"
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_tex/solve_prop_fixed_multiplier_reduction.tex
  - discovery/solve_tex/solve_thm_ambient_gaussian_efficiency.tex
  - reviews/review_math.json
seeds_burned: []
proof_attempt_summary: |
  The run derived and internally validated a three-regime hardening theory, including the
  marked critical law, residual-stable endpoint, separated-regime feasible calibration,
  fixed-multiplier reduction, and ambient Gaussian efficiency argument; the math referee
  passed and all eight source checks were independently attested. It missed field tier
  because feasible inference remains confined to a one-dimensional C² Bernoulli subclass
  and does not adapt through either transition. Reaching field tier would require a new
  transition-adaptive procedure, broader feasible marked-tail theory, or a class-intrinsic
  minimax efficiency result rather than a bounded repair of this note.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 22949084
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 22949084
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# stat_incremental_hardening_limit / v1 — Downgraded

**Topic.** Hardening frontier for binary incremental propensity interventions under weak overlap. Observe iid bounded-outcome data with binary treatment, consistency and exchangeability. On an explicit second-order regularly varying lower-propensity class with tail exponent strictly between zero and one, convergent treated boundary marks, and uniformly positive treated-residual variance, let the odds multiplier delta_n diverge and let a_n be the equivalent power normalizer or generalized inverse satisfying n E[e 1{e<=1/a_n}] asymptotically equal to one. For the incremental mean psi_delta, derive separated Gaussian, compensated marked infinitely-divisible, and residual-stable laws as h_n=delta_n/a_n tends to zero, a positive finite value, or infinity. The critical jump map must retain both the treated residual and propensity-path treatment contrast; prove the latter vanishes only at the stable endpoint. Construct cross-fitted local-polynomial or series nuisance fits, empirical tail/mark calibration with certified one-dimensional Levy inversion, regime-valid confidence procedures, and the pointwise ambient triangular-experiment efficiency bound in the Gaussian branch. Consumer: npcausal::ipsi and the Naimi et al. nuMoM2b vegetable-preeclampsia incremental-effect analysis, whose bounded-delta multiplier bands do not cover hardening odds shifts. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh derivations give the compensated critical jump map, an O(h_n^{-kappa}) hardening reduction to residual IPW, exact nuisance-bias and fitted-score envelopes, stable-tail nondegeneracy from residual separation, and a concrete C2 covariate class whose weighted local-linear rates support score replacement in all three regimes. Bernoulli/Beta quadrature verifies nonzero critical variance and skewness; fitted diagnostics at h=1/4,1,4 shrink on the predicted scale. Checks exclude deterministic-residual degeneracy, fixed-delta critical resampling, and recent fixed-tilt, continuous-exposure, and hard-trimming collisions. UNRESOLVED BOTTLENECK: Prove uniform plug-in quantile coverage by combining cross-fitted score replacement with empirical tail/mark and logarithmically sensitive normalizer rates plus certified inversion error over each separated regime. EARLY KILL TEST: On the explicit C2 class, prove the weighted local-fit information bound, fitted-score replacement, and empirical critical quantile consistency for h in {1/4,1,4} without oracle marks or an assumed final remainder; failure of any one forces a pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_incremental_hardening_limit.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Cold-tier verdict: tier=subfield; paper_score_ceiling=7.1 < 7.4; meets_floor=false; salvageable=false; no bounded field-lifting correction was overlooked.

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
