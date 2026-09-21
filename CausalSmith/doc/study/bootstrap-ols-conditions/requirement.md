# Substrate requirement: bootstrap-ols-conditions

## Goal
Discharge the two bootstrap-side conditions for OLS, so that bootstrap confidence intervals for a
regression coefficient follow from moment assumptions on the data alone, with nothing about
resampling left for the user to prove.

## Provides (API contract)
`Causalean/Stat/Bootstrap/SmoothZEstimator/OLS.lean` currently proves
`BootstrapAsymLinear.olsContrast`, but it still TAKES two hypotheses from the caller:
- `hBootConsistent : BootstrapEstimatorConsistent S (olsSampleEstimator x y) (olsBeta P x y)`
- `hBootSolve : BootstrapSolvesEstimatingEquationInProbability S (olsScore x y) (olsSampleEstimator x y)`
(both defined in `Stat/Bootstrap/SmoothZEstimator/Basic.lean`). OLS is closed-form, so both should be
theorems, not hypotheses. Provide:
- `olsSampleEstimator_bootstrapSolves` — the resampled OLS estimator solves its own normal equations
  with bootstrap probability tending to one, in sampling probability. On a resample whose design
  second moment is invertible the normal equations hold EXACTLY, so the content is that the resample
  Gram matrix is invertible with high probability.
- `olsSampleEstimator_bootstrapConsistent` — the resampled OLS estimator converges to the population
  coefficient in bootstrap probability, in sampling probability.
- `BootstrapAsymLinear.olsContrast_of_moments` — the user-facing corollary: the same conclusion as
  `olsContrast` but with those two hypotheses REMOVED, assuming only what a statistician would state
  (measurable regressor and outcome, integrable raw second moments, positive-definite population
  design second moment `(olsQ P x y).PosDef`, and positive contrast influence variance).
- The corresponding interval corollary, e.g. `olsContrast_percentileCI_coverage_of_moments`, so a user
  gets asymptotic 1−α coverage for a regression contrast from moment conditions alone.

## Statement / milestones
1. Resample Gram convergence: the resample design second moment converges to the population one in
   bootstrap probability, in sampling probability. Route: the promoted vector bootstrap weak law
   `bootstrapMeanVec_sub_dataMean_tendsto_zero_ae` /
   `bootstrapMeanVec_sub_populationMean_tendsto_zero_ae`
   (`Stat/Bootstrap/SmoothFunctionOfMeans/WeakLawVector.lean`) applied to the coordinates of
   `x xᵀ` and `x y`, plus the strong law for the data side.
2. Invertibility with high probability: on the event that the resample Gram is within ε of a
   positive-definite limit it is invertible (continuity of the determinant, or the standard
   perturbation bound on the smallest eigenvalue), so the resample normal equations are solvable and
   the resampled estimator satisfies them exactly — giving `..._bootstrapSolves`.
3. Consistency: combine (1)–(2) with the closed form `β̂* = (Gram*)⁻¹ (Xᵀy)*` and continuity of
   matrix inversion at a positive-definite point to get `..._bootstrapConsistent`.
4. Assemble `olsContrast_of_moments` and its interval corollary by feeding (2)–(3) into the existing
   `BootstrapAsymLinear.olsContrast`.

## Standard reference
Freedman (1981, Ann. Statist. 9:1218), "Bootstrapping regression models"; Hall (1992) §4; the
resample-Gram invertibility argument is the standard one for the pairs bootstrap in regression.

## Intended reuse
Any user bootstrapping a regression coefficient or contrast. It is also the template for removing
the analogous bootstrap-side hypotheses from the feasible-GMM instance later.

## May assume / must derive
- May assume: everything already in `Causalean/Stat/Bootstrap/**` (the interval API, Efron
  resampling and its exact moments, the a.s. bootstrap mean CLT, the bootstrap weak law, conditional
  Chebyshev tightness) and `Stat/LinearModel/OLSAsymptotics/**` (`olsQ`, `olsBeta`, `olsScore`,
  `olsInfluence`, `olsSampleEstimator`, `olsSmoothZRegularity`), plus Mathlib's strong law and
  matrix-inversion continuity.
- Must derive: both bootstrap-side conditions and the two corollaries. Do NOT add a new hypothesis
  that merely renames what is to be proved (e.g. "the resample Gram is invertible" as an assumption),
  and do not weaken `olsContrast`'s conclusion.

## Non-goals
- Wild or residual bootstrap for regression; heteroskedasticity-robust variance ESTIMATION (the
  interval here is percentile/basic, not studentized); the GMM analogue (later, same template);
  fixed-design regression.

## Known building blocks
- `Stat/Bootstrap/SmoothZEstimator/{Basic,OLS}.lean` — the two predicates and `olsContrast`.
- `Stat/Bootstrap/SmoothFunctionOfMeans/{WeakLaw,WeakLawVector,Tightness}.lean`.
- `Stat/Bootstrap/EfronResampling/` — `bootstrapResample`, `finAverage`, the exact moment identities.
- `Stat/LinearModel/OLSAsymptotics/` — the OLS objects above (owned by another session; do NOT edit
  those files, import them).
- Conventions the gate enforces: files ≤600 lines (900 is a hard error), 1–3 `headline_theorems`
  entries per new theorem-bearing file in `doc/library_review/Stat.json`, NL crosslinks on every
  headline docstring, and no library name may reuse this run's slug.
