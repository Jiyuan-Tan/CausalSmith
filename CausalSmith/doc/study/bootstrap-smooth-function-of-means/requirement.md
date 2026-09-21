# Substrate requirement: bootstrap-smooth-function-of-means

## Goal
Make the bootstrap directly usable for the most common estimator class — a smooth function of
sample means (ratios, correlations, regression slopes written as moment ratios, variance ratios) —
by proving its bootstrap linearization, plus the bootstrap law of large numbers that every
estimator-class argument needs.

## Provides (API contract)
Setting as in study `bootstrap-percentile-intervals`: `S : IIDSample Ω X μ P`, `S.sampleVector`,
bootstrap resampling law `P*_x`, the structure `BootstrapAsymLinear`.
- Bootstrap weak law (almost surely in the data): for measurable `g : X → ℝ` with
  `∫ |g| dP < ∞`, for μ-a.e. ω and every ε > 0,
  `P*_x(|mean_{x*} g − mean_x g| > ε) → 0` with `x = S.sampleVector n ω`; hence also
  `P*_x(|mean_{x*} g − ∫ g dP| > ε) → 0` a.s.
- Bootstrap √n-tightness: for `g` with `∫ g² dP < ∞`, for μ-a.e. ω,
  `P*_x(√n |mean_{x*} g − mean_x g| > M)` is bounded by `(mean_x g² − (mean_x g)²)/M²` for every
  M > 0 and every SAMPLE SIZE n ≠ 0 (Chebyshev under `P*_x`), so it is `O_{P*}(1)` a.s.
  Corrected 2026-09-17 (reviewer was right): the earlier wording said "every n", but at `n = 0`
  there is no empirical distribution to resample from, so `n ≠ 0` is the honest hypothesis — the
  same convention the promoted `EfronResampling` moment identities use. Do NOT manufacture a
  junk-value extension to cover `n = 0`.
- Vector version of both for `g : X → EuclideanSpace ℝ (Fin d)` (or any finite-dimensional normed
  space), componentwise.
- Constructor `BootstrapAsymLinear.smoothFunctionOfMeans`: for
  `g : X → EuclideanSpace ℝ (Fin d)` [measurable] with `∫ ‖g‖² dP < ∞`, mean `m = ∫ g dP`, and
  `h : EuclideanSpace ℝ (Fin d) → ℝ` [measurable] and differentiable at `m` with derivative `Dh`
  such that `0 < ∫ (Dh (g − m))² dP`, the estimator `est n x = h (mean_x g)` satisfies
  `BootstrapAsymLinear S est (h m) (fun x => Dh (g x − m))`.
  Measurability of `g` and `h` is an explicit hypothesis, authorized 2026-09-17: the bundle's `meas`
  field needs every `est n` measurable, and pointwise differentiability at one point gives only
  continuity there, not measurability of `h`. Both are standard regularity conditions (every
  continuous or Borel `h` qualifies) and neither weakens the conclusion. The influence function
  `x ↦ Dh (g x − m)` is then measurable automatically, `Dh` being a continuous linear map.
- A one-line user corollary, e.g. `percentileCI_coverage_smoothFunctionOfMeans`, and the ratio
  estimator `mean Y / mean W` (with `E W ≠ 0`) as a worked instance.

## Statement / milestones
1. Bootstrap WLLN a.s. for integrable `g`: truncate at a level growing with n or use the exact
   bootstrap mean/variance of truncated parts plus the strong law for the data; square-integrable
   case is Chebyshev with the exact bootstrap variance and the strong law for `mean_x g²`.
2. Bootstrap tightness (Chebyshev with the exact bootstrap variance from study
   `efron-bootstrap-resampling`).
3. Sampling linearization of `h(mean g)`: differentiability at `m` + strong law + CLT tightness.
4. Bootstrap linearization: `h(mean_{x*} g) − h(mean_x g) − Dh(mean_{x*} g − mean_x g)` is
   `o(‖mean_{x*} g − m‖ + ‖mean_x g − m‖)` by differentiability at `m`; both norms are
   `O(n^{-1/2})` (bootstrap tightness, data CLT) and the bootstrap mean is near `m` (bootstrap WLLN).
5. Constructor, corollary, ratio instance.

## Standard reference
Bickel & Freedman (1981), Section 3; Hall, *The Bootstrap and Edgeworth Expansion* (1992),
Section 2.4; van der Vaart, *Asymptotic Statistics*, Theorem 23.5 (delta method for the bootstrap).

## Intended reuse
Any user whose estimator is a smooth function of moments calls the constructor and then
`.percentileCI_coverage`. The bootstrap weak law and tightness are inputs to the planned
Z-estimator bootstrap study.

## May assume / must derive
- May assume: studies `efron-bootstrap-resampling`, `efron-bootstrap-mean-clt`,
  `polya-cdf-quantile-convergence`, `bootstrap-percentile-intervals`; Mathlib strong law and
  differentiability API; existing Causalean delta-method results (`Stat/Inference/DeltaMethod.lean`).
- Must derive: the bootstrap weak law, tightness, both linearizations, and the constructor. Only
  `∫ ‖g‖² dP < ∞` and differentiability of `h` at `m` (not continuous differentiability) may be
  assumed.

## Non-goals
- Z-/M-estimators (separate study), non-differentiable functionals (quantiles), second-order
  accuracy, the bootstrap for a degenerate derivative (`Dh (g − m) = 0` a.s.).

## Known building blocks
Promoted (waves 1-3). Reuse; do not redefine:
- `Causalean/Stat/Bootstrap/AsymptoticLinear/` — the interface this study extends:
  `BootstrapAsymLinear S est theta0 psi` (fields `meas`, `mean_zero`, `var_pos_finite`, `linear`,
  `boot_linear`), `asymptoticVariance`, `asymptoticGaussian`, `isAsymLinear`,
  `centeredEstimatorBootstrapStatistic`, `bootstrapEstimatorLaw`, `samplingEstimatorLaw`,
  `bootstrapQuantile`, `percentileCI`, `basicCI`, `measurable_bootstrapQuantile`,
  `bootstrapQuantile_eq_affine`, and on the bundle: `.consistent`, `.quantile_tendsto`,
  `.percentileCI_coverage`, `.basicCI_coverage`, plus `BootstrapAsymLinear.sampleMean` with
  `sampleMeanStatistic` (the pattern to imitate for the new constructor).
  Generic helpers in `LimitLemmas.lean`: `cdfKolmogorov_triangle`,
  `conditionalSlutsky_cdfKolmogorov_inProb`, `quantile_tendsto_inProb_of_cdfKolmogorov`,
  `tendsto_dist_random_Icc_coverage`, `gaussianReal_quantile_Icc_toReal`.
- `Causalean/Stat/Bootstrap/EfronResampling/`: `empiricalMeasure`, `bootstrapResample`,
  `bootstrapLaw`, `bootstrapCDF`, `bootstrapLowerQuantile`, `finAverage`,
  `integral_bootstrapResample_eq_average`, `integral_finAverage_bootstrapResample`,
  `integral_centered_finAverage_sq_bootstrapResample`, `variance_empiricalMeasure_eq_empiricalVar`,
  `measurable_bootstrapCDF`, `measurable_bootstrapLowerQuantile`; and `EfronResampling/Mean/`:
  `centeredBootstrapSum`, `bootstrapMeanLaw`, `bootstrapMeanLaw_tendsto_gaussian_ae`,
  `bootstrapMeanLaw_cdfKolmogorov_samplingMeanLaw_tendsto_ae`, `centeredEmpiricalLindeberg_tendsto_ae`.
- `Causalean/Stat/Quantile/CdfConvergence.lean`, `Causalean/Stat/CLT/Lindeberg.lean` (see wave-2 list).
- `Causalean.Stat.IIDSample.sampleVector`, `sampleMean`, `empiricalVar`; `Stat/Limit/WLLN.lean`;
  `Stat/Inference/DeltaMethod.lean` (`deltaMethod_rate`, `deltaMethod_scalar_rate`);
  `Stat/CLT/MultivariateCLT.lean`.
- Conventions the gate enforces: keep each new file under 600 lines; give every new theorem-bearing
  file 1-3 `headline_theorems` entries in `doc/library_review/Stat.json` and NL crosslinks on each
  headline docstring; library names must not reuse the run slug.

