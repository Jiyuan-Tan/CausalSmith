# Substrate requirement: efron-bootstrap-mean-clt

## Goal
Bickel–Freedman consistency of the nonparametric bootstrap for the sample mean: for almost every
data sequence, the bootstrap distribution of `√n (X̄*ₙ − X̄ₙ)` converges to `N(0, σ²)`, and (when
σ² > 0) it is uniformly close to the true sampling distribution of `√n (X̄ₙ − E X)`.

## Provides (API contract)
- Bootstrap CLT for the mean (almost sure). For a real i.i.d. sample `S : IIDSample Ω ℝ μ P` with
  `E X² < ∞` and `σ² = Var X`: for μ-a.e. ω, as n → ∞ (n ≥ 1), the bootstrap law `bootstrapLaw` of `x* ↦ √n (mean(x*) − X̄ₙ(ω))` at the data vector
  `(Z₀ ω, …, Z_{n−1} ω)` converges weakly to `gaussianReal 0 σ²`.
- Bootstrap consistency in Kolmogorov distance (almost sure). If also σ² > 0: for μ-a.e. ω,
  `sup_t |P*_ω(√n (X̄* − X̄ₙ) ≤ t) − μ(√n (X̄ₙ − E X) ≤ t)| → 0`.
- The same two results for a statistic of a general observation: data in any measurable space `X`
  and a measurable `ψ : X → ℝ` with `∫ ψ² dP < ∞`, bootstrapping `n^{-1/2} ∑ (ψ(x*ᵢ) − ψ̄ₙ)` with
  limit variance `Var ψ`. (The real-data version may be the specialization `ψ = id`.)

## Statement / milestones
1. For fixed ω, identify the bootstrap law of the centred scaled resample sum as the row-sum law of
   an i.i.d. triangular array with row law `R n` = empirical law of `ψ(Zᵢ ω) − ψ̄ₙ(ω)`, so the
   Lindeberg–Feller CLT `iidRowNormalizedSumLaw_tendsto_gaussian` applies pointwise in ω.
2. Variance condition a.s.: `∫ y² d(R n) = empiricalVar → Var ψ` almost surely (strong law).
3. Lindeberg condition a.s.: for each ε > 0,
   `n⁻¹ ∑_{i<n} (ψ(Zᵢ) − ψ̄ₙ)² 1{|ψ(Zᵢ) − ψ̄ₙ| ≥ ε√n} → 0` a.s. Route: for fixed M, eventually
   `ε√n ≥ M + |ψ̄ₙ|`-type domination bounds it by `n⁻¹ ∑ g_M(Zᵢ)` with `g_M` a truncated tail of ψ²;
   apply the strong law, then let M → ∞ through a countable sequence (dominated convergence).
4. Kolmogorov consistency: combine (1)–(3) with the i.i.d. CLT for the sampling law (Mathlib) and
   Pólya's theorem (`tendsto_cdfKolmogorov_of_tendsto`).

## Standard reference
Bickel & Freedman (1981, Ann. Statist. 9:1196–1217), Theorem 2.1; Singh (1981, Ann. Statist.
9:1187); van der Vaart, *Asymptotic Statistics*, Theorem 23.4.

## Intended reuse
Percentile and basic bootstrap confidence intervals for the mean and, through a linearization, for
asymptotically linear estimators (study `bootstrap-percentile-intervals`). The ψ-version is what
that consumer needs.

## May assume / must derive
- May assume: the promoted results listed under Known building blocks; Mathlib's strong law
  (`ProbabilityTheory.strong_law_ae_real`) and i.i.d. CLT.
- Must derive: the almost-sure variance and Lindeberg conditions and the two headline results.
  Only a finite second moment may be assumed — no higher moments.

## Non-goals
- Vector-valued means, bootstrap of non-smooth statistics, Edgeworth/second-order accuracy,
  bootstrap failure examples (infinite variance).

## Known building blocks
Promoted by the wave-1 studies (2026-09-17). Reuse these; do not redefine them:
- `Causalean/Stat/Bootstrap/EfronResampling/`: `Causalean.Stat.empiricalMeasure`,
  `bootstrapResample` (the product of `n` empirical draws), `bootstrapLaw T x`, `bootstrapCDF`,
  `bootstrapLowerQuantile`, `finAverage`, `bootstrapResample_eq_average_dirac`,
  `integral_bootstrapResample_eq_average`, `integral_finAverage_bootstrapResample`,
  `integral_centered_finAverage_sq_bootstrapResample`, `variance_empiricalMeasure_eq_empiricalVar`,
  `measurable_bootstrapCDF`, `measurable_bootstrapLowerQuantile`.
- `Causalean/Stat/CLT/Lindeberg.lean`: `iidRowSumLaw`, `iidRowNormalizedSumLaw`,
  `iidRowNormalizedSumLaw_tendsto_gaussian` (unscaled rows: mean 0, `∫ x² ∂R n → σ²`, Lindeberg tail
  `∫_{|x| ≥ ε√n} x² ∂R n → 0` ⇒ law of `n^{-1/2} Σ` → `gaussianReal 0 σ²`, σ² = 0 allowed),
  `iidRowSumLaw_tendsto_gaussian` (scaled rows), `iidRowSumLaw_scaledRowMeasure_eq_normalized`.
- `Causalean/Stat/Quantile/CdfConvergence.lean`: `tendstoUniformly_cdf_of_tendsto` (Pólya),
  `tendsto_cdfKolmogorov_of_tendsto`, `cdfKolmogorov`, `tendsto_quantile_of_tendsto`,
  `quantile_gaussianReal_zero`, `continuous_cdf_gaussianReal_zero`.
- `Causalean.Stat.IIDSample.sampleVector` (`Stat/CLT/SampleFnEstimator.lean`), `IIDSample.sampleMean`,
  `IIDSample.empiricalVar`, `empiricalVar_eq_centered`, `empiricalVar_tendsto_inProb`
  (`Stat/Inference/VarianceEstimation.lean`); `Stat/Limit/WLLN.lean` (uses
  `ProbabilityTheory.strong_law_ae_real`).
- Mathlib `tendstoInDistribution_inv_sqrt_mul_sum_sub` (`Probability/CentralLimitTheorem.lean`).
- Import note (module system): `Mathlib.Probability.CentralLimitTheorem` imports
  `Mathlib.MeasureTheory.Measure.LevyConvergence` privately; import the latter directly when using
  `ProbabilityMeasure.tendsto_iff_tendsto_charFun`.
