# Substrate requirement: bootstrap-percentile-intervals

## Goal
Validity of the nonparametric bootstrap for asymptotically linear estimators — the version used in
applied econometrics: under a linearization of both the estimator and its bootstrap replicate, the
bootstrap distribution of `√n (θ̂* − θ̂)` is consistent for that of `√n (θ̂ − θ₀)`, and the
percentile and basic bootstrap confidence intervals have asymptotic coverage 1 − α.

## Provides (API contract)
This study is the public entry point other users call, so the interface matters as much as the
proofs. Names below are suggestions; keep the shape.

Setting: `S : IIDSample Ω X μ P`; an estimator given as a statistic of the sample vector,
`est : (n : ℕ) → (Fin n → X) → ℝ` (so it can be evaluated at a resample); target `θ₀ : ℝ`;
influence function `ψ : X → ℝ`. Write `S.sampleVector n ω = (Z₀ ω, …, Z_{n−1} ω)` (existing
`Causalean.Stat.IIDSample.sampleVector`, `Stat/CLT/SampleFnEstimator.lean`; reuse it), and `P*_x` for the bootstrap resampling law at data `x`.

Named objects (definitions, so users can state results about them):
- `bootstrapQuantile est n β x` — lower β-quantile of the bootstrap law of
  `x* ↦ √n (est n x* − est n x)`.
- `percentileCI est n α x = [est n x + q_{α/2}/√n, est n x + q_{1−α/2}/√n]` and
  `basicCI est n α x = [est n x − q_{1−α/2}/√n, est n x − q_{α/2}/√n]`, with
  `q_β = bootstrapQuantile est n β x`.

A bundled hypothesis structure `BootstrapAsymLinear S est θ₀ ψ` with fields:
- `meas` : each `est n` and `ψ` measurable;
- `mean_zero` : `∫ ψ dP = 0`; `var_pos_finite` : `0 < ∫ ψ² dP < ∞`;
- `linear` (sampling linearization):
  `√n (est n (S.sampleVector n ω) − θ₀) − n^{-1/2} ∑_{i<n} ψ(Zᵢ ω) → 0` in μ-probability;
- `boot_linear` (bootstrap linearization): for every ε > 0,
  `μ{ω : P*_{x}(|√n (est n x* − est n x) − n^{-1/2} ∑ᵢ (ψ(x*ᵢ) − ψ̄(x))| > ε) > ε} → 0`,
  where `x = S.sampleVector n ω` and `ψ̄(x)` is the mean of `ψ` over `x`.

Conclusions as dot-notation theorems on `h : BootstrapAsymLinear S est θ₀ ψ`, with `σ² = ∫ ψ² dP`:
- `h.consistent` : `sup_t |P*_x(√n (est* − est) ≤ t) − μ(√n (est − θ₀) ≤ t)| → 0` in μ-probability.
- `h.quantile_tendsto` : for β ∈ (0,1), `bootstrapQuantile est n β (S.sampleVector n ·) → √σ² · z_β`
  in μ-probability.
- `h.percentileCI_coverage`, `h.basicCI_coverage` : for α ∈ (0,1),
  `μ{ω : θ₀ ∈ CI est n α (S.sampleVector n ω)} → 1 − α`, with the events proved measurable.
- Constructor `BootstrapAsymLinear.sampleMean` : the sample mean of a real square-integrable
  non-degenerate observation satisfies the structure with `ψ = x − E X` (both linearizations exact),
  so users get the mean's percentile and basic intervals in one line.
- A bridge lemma: `h.linear` gives the existing `IsAsymLinear` for
  `θn n ω = est n (S.sampleVector n ω)`, so users can also reach the existing Wald results.

## Statement / milestones
1. Conditional Slutsky in Kolmogorov distance: if the bootstrap law of the linear part is
   Kolmogorov-close to `N(0,σ²)` and the bootstrap remainder is small in bootstrap probability,
   the bootstrap law of the sum is Kolmogorov-close to `N(0,σ²)` (continuity of the normal CDF).
2. Linear part: `bootstrapMeanLaw_tendsto_gaussian_ae` (almost-sure bootstrap CLT for `ψ`), upgraded
   with Pólya (`tendstoUniformly_cdf_of_tendsto`) to Kolmogorov distance.
3. Sampling side: `√n(θ̂ − θ₀) ⇒ N(0,σ²)` from the sampling linearization (existing Causalean
   asymptotic-linearity CLT or Mathlib CLT + Slutsky), then Pólya.
4. Quantile convergence in probability (`tendsto_quantile_of_tendstoUniformly` /
   `tendsto_quantile_of_tendsto`, applied on the high-probability event or along subsequences).
5. Coverage: rewrite `θ₀ ∈ CIₙ` as `√n (θ̂ − θ₀)` lying between two bootstrap quantiles, prove
   the event measurable (`measurable_bootstrapLowerQuantile`), and conclude with Slutsky + the continuous normal limit.
6. Sample-mean corollary.

## Standard reference
van der Vaart, *Asymptotic Statistics*, Section 23.2 (Lemma 23.3, Theorem 23.9 and its
corollaries); Horowitz (2001), "The Bootstrap", *Handbook of Econometrics* Vol. 5, Section 2;
Shao & Tu, *The Jackknife and Bootstrap*, Ch. 3–4.

## Intended reuse
The user-facing bootstrap API. Estimator-class studies (smooth functions of means, Z-estimators)
will add further constructors of `BootstrapAsymLinear`, so a consumer only needs to show their
estimator is in a covered class and then call `.percentileCI_coverage`.

## May assume / must derive
- May assume: the promoted results listed under Known building blocks; existing Causalean
  asymptotic-linearity CLT; measurability of `θ̂ n` and `ψ`.
- Must derive: every conclusion above from the two linearization hypotheses. Coverage must be
  stated for measurable events (prove measurability; do not state it with outer measure).
  Do not add hypotheses beyond the setting and the two linearizations.

## Known building blocks
Promoted and committed (44eb3dc41). Reuse; do not redefine:
- `Causalean/Stat/Bootstrap/EfronResampling/`: `empiricalMeasure`, `bootstrapResample`,
  `bootstrapLaw T x`, `bootstrapCDF`, `bootstrapLowerQuantile T β x` (lower β-quantile of
  `bootstrapLaw T x`), `measurable_bootstrapCDF`, `measurable_bootstrapLowerQuantile`, `finAverage`,
  `integral_bootstrapResample_eq_average`.
- `EfronResampling/Mean/`: `centeredBootstrapSum ψ x x*` (`n^{-1/2} Σ (ψ(x*ᵢ) − ψ̄(x))`),
  `bootstrapMeanLaw S ψ hψ n ω`, `samplingMeanLaw`, `populationVariance`,
  `bootstrapMeanLaw_tendsto_gaussian_ae` (a.s. → `N(0, Var ψ)`, only `∫ψ² < ∞`),
  `bootstrapMeanLaw_cdfKolmogorov_samplingMeanLaw_tendsto_ae`, and the `bootstrapRealMeanLaw_*`
  (ψ = id) versions; `centeredEmpiricalSecondMoment_tendsto_ae`, `centeredEmpiricalLindeberg_tendsto_ae`.
- `Causalean/Stat/Quantile/CdfConvergence.lean`: `cdfKolmogorov`, `tendstoUniformly_cdf_of_tendsto`,
  `tendsto_cdfKolmogorov_of_tendsto`, `tendsto_quantile_of_tendsto`,
  `tendsto_quantile_of_tendstoUniformly`, `StrictlyIncreasingAt`, `quantile_gaussianReal_zero`,
  `continuous_cdf_gaussianReal_zero`, `strictMono_cdf_gaussianReal_zero`; the lower quantile
  `Causalean.Stat.quantile` (`Stat/Quantile/Quantile.lean`); `Causalean.Mathlib.probit`.
- `Causalean.Stat.IIDSample.sampleVector` (`Stat/CLT/SampleFnEstimator.lean`); `IsAsymLinear`,
  `IsAsymLinear.tendsto_normal` (`Stat/CLT/AsymptoticLinearity.lean`);
  `Tendsto_dist`, `Tendsto_inProb` (`Stat/Limit/Convergence.lean`); Slutsky-type lemmas in
  `Stat/CLT/AsymptoticLinearity.lean` and `Stat/Inference/Studentize.lean`.
- Import note (module system): `Mathlib.Probability.CentralLimitTheorem` imports
  `Mathlib.MeasureTheory.Measure.LevyConvergence` privately; import the latter directly when needed.
- Naming: library module and declaration names must not reuse this study's run slug.

## Non-goals
- Proving the bootstrap linearization for specific estimator classes (Z-estimators, Hadamard-
  differentiable functionals) — consumers supply it.
- Bootstrap-t / studentized intervals, bootstrap standard errors (need uniform integrability),
  second-order refinements, multiplier/wild/block bootstraps, Monte Carlo error from finite B.
