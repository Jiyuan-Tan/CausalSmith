# Substrate requirement: efron-bootstrap-resampling

## Goal
The nonparametric (Efron) bootstrap as an actual resampling distribution: the empirical measure of
a data vector, the law of an n-point resample drawn with replacement from it, the bootstrap law of
a statistic, and the exact finite-sample facts about it.

## Provides (API contract)
- `empiricalMeasure (x : Fin n → X) : Measure X := (n)⁻¹ • ∑ i, dirac (x i)`, a probability measure
  when `n ≠ 0` (reuse an existing definition if Causalean/Mathlib has one).
- `bootstrapResample (x : Fin n → X) : Measure (Fin n → X) := Measure.pi (fun _ => empiricalMeasure x)`
  — n draws with replacement.
- `bootstrapLaw (T : (Fin n → X) → ℝ) (x : Fin n → X) : Measure ℝ := (bootstrapResample x).map T`
  — the bootstrap distribution of statistic `T` given data `x`.
- Finite-average representation: `bootstrapResample x = (n^n)⁻¹ • ∑ j : Fin n → Fin n, dirac (x ∘ j)`,
  hence `∫ f ∂(bootstrapResample x) = (n^n)⁻¹ ∑ j, f (x ∘ j)` for measurable `f`.
- Exact moments for real data `x : Fin n → ℝ`, `n ≠ 0`, with `x̄ = n⁻¹ ∑ x i`:
  bootstrap mean of the resample mean equals `x̄`; bootstrap second moment of
  `√n (mean(x*) − x̄)` equals `n⁻¹ ∑ (x i − x̄)²`.
- Link to the existing plug-in variance: for an `IIDSample S` and `ψ : X → ℝ`, the variance of
  `ψ` under `empiricalMeasure` of the first `n` observations equals
  `Causalean.Stat.IIDSample.empiricalVar S ψ n ω`.
- Measurability in the data: for measurable `T` and each `t : ℝ`, the bootstrap CDF
  `x ↦ (bootstrapLaw T x (Iic t)).toReal` is measurable, and so is the bootstrap lower β-quantile
  `x ↦ sInf {t | β ≤ bootstrap CDF at t}`.

## Statement / milestones
1. Definitions and the probability-measure instance.
2. Finite-average representation (product of finite sums of Diracs).
3. Exact bootstrap mean/variance identities for the sample mean.
4. `empiricalVar` link.
5. Measurability of the bootstrap CDF (finite sum of measurable indicators) and quantile (reduce the
   infimum to rationals by right-continuity).

## Standard reference
Efron (1979, Ann. Statist. 7:1); Efron & Tibshirani, *An Introduction to the Bootstrap*, Ch. 6;
Shao & Tu, *The Jackknife and Bootstrap*, Section 1.4 and 3.1.

## Intended reuse
The foundation for the bootstrap CLT for the mean and for percentile/basic bootstrap confidence
intervals of asymptotically linear estimators; measurability is needed so that coverage
probabilities are genuine probabilities of measurable events.

## May assume / must derive
- May assume: standard Mathlib measure theory (`Measure.pi`, `dirac`, finite sums).
- Must derive: every item above. The bootstrap must be defined as resampling (a product of
  empirical measures), not as a formula for its variance.

## Non-goals
- Limit theorems (separate studies), parametric/residual/block/wild bootstraps, Monte Carlo
  approximation of the bootstrap law by B simulated resamples.

## Known building blocks
- `Causalean.Stat.IIDSample`, `IIDSample.sampleMean`, `IIDSample.empiricalVar`
  (`Stat/Inference/VarianceEstimation.lean`), `Stat/Sample/EmpiricalMass.lean`.
- Mathlib `MeasureTheory.Measure.pi`, `Measure.dirac`, `Measure.pi_pi`.
