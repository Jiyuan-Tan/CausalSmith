# Substrate requirement: polya-cdf-quantile-convergence

## Goal
Pólya's theorem (weak convergence to a law with continuous CDF implies uniform convergence of the
CDFs) and convergence of quantiles, the two deterministic facts that turn a CLT into valid
confidence intervals built from estimated quantiles.

## Provides (API contract)
- `tendstoUniformly_cdf_of_tendsto` — if probability measures `ν n → ν` weakly on ℝ and
  `ProbabilityTheory.cdf ν` is continuous, then `cdf (ν n) → cdf ν` uniformly on ℝ.
- A two-sequence corollary: if `ν n → ν` and `ν' n → ν` weakly with `cdf ν` continuous, then
  `sup_t |cdf (ν n) t − cdf (ν' n) t| → 0`.
- A lower-quantile function for a probability measure on ℝ, `β ↦ sInf {t | β ≤ cdf ν t}`
  (reuse an existing Mathlib/Causalean definition if one exists).
- Quantile convergence: if `cdf (ν n) → cdf ν` uniformly (or pointwise near q) and `cdf ν` is
  continuous and strictly increasing at `q = quantile ν β`, with `β ∈ (0,1)`, then
  `quantile (ν n) β → q`.
- Gaussian instance: for `σ² > 0` the CDF of `gaussianReal 0 σ²` is continuous and strictly
  increasing, and its β-quantile is `√σ² · z_β` where `z_β` is the standard-normal quantile.

## Statement / milestones
1. Pólya: split ℝ by finitely many points where `cdf ν` takes values within ε of each other
   (possible by continuity and the limits 0 and 1), use pointwise convergence at those points
   (continuity points) and monotonicity in between.
2. Pointwise CDF convergence at continuity points from weak convergence (via Portmanteau / null
   frontier of `Iic t`), if not already in Mathlib or Causalean.
3. Quantile convergence (deterministic ε-argument from strict monotonicity at q).
4. Gaussian facts and quantile identification.

## Standard reference
van der Vaart, *Asymptotic Statistics*, Lemma 2.11 (Pólya) and Lemma 21.2 (quantile
convergence); Billingsley, *Probability and Measure*, Section 14.

## Intended reuse
Bootstrap consistency in Kolmogorov distance and percentile/basic bootstrap confidence intervals
(consumers apply these deterministic lemmas for each data realisation or along subsequences).
Also reusable for any Wald/quantile-based interval.

## May assume / must derive
- May assume: Mathlib's weak-convergence topology on `ProbabilityMeasure ℝ`, Portmanteau results,
  `ProbabilityTheory.cdf` and its properties, `gaussianReal` facts.
- Must derive: Pólya's uniform convergence and quantile convergence. Do not assume uniform CDF
  convergence as a hypothesis where the goal is to prove it.

## Non-goals
- Multivariate Pólya, rates (DKW / Berry–Esseen), random-measure versions.

## Known building blocks
- Mathlib: `ProbabilityTheory.cdf`, `MeasureTheory.ProbabilityMeasure` topology, Portmanteau
  (`Mathlib/MeasureTheory/Measure/Portmanteau.lean`), `gaussianReal`.
- Causalean: `Causalean.Stat.Tendsto_dist.tendsto_measure_of_null_frontier`
  (`Stat/Inference/Studentize.lean`), `Causalean.Mathlib.stdNormalCDF`, `probit`
  (`Mathlib/Probability/StdNormalCDF.lean`), `Stat/Quantile/*`.
