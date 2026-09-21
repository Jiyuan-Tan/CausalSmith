# Substrate requirement: poisson-add-one-poincare

## Goal
Build axiom-clean reusable Poisson concentration substrate proving the scalar add-one Poincaré variance inequality and a finite-product tensorized corollary.

## Provides (API contract)
- A scalar theorem: for every `lambda : NNReal` and real function `f : Nat → Real` satisfying the appropriate measurability and L² hypotheses under `poissonMeasure lambda`, `Var(f(N)) ≤ lambda * E[(f(N+1)-f(N))^2]`, including `lambda = 0`.
- A finite-product/tensorized theorem for independent Poisson coordinates, compatible with `Measure.pi` and coordinate replacement, bounding the variance of a finite statistic by the sum of its expected squared add-one coordinate increments.
- Supporting countable-series lemmas needed to make the scalar result usable for arbitrary L² functions.

## Statement / milestones
Prove the pairwise product-law variance identity, triangular double-`tsum` reindexing/Tonelli, finite telescoping with Cauchy–Schwarz, and the Poisson shift identity `n * p_n = lambda * p_(n-1)`. First establish the add-one inequality for finite-support functions, then pass to arbitrary L² functions by finite-support truncation and L² closure. Tensorize over a finite coordinate type using conditional/product variance decomposition and coordinate replacement.

## Standard reference
The Poisson Poincaré inequality is standard in concentration of measure for Poisson laws; the product result is the standard Efron–Stein/Poincaré tensorization over independent coordinates.

## Intended reuse
The immediate consumer is `poisson_inverse_count_risk` in `stat_semisupervised_discrete_ate_annotation_frontier/v1`, followed by `inverse_count_baseline`, the uniform mixed upper bound, and the headline frontier theorem. Shared declarations must be paper-independent and support finite coordinate products such as `Fin d → Bool → Nat × Nat`.

## May assume / must derive
May assume standard measurability, integrability/L² hypotheses, Mathlib's Poisson mass formula, and existing product variance decomposition. Must derive the scalar add-one inequality including `lambda=0`, the countable-series/truncation closure used by it, and finite-product tensorization. All public results must have zero `sorry`, use no `admit`, and introduce no axioms.

## Non-goals (optional)
Do not import any `CausalSmith/*_Research` module. Do not encode the paper's inverse-count statistic or reciprocal-Poisson moment estimates; after promotion those are run-local specializations. Do not weaken the result to finite-support functions only.

## Known building blocks (optional)
Search and reuse `Mathlib.Probability.Distributions.Poisson.Basic`, `Mathlib.Probability.Moments.Variance`, `Mathlib.MeasureTheory.Integral.Prod`, `Causalean.Mathlib.Probability.VarianceProd`, `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.KL`, `integral_poissonMeasure`, `integrable_poissonMeasure_iff`, `poissonMeasure_singleton`, `variance_eq_integral`, and `variance_prod_eq_integral_variance_add`.
