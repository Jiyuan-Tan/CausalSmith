# Substrate requirement: nested-paired-poisson-product-moments

## Goal
Build reusable finite nested-array probability infrastructure that makes paired-Poisson Poincaré bounds and their energy integrals reducible to scalar Poisson moments.

## Provides (API contract)
- A public measurable equivalence and measure-preserving theorem flattening `iota → kappa → Nat × Nat` under `nestedPairedPoissonMeasure lambda₁ lambda₂` to a finite `Sigma i (Sigma j (Fin 2)) → Nat` Poisson product.
- `memLp_nestedPairedPoisson_of_polynomial_bound`, or an equally composable finite-coordinate criterion, proving `MemLp F 2` for real functions and their add-one increments from a finite polynomial-growth bound.
- Finite-coordinate product-integral/factorization lemmas evaluating or bounding integrals of products and squares of coordinate functions under the nested paired law by scalar Poisson moments.

## Statement / milestones
Expose the flattening equivalence and map/measure-preserving chain currently constructed privately inside `nestedPairedPoisson_addOne_poincare`. Use it to prove finite polynomial moments and an L² criterion for polynomial-growth functions and all coordinate add-one increments. Provide factorization identities or inequalities sufficient to reduce the tensorized Poincaré energy of rational polynomial-growth finite-sum statistics to scalar shifted-reciprocal Poisson moments.

## Standard reference
Standard finite-product probability: measurable equivalence under reassociation/flattening, independence/product-measure factorization, finite Poisson moments, and polynomial-growth L² integrability.

## Intended reuse
The immediate consumer is `poisson_inverse_count_risk` in `stat_semisupervised_discrete_ate_annotation_frontier/v1`, then the inverse-count baseline and mixed-estimator upper-bound chain. The shared API must work for arbitrary finite nested index types and paired nonnegative Poisson rates.

## May assume / must derive
May assume finite index types, nonnegative Poisson rates, measurability of the statistic, and an explicit finite polynomial-growth bound. Must derive the public flattening/measure-preserving theorem, polynomial-moment/L² closure, add-one increment closure, and product-integral factorization. All public declarations must have zero `sorry`, use no `admit`, and introduce no axioms.

## Non-goals (optional)
Do not import any `CausalSmith/*_Research` module. Do not encode the paper's inverse-count statistic or its scalar shifted reciprocal identities; those remain run-local. Do not reprove the already promoted scalar or tensorized Poisson Poincaré theorems.

## Known building blocks (optional)
Reuse `Causalean.Mathlib.Probability.PoissonAddOnePoincare.Tensorization`, `Causalean.Mathlib.Probability.PoissonPi`, `Mathlib.Probability.Distributions.Poisson.Basic`, and `Mathlib.MeasureTheory.Function.LpSpace.Basic`. In particular, refactor/export the private flattening construction around `nestedPairedPoisson_addOne_poincare` rather than duplicating it.
