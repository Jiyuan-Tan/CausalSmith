# Substrate requirement: rectangular-signal-singular-values

## Goal
Build reusable singular-value theorems for rectangular full-rank products, orthonormal signal-subspace compression, and vertical stacks.

## Provides (API contract)
- Rectangular product lower bound: for full-column-rank finite real maps/matrices `A`, `B` and square core `D`, bound the last nonzero singular value of `A * D * Bᵀ` below by the product of the least signal singular values/lower moduli of `A`, `D`, and `B`; handle the noninjective ambient transpose by restricting to its rank-k signal subspace.
- Orthonormal compression: if `V` has orthonormal columns and its range is the adjoint range/row space of rank-k `M`, prove `singularValues (M ∘ V) (k-1) = singularValues M (k-1)`, or an all-nonzero-singular-values equivalent.
- Vertical-stack monotonicity: the kth singular value of a compatible direct-sum/vertical stack of `M0,M1` is at least that of either component, or expose a Gram/eigenvalue result giving this immediately.

## Statement / milestones
Prefer generic finite-dimensional real `LinearMap` statements with explicit zero-extension/index side conditions and thin finite-matrix corollaries. A min–max, lower-modulus-on-subspace, Gram-operator, or partial-isometry development is acceptable, but exported results must directly cover the three contracts above.

## Standard reference
Standard matrix analysis: multiplicative lower bounds for nonzero singular values, invariance under restriction to an orthonormal basis of the signal/right-singular subspace, and monotonicity under adding a positive Gram summand in a vertical stack.

## Intended reuse
The run `stat_proxy_effectlaw_eigencollision_frontier/v1` needs thin adapters for proxy-moment factorization, signal-basis compression, and stacked signal margins. These theorems should be reusable for rectangular identification operators and weak-rank arguments throughout Causalean.

## May assume / must derive
May assume finite-dimensional real inner-product spaces, full-column-rank/injectivity on the stated signal maps, orthonormality, and the exact range equality for compression. Must derive the correct nonzero-spectrum/indexed bounds without pretending an ambient transpose is injective.

## Non-goals
Do not import any `*_Research` module or mention `UCVMWModel`, proxy moments, `SignalBasis`, or paper summary objects. Do not weaken to an additive Weyl bound or only the final singular value of an everywhere-injective square map.

## Known building blocks
Use Mathlib adjoint, singular values, direct sums, Gram operators, and finite-dimensional spectral facts, plus the promoted `Causalean.Mathlib.Analysis.SingularValueWeyl` min–max support if useful.

Verification requires targeted builds, zero `sorry`/`admit`/custom axioms, and standard-only `#print axioms`.
