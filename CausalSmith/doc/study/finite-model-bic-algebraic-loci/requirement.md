# Reusable finite-model BIC consistency and algebraic-locus closure

## Goal

Build axiom-clean, zero-sorry Causalean lemmas, independent of every CausalSmith research module, for two standard ingredients used together in generic finite-model selection.

## Provides (API contract)

1. Finite penalized argmin consistency: for a finite nonempty model index type with a deterministic tie rank, prove that if random empirical loss coordinates converge in probability to population losses, the population minimizers are separated from all nonminimizers by a strictly positive gap, model penalties are deterministic and o(n), and the selector minimizes n times empirical loss plus the penalty with the fixed tie rule, then the selector belongs to the population-minimizer class with probability tending to one. Provide a specialization-friendly formulation in Causalean.Stat.Tendsto_inProb / measure-event language; a finite-uniform-convergence helper may be factored separately.

2. Finite real multivariate-polynomial zero-locus closure: prove that the union of a finite family of zero loci equals the zero locus of the product polynomial, and that this product is nonzero when every factor is nonzero. Include the finite-subtype/indexed form needed to package finitely many exceptional equations as one proper algebraic locus.

## Statement / milestones

- Establish finite uniform convergence in probability from coordinatewise convergence.
- Prove the finite penalized-selector consistency theorem with deterministic tie-breaking and sublinear penalties.
- Prove finite zero-locus union/product equality for real multivariate polynomials.
- Prove nonvanishing of the finite product under nonvanishing of each factor, including a finite indexed/subtype form.
- Verify the final declarations with a real build, source grep for `sorry`/`admit`/`axiom`, and `#print axioms`.

## Standard reference

These are standard finite-model M-estimation/BIC separation arguments and integral-domain identities for multivariate polynomials. Use existing Mathlib and Causalean convergence and polynomial APIs wherever possible.

## Intended reuse

The current paper will locally prove its Gaussian likelihood gap and individual polynomial equations, then specialize these generic lemmas. The results should also support other fixed finite-model selection and generic-identifiability arguments.

## May assume / must derive

May assume coordinatewise convergence in probability, a strictly positive population loss gap, deterministic penalties with penalty/n tending to zero, and that each indexed polynomial factor is nonzero. Must derive finite-uniform convergence, selector-class consistency, union-as-product-zero-locus equality, and nonzero product.

## Non-goals

Do not mention `BlockedState`, covariance models, or `exceptionalSet`, and do not import any `CausalSmith.*_Research` module. Do not prove the paper-specific Gaussian likelihood gap or construct its individual exceptional polynomials.

## Known building blocks

Search `Causalean.Stat.Limit.Convergence` and `Causalean.Stat.Sample` for convergence-in-probability notation; use Mathlib probability/topology finite-set lemmas and `Mathlib.Algebra.MvPolynomial` plus integral-domain/product lemmas. Let the study coordinator choose the narrowest final Causalean modules.
