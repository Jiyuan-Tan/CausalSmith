# Gaussian covariance discrepancy and rational-locus compilers

## Goal

Build axiom-clean, zero-sorry Causalean lemmas, independent of every CausalSmith research module, for reusable Gaussian covariance-discrepancy and rational-map algebraic-locus arguments.

## Provides (API contract)

1. Gaussian covariance discrepancy on positive-definite matrices. For a finite index type, package `log det K + trace (K⁻¹ * T)` and prove the continuity and strict-gap facts needed to compare finitely many covariance-model classes: the normalized discrepancy is minimized exactly at `K = T`; a true covariance separated from a competing closed/model set has a strictly positive population gap under appropriate compactness/coercivity hypotheses; and this gap is stable under covariance perturbations. Provide a theorem surface that composes with `Causalean.Stat.finite_penalized_argmin_consistent` when empirical covariance converges in probability. Factor attainment/coercivity separately and state all topological hypotheses explicitly rather than assuming a paper-specific model image.

2. Rational-map algebraic-locus compilers over `ℝ`. Develop a specialization-friendly representation for finite-dimensional rational maps whose denominators are nonzero on a domain. Prove that equality/intersection conditions between polynomial or rational matrix maps can be cleared to finitely many multivariate-polynomial equations, and that their finite conjunction/union can be represented by one zero locus. Prove a characteristic-zero derivative compiler: for a nonconstant rational scalar coordinate, the locus where its full Fréchet derivative vanishes is the zero locus of a nonzero multivariate polynomial, under explicit denominator/domain hypotheses. Include matrix inverse via adjugate/determinant and finite-coordinate forms.

## Statement / milestones

- Define the Gaussian covariance discrepancy with explicit finite-dimensional positive-definiteness hypotheses.
- Prove continuity, unique minimization at the truth, strict separation from appropriate compact/closed competitors, and perturbation stability.
- Define a finite-dimensional rational-map representation with explicit nonvanishing denominators.
- Clear equality/intersection and zero-derivative conditions to finite polynomial equations, combine them using the existing finite polynomial zero-locus lemmas, and prove the resulting polynomial is nonzero under explicit witness/nonconstancy hypotheses.
- Include specialization-friendly finite-coordinate and matrix adjugate/determinant forms.
- Finish with a real build, source grep for `sorry`/`admit`/`axiom`, and `#print axioms`.

## Standard reference

Use standard finite-dimensional Gaussian likelihood/KL matrix inequalities, compact minimum-separation arguments, and elementary rational-function denominator clearing in characteristic zero. Prefer existing Mathlib matrix, topology, calculus, and multivariate-polynomial APIs.

## Intended reuse

The current paper will instantiate these generic results for a finite family of blocked covariance images and labelled total-effect coordinates. The theorem surfaces should also support other finite Gaussian covariance-model selection and generic rational-identifiability arguments.

## May assume / must derive

May assume explicit positive-definiteness, compactness/coercivity or attainment conditions, denominator nonvanishing on the domain, finite-dimensional coordinate representations, and paper-supplied witnesses/nonconstancy. Must derive the generic discrepancy continuity/separation/stability and the rational equality/derivative polynomial compilers.

## Non-goals

Do not mention `BlockedState`, `covModel`, `rawCovParam`, `effectVectorFormula`, or `exceptionalSet`, and do not import any `CausalSmith.*_Research` module. Do not prove model-specific closedness/coercivity, rational representations, denominator nonvanishing, or witnesses for distinct model intersections and nonconstant-effect gradients.

## Known building blocks

Search `Mathlib.Analysis.SpecialFunctions.Log.Basic`, finite-dimensional topology and compactness, matrix determinant/inverse/positive-definite APIs, `Causalean.Stat.MEstimation.FiniteModelSelection`, `Mathlib.Algebra.MvPolynomial`, `Mathlib.FieldTheory.RatFunc`, `Mathlib.Analysis.Calculus.FDeriv.Basic`, and `Causalean.Mathlib.MeasureTheory.PolynomialZeroLocus`. Let the study coordinator choose the narrowest final Causalean modules.
