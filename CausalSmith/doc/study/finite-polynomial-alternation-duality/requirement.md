# Substrate requirement: finite-polynomial-alternation-duality

## Goal
Build axiom-clean reusable approximation-theory substrate for real polynomials on a compact nondegenerate interval: an affine-interval Markov derivative inequality and a finite Chebyshev alternation dual certificate for best uniform approximation.

## Provides (API contract)
- A theorem bounding `sup_{x in [r,s]} |Q'(x)|` by `2 * L^2 / (s-r)` times `sup_{x in [r,s]} |Q(x)|` whenever `r < s` and the real polynomial `Q` has degree at most `L`.
- A finite alternation-duality theorem for a continuous real target `f` on `[r,s]`: for approximation by polynomials of degree at most `L`, produce `L+2` strictly ordered nodes and normalized alternating signed Lagrange weights that annihilate every monomial through degree `L` and whose signed integral against `f` attains the best uniform approximation error (up to the theorem's explicit sign convention).
- Convenient paper-independent corollaries that package the nodes, normalization, moment annihilation, and target separation for downstream finite-support moment-prior constructions.

## Statement / milestones
For `Q : Polynomial Real`, `r < s`, and `Q.natDegree <= L`, prove the compact-interval Markov bound with the exact scaling factor `2 * L^2 / (s-r)` after affine reduction to `[-1,1]`.

For continuous `f : Real -> Real` on `Set.Icc r s`, prove existence of a best degree-`L` uniform approximant and a finite alternating dual witness with `L+2` ordered support points. Its normalized signed weights must sum in absolute value to one, annihilate `x^j` for every `j <= L`, and evaluate `f` to the best approximation error. Expose a specialization-friendly corollary for continuous rational targets such as `p / (p + a)` on an interval separated from the pole, without naming or importing any research run.

## Standard reference
The classical Markov brothers' inequality for algebraic polynomials and the Chebyshev alternation theorem / finite dual characterization of minimax polynomial approximation on a compact interval.

## Intended reuse
Reusable moment-matching lower bounds and polynomial-approximation arguments across Causalean. The immediate consumer is a finite-support moment dual for `f(p)=p/(p+a)`, but all shared declarations must remain generic over continuous real targets and compact nondegenerate intervals.

## May assume / must derive
May use established Mathlib results about real polynomials, derivatives, compactness, Lagrange interpolation, Chebyshev polynomials, finite-dimensional subspaces, and existence of minimizers. Must derive the affine scaling, the stated degree-dependent derivative constant, existence/order/normalization of the finite witness, monomial annihilation, and attainment of the best uniform approximation error. No `sorry`, `admit`, or new axioms.

## Non-goals (optional)
Do not import any `CausalSmith/*_Research` module or mention annotation studies, ATEs, priors, or run-specific types. Do not weaken the deliverable to an abstract Hahn-Banach functional without a finite ordered support witness. Multivariate approximation and asymptotic approximation rates are out of scope.

## Known building blocks (optional)
Inspect `Mathlib.LinearAlgebra.Lagrange`, `Mathlib.Analysis.Calculus.Deriv.Polynomial`, `Mathlib.Topology.Algebra.Polynomial`, `Mathlib.RingTheory.Polynomial.Chebyshev`, and `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Duality`. Reuse existing declarations where faithful; do not duplicate an existing Mathlib/Causalean theorem.
