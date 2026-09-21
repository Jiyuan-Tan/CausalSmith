# Substrate requirement: semialgebraic stratification and Sard

## Goal
Build reusable Lean infrastructure for finite-dimensional real semialgebraic projection, boundary nullity, finite Whitney/Nash stratification, and the semialgebraic Sard dimension drop needed for generic-translation arguments.

## Provides (API contract)
- A paper-agnostic predicate or existing compatible interface expressing that a subset of a finite-dimensional real coordinate space is semialgebraic.
- A theorem that coordinate projections of semialgebraic sets are semialgebraic (Tarski–Seidenberg).
- A theorem that the topological boundary of a semialgebraic subset of a finite-dimensional real coordinate space has strictly smaller semialgebraic dimension and hence ambient Lebesgue measure zero.
- A finite Whitney stratification theorem for semialgebraic sets by continuously differentiable Nash strata, sufficient to stratify a set and the boundary of another set simultaneously after refinement.
- A Sard theorem saying that the critical-value set of a Nash map between Nash manifolds is semialgebraic and has dimension strictly smaller than the target manifold.
- A reusable corollary for two finitely Whitney/Nash-stratified semialgebraic sets in `ℝ^d`: outside an ambient Lebesgue-null set of translations, every pair of strata is transverse under the subtraction map `(u,e) ↦ u - e`.

## Statement / milestones
For semialgebraic `C E ⊆ ℝ^d`, with `E` compact, full-dimensional, and regular closed, produce finite Nash Whitney stratifications of `C` and `frontier E`. For every stratum pair, the subtraction map is Nash. Its nonregular values form a semialgebraic set of dimension less than `d`, hence a Lebesgue-null set. The finite union of those exceptional sets is null, so almost every translation makes all stratum intersections transverse. The implementation may expose more primitive general theorems instead of one monolithic corollary, but each listed API fact must be axiom-free and reusable.

## Standard reference
Bochnak, Coste, and Roy, *Real Algebraic Geometry* (1998), Theorem 2.2.1, Proposition 2.8.13, Theorem 9.6.2, and Theorem 9.7.11, DOI 10.1007/978-3-662-03718-8.

## Intended reuse
The immediate consumer is `scm_partialdiff_uniform_singledoor/v1`, specifically its generic ellipsoid-intersection stability lemma and boundary random-set limit. The API must not mention LDiffPC, SCMs, covariance matrices, ellipsoids, or this paper; it should work for arbitrary finite-dimensional real semialgebraic sets and Nash maps.

## May assume / must derive
May reuse any existing Mathlib facts about finite-dimensional Euclidean spaces, manifolds, differentiability, transversality, Sard, Lebesgue-null sets, polynomial maps, and measure zero. Must derive the semialgebraic closure properties, finite stratification/refinement, dimension-drop-to-null bridge, and generic-translation corollary from imported axiom-free infrastructure. No `sorry`, `admit`, `axiom`, `native_decide`, classical theorem placeholder, or paper-specific assumption is permitted.

## Non-goals (optional)
No effective CAD algorithm, complexity bound, quantifier-elimination executable, algebraic certificate extraction, o-minimal generalization, or paper-specific boundary-limit theorem is required.

## Known building blocks (optional)
The parent formalization found generic topology, measure, manifold, and graph ingredients in Mathlib/Causalean but no existing LDiffPC, Tarski–Seidenberg, real-semialgebraic, Whitney/Nash stratification, or matching Sard interface. Re-search before defining anything to avoid duplicating a newly available primitive.
