# Substrate requirement: uniform compact correspondence exclusion

## Goal
Formalize a reusable uniform compact-family exclusion theorem for continuous parameter-dependent residuals and parameter-dependent reference neighborhoods, with a finite-dimensional real square-matrix specialization.

## Provides (API contract)
- A definition/structure recording an attained positive residual minimum on the far part of a compact feasible correspondence, analogous to the existing `PositiveExclusionRadius` but uniform over a compact parameter family.
- A general theorem: the far feasible set is empty, or its continuous nonnegative residual has an attained strictly positive minimum and therefore one uniform positive exclusion tolerance.
- A convenient implication form saying every feasible pair with residual at most the uniform tolerance lies strictly inside its parameter-dependent reference neighborhood.
- A specialization for finite-dimensional real square matrices using the Euclidean/operator-norm distance, suitable for simultaneous-congruence residuals.

## Statement / milestones
Let `P` and `X` be topological/metric spaces with the assumptions genuinely needed for compactness and distance continuity. Let `K : Set (P × X)` be a compact feasible correspondence, `x₀ : P → X` a continuous reference section, `r : P × X → ℝ` a continuous nonnegative residual, and `ρ : P → ℝ` a continuous strictly positive radius. Assume:

- `(p, x₀ p) ∈ K` for every relevant parameter `p` (or every `p` in an explicitly supplied compact parameter domain);
- for `(p,x) ∈ K`, `r (p,x) = 0` implies `x = x₀ p`;
- the far set `F = {(p,x) ∈ K | dist x (x₀ p) ≥ ρ p}` is closed, either as an explicit hypothesis or derived from continuity;
- `r` is nonnegative on `K`.

Prove the dichotomy:

1. `F` is empty; or
2. there exist `(p*,x*) ∈ F` and `ε₀ > 0` such that `r (p*,x*) = ε₀` and `ε₀ ≤ r (p,x)` for every `(p,x) ∈ F`.

Derive a uniform exclusion corollary: for some `ε₀ > 0`, every `(p,x) ∈ K` satisfying `r (p,x) < ε₀` (or `≤ ε₀/2`) obeys `dist x (x₀ p) < ρ p`. Handle the empty-far-set branch explicitly so the theorem always supplies a positive tolerance.

Provide a specialization where `X` is real `d × d` matrices with the Euclidean operator norm (or a provably equivalent matrix norm), `P` is any compact parameter type/set, and the far condition is matrix distance at least `ρ p`. The specialization should compose with a simultaneous-congruence residual but need not hard-code paper-specific tuples.

## Standard reference
Standard compactness and extreme-value argument: a closed subset of a compact feasible correspondence is compact; a continuous real residual attains its minimum there; unique-zero identification excludes zero on the far set, making the attained minimum positive. This generalizes the existing `Causalean.Discovery.LinearDisentanglement.Quantitative.exists_positiveExclusionRadius` from one fixed reference problem to a compact parameterized correspondence.

## Intended reuse
Reusable for uniform local-stability/contraction theorems where each parameter has its own reference solution and neighborhood, especially simultaneous congruence and linear disentanglement. The immediate consumer ranges over bounded true systems, candidate covariances, nuisance matrices, shifts, and finitely many subsets, but all of that tuple construction remains paper-local. The substrate must expose a generic compact-correspondence interface.

## May assume / must derive
May assume: compactness of the feasible correspondence (and an explicit compact parameter domain if used); continuity of the reference section, residual, and positive radius; nonnegativity; exact-zero uniqueness; metric/topological separation assumptions; and closedness of the far set if the theorem does not derive it from continuity.

Must derive: compactness of the far feasible set from `K` and closedness; attainment of the residual minimum; strict positivity from zero uniqueness and the positive radius; a positive tolerance in both empty and nonempty far-set branches; and the uniform near-reference implication. Do not assume the desired uniform minimum or uniform exclusion tolerance.

## Non-goals (optional)
No paper-specific `*_Research` imports or types; no BACKSHIFT system/corruption/confidence-region structures; no proof that a particular paper's tuple set is compact; no conversion from confidence radius to congruence residual; no effective computation of the minimum; no finite-sample probability or algorithmic claim. The theorem is intentionally existential/non-effective.

## Known building blocks (optional)
Mathlib compact sets, closed subsets of compact sets, continuous functions on products, continuity of distance/norm, extreme-value/minimum attainment, and finite-dimensional real matrix topology. Reuse or generalize `Causalean.Discovery.LinearDisentanglement.Quantitative.CompactExclusion`, especially `PositiveExclusionRadius` and `exists_positiveExclusionRadius`, where faithful. Imports may use only Mathlib, Causalean, and neutral modules in this study staging tree.
