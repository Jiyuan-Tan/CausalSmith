## Done
- Ground-truth audit found four compiling modules and exactly 12 remaining `sorry`s.
- `Basic.lean`: Boolean closure, finite unions, coordinate products, map images, closure, interior, and frontier are proved.
- `DimensionBoundary.lean`: empty-set characterization, ambient upper bound, full-dimensional boundary corollary, and boundary nullity corollary are derived.
- `NashWhitney.lean`: single-set stratification and simultaneous set/frontier refinement are derived.
- `SardTranslation.lean`: nullity, almost-everywhere transversality, and the final existence corollary are derived from upstream statements.
- Added concise source comments identifying the missing foundational proof ingredients.
- Verification: LSP reported no errors; targeted `lake build CausalSmith.Substrate.SemialgebraicStratificationSard.SardTranslation` succeeded with 12 `sorry` warnings.
- Causalean search, Mathlib LeanSearch/local search, and bounded source grep found no reusable real-semialgebraic, real-closed-field quantifier-elimination, Nash/Whitney-stratification, or semialgebraic Sard implementation. Mathlib only offers adjacent smooth-manifold, Jacobian-nullity, Hausdorff-dimension, and Presburger-semilinear results.
- Fetched the Springer primary-source chapters. Their abstracts confirm projection stability and dimension theory in Chapter 2, and semialgebraic Sard plus Whitney conditions in Chapter 9.

## Remaining
- `Basic.lean`: `isSemialgebraic_coordinateProjection`.
- `DimensionBoundary.lean`: `semialgebraicDim_eq_ambient_iff`, `semialgebraicDim_frontier_lt_ambient`, `volume_eq_zero_of_semialgebraicDim_lt_ambient`.
- `NashWhitney.lean`: `isNashManifold_univ`, `IsNashManifold.semialgebraicDim_eq`, `exists_compatible_nashWhitneyStratification`.
- `SardTranslation.lean`: `nash_sard`, `IsNashManifold.coordinateProduct`, `subtraction_isNashMap`, `exceptionalTranslations_eq_iUnion_criticalValues`, `exceptionalTranslations_semialgebraic_dim_lt`.

## Blocked
- Projection requires a new axiom-free real-closed-field quantifier-elimination development.
- Boundary dimension and dimension-to-nullity require semialgebraic cell decomposition and its dimension/measure theory.
- Finite compatible Whitney/Nash stratification and semialgebraic Sard require substantial additional Nash geometry and rank-stratification infrastructure.
- These are the principal theorems of multiple book chapters, not proof gaps bridgeable from the available Mathlib/Causalean primitives within the remaining substrate rounds.

## Decisions
- Retain the quantifier-free predicate; redefining semialgebraicity as projection-closed would hide Tarski–Seidenberg and violate the API contract.
- Retain ambient frontier dimension drop; unrestricted `dim (frontier s) < dim s` is false for lower-dimensional closed sets.
- Retain explicit Nash charts and curve-based tangent vectors; no paper-specific assumptions or placeholders were introduced.
- Do not dispatch another filler: closing only downstream consequences cannot remove their foundational dependency, while assigning Tarski–Seidenberg alone would amount to requesting an entire missing quantifier-elimination library.