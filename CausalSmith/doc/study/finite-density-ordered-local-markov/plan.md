## Done
- Ground truth: targeted build, direct `lake env lean` compile, and LSP diagnostics all succeed with no errors; exactly one source `sorry` remains in `Main.lean`.
- `Coordinates.lean`, `FiniteMeasure.lean`, `ThreeBlock.lean`, and `Local.lean` are closed; in particular `Factorization.localMarkovParents_of_parentClosed` is proved.
- `Main.lean` wrappers and the direct `UnitCubeFactorization` specialization compile modulo the single superset theorem.
- Library search found `Causalean.condIndep_valuesProjection_weak_union` and `condIndepFun_weak_union_of_prodMk`; the former is an exact template for the remaining projection/sigma-algebra transport.
- Evans, Chapter 6 §6.1–6.2 confirms the ordered Markov statement and that factorization implies it without positivity: https://www.stats.ox.ac.uk/~evans/gms/_book/dag.html

## Remaining
- `Main.lean`: prove `Factorization.localMarkovSuperset_of_parentClosed` (the only source placeholder).
- After closure: rebuild from source, scan the full substrate tree for proof placeholders, and audit axioms of all central declarations.

## Blocked
- None.

## Decisions
- Use one filler because the only open obligation is one tightly coupled weak-union/projection-transport proof.
- Set `C := G.parents i`, `Y := P \ A`, and `W := A \ C`; use `Y ∪ W = P \ C` and `C ∪ W = A`.
- Derive the result from `localMarkovParents_of_parentClosed` via `CondIndepFun.comp`, `condIndepFun_weak_union_of_prodMk`, and equality of the joined coordinate comaps with the comap of projection to `A`.
- Keep the general standard-Borel, sigma-finite API unchanged; add no positivity, inhabitation, paper-specific premise, or forbidden import.