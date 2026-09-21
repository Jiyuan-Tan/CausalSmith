## Done
- Ground truth: `lake build CausalSmith.Substrate.FiniteSideInformationMinimaxConvergence` succeeds (3179 jobs; warnings only).
- Source scan finds exactly 3 `sorry`s, all in `SimplexSpecialization.lean`; no `admit` or custom `axiom` occurs in the substrate tree.
- `Coordinates.lean`, `Risk.lean`, `Selector.lean`, `Experiments.lean`, `Concentration.lean`, `Fiber.lean`, `Comparison.lean`, `Approximation.lean`, and `Main.lean` are closed.
- `finiteSideInfo_minimax_tendsto` is proved; verification reports only standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- LSP reports no errors in `SimplexSpecialization.lean`, only its three `sorry` warnings and a linter warning.
- Library/Mathlib search found `IsClosed.isCompact`, `continuous_subtype_val`, and `isCompact_iff_compactSpace`; a standalone LSP snippet confirmed direct proofs of all three remaining declarations compile.

## Remaining
- `SimplexSpecialization.lean` (3): `isCompact_closed_finitePmf`, `continuous_closed_finitePmf_coordinate`, `closedSimplex_finiteSideInfo_minimax_tendsto`.

## Blocked
- None.

## Decisions
- Preserve all current statements and the clean paper-independent dependency chain.
- Use one filler for the final three declarations because they occupy one small file and form a single import-coupled specialization layer.
- Use compact-subtype instances via `isCompact_iff_compactSpace` and nonemptiness via `Set.Nonempty.to_subtype`, then apply the general convergence theorem.
- No primary paper is named; the requirement cites standard decision theory, so source fetching is inapplicable.