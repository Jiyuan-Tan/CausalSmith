## Done
- Ground-truth audit of all five Lean files confirms the complete intended API: explicit ordered roots; algebraic top projector; orthogonal-projector/eigenvector-choice independence; Gram truncation and pseudoinverse bridges; all four Moore–Penrose equations; local C¹ results; and locally bounded Wald derivative.
- Causalean and Mathlib searches found no reusable existing projector/pseudoinverse substrate; confirmed relevant Mathlib calculus and Hermitian-matrix lemmas already used by the implementation.
- Direct `lake env lean` checks passed for every source file. Targeted `lake build CausalSmith.Substrate.RankOneSpectralProjectorSmoothness.Wald` completed successfully (2649 jobs), and LSP reports no errors or failed dependencies for `Wald.lean`.
- Source audit found zero `sorry`, `admit`, or new `axiom`. `#print axioms` on twelve representative/core theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Import audit confirms a clean paper-agnostic closure containing only Mathlib and modules within this substrate tree. No research module is imported.
- No primary source was fetched because the requirement names only standard textbook finite-dimensional spectral theory and Fréchet calculus, not a specific source.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Retain total ambient-space formulas for `lambda₁`, `lambda₂`, and `topProjector`, imposing symmetry only on spectral claims; this preserves an open strict-gap domain for calculus.
- Retain normalization as `dotProduct u u = 1` and validate the pseudoinverse formula through the full Moore–Penrose system.
- The statements are substantive and applicable to the intended `Fin 2` Gram baseline; no continuity of an eigenvector selector, strengthened paper assumption, or vacuous premise was introduced.
- Advance to review with no filler dispatch because the verified source has no remaining proof holes.