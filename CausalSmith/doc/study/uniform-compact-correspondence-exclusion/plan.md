## Done
- `Core.lean`: all nine theorems are proved, including far-set closedness/compactness, attained positive minimum, dichotomy, explicit attainment, and both uniform exclusion forms.
- `Matrix.lean`: both Euclidean operator-norm square-matrix specializations are proved.
- `Main.lean`: exports the complete substrate.
- Audited the canonical `Causalean.Discovery.LinearDisentanglement.Quantitative.CompactExclusion` source and searched Causalean/Mathlib; the implementation reuses `IsCompact.exists_isMinOn`.
- Fresh full project build (3798 jobs), targeted umbrella build, direct elaboration of all three source files, and Lean-LSP diagnostics all succeed with zero errors.
- Source scan finds no `sorry`, `admit`, or `axiom`; all eleven theorem axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Parameters are represented by the projection of compact `K`; no separate compact parameter domain is required.
- Reference membership in `K` is omitted because it is mathematically unnecessary: feasible zero uniqueness and positive `ρ` already exclude zero residual on the far set.
- The explicit-closedness core supports pseudometric candidate spaces; continuity-derived closedness uses `T2Space P` and `MetricSpace X`.
- The matrix API uses Mathlib's scoped `Matrix.Norms.L2Operator` metric and exposes the consumer conclusion as `‖B - B₀ p‖ < ρ p`.
- No filler subagents are needed because the verified module has no open proofs.