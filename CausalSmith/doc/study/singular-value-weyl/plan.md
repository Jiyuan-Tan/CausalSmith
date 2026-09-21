## Done
- `TailSubspace.lean`: proved `exists_large_subspace_norm_le_singularValues` for every in-range index.
- `Comparison.lean`: proved `singularValues_le_of_large_subspace` using the leading singular subspace intersection argument.
- `Main.lean`: proved the one-sided and absolute Weyl bounds for rectangular linear maps and every natural index, plus the literal-norm continuous-linear-map wrapper.
- Direct elaboration of all three files and `lake build CausalSmith.Substrate.SingularValueWeyl.Main` succeeded.
- Source scan found no `sorry`, `admit`, or `axiom`. `#print axioms` for all five declarations reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Causalean search and Mathlib LeanSearch found no existing indexed singular-value perturbation theorem.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Use complementary min–max support lemmas, directly covering rectangular and rank-deficient maps.
- Express codimension as `finrank V ≤ finrank S + j`.
- Use `‖D.toContinuousLinearMap‖` for plain linear maps and expose literal `‖D‖` through the continuous-linear-map wrapper.
- Mirsky's 1960 primary paper was located, but its publisher PDF endpoint returned HTTP 403; accessible references confirm the same all-index operator-norm inequality.