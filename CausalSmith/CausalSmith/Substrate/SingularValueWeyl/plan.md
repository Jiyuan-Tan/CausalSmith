## Done
- `TailSubspace.lean`: proved `exists_large_subspace_norm_le_singularValues` for every in-range index via the tail of Mathlib's ordered eigenbasis.
- `Comparison.lean`: proved `singularValues_le_of_large_subspace` from a codimension bound via a nonzero intersection with the leading singular subspace.
- `Main.lean`: proved `singularValues_add_le_add_opNorm`, the two-sided `abs_singularValues_add_sub_singularValues_le_opNorm`, and the literal-norm `ContinuousLinearMap.abs_singularValues_add_sub_singularValues_le`, all for rectangular maps and every natural index (including zero extension).
- Ground-truth verification this round: direct `lake env lean` elaboration of all three source files and `lake build CausalSmith.Substrate.SingularValueWeyl.Main` succeeded; source scan found no `sorry`, `admit`, or `axiom`; `#print axioms` for all five declarations reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Causalean index search and Mathlib LeanSearch found no existing indexed singular-value perturbation theorem to reuse.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Use complementary min--max support lemmas rather than Hermitian dilation; this handles rectangular maps and rank-deficient/zero singular values directly.
- Express codimension as `finrank V ≤ finrank S + j`; this is sufficient for the intersection argument without quotient bookkeeping.
- Plain `LinearMap` has no norm instance, so its API uses `‖D.toContinuousLinearMap‖`; the immediate continuous-linear-map wrapper exposes literal `‖D‖` as required.
- Mirsky's 1960 primary paper (QJM 11, 50--59, DOI 10.1093/qmath/11.1.50) was located, but the publisher PDF endpoint remains inaccessible with HTTP 403; accessible references confirm the same all-index operator-norm inequality.
