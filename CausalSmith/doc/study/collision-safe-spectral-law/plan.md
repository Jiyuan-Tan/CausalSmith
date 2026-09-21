## Done
- Ground-truth audit found five substrate modules and zero `sorry`, `admit`, `axiom`, or unsafe shortcuts.
- `Basic.lean` and `MoorePenrose.lean` provide the rectangular carrier, canonical Moore–Penrose inverse, Penrose projections, moving-range identity, symmetric max-norm bound, and singular-margin specialization.
- `FunctionalCalculus.lean` provides basis-independent aggregate projectors, collision cancellation, divided differences for unrelated diagonalizers, dimension-squared stability, spectrum bounds, and anchor perturbation estimates.
- `AtomicWasserstein.lean` provides primal attainment, monotone/CDF equality, exact KR duality, an attaining normalized one-Lipschitz potential, the direct dual-bound corollary, and measure-extensional invariance.
- `Composition.lean` closes `atomicW1_le_operator_anchor_perturbation` without eigengaps, matching eigenbases, or diagonalizer perturbation assumptions.
- Fresh direct `lake env lean` checks passed for all five files; full `lake build` passed (3798 jobs).
- Public-endpoint `#print axioms` audit reported only `propext`, `Classical.choice`, and `Quot.sound`; the temporary audit file was removed.
- Dependency and forbidden-name scans are clean. Imports are only Mathlib and this substrate tree.
- Library searches found no reusable exact endpoints. Vallander’s primary archive confirms the real-line W1/CDF identity; Wedin’s 1973 primary bibliographic record matches the pseudoinverse perturbation target.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Submit for review with zero filler agents because the source is fully proved and freshly verified.
- Retain the equal-rank hypothesis on `moorePenrose_sub_eq` as the requested perturbative API, although its algebraic identity is valid without using that hypothesis.
- Preserve arbitrary finite slot types, zero-weight compatibility, moving row/column spaces, unrelated diagonalizers, repeated eigenvalues, and normalized attained KR potential composition.