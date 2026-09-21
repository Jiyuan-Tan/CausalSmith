## Done
- Closed `Basic.lean`: affine evaluation/continuity, strict-to-weak inclusion, and weak-cell closedness/convexity.
- Closed `Closure.lean`: segment feasibility, sequential approximation, and `closure_strictCell_eq_weakCell`.
- Closed `CommonSlack.lean`: bounded common slack, witness conversions, supremum argument, feasibility equivalence, and empty-system edge case.
- Closed `Polynomial.lean`: checked degree-≤1 compilation and exact strict/weak cell preservation.
- Closed `Extrema.lean`: image-closure equality, boundedness transfer, generic `sInf`/`sSup` equality, and affine specializations.
- Round-6 ground truth: direct `lake env lean` checks pass for every module; exactly four source `sorry`s remain, all in `Example.lean`.
- Searched Causalean and Mathlib first; no reusable affine-cell example API appeared. No specific primary source was named.

## Remaining
- `Example.lean` (4): `mem_strictCell_mixedExample`, `mem_weakCell_mixedExample`, `half_mem_strictCell_mixedExample`, and `closure_strictCell_mixedExample`.

## Blocked
- None.

## Decisions
- Retain coefficient-vector affine functions, list-marked constraints, bounded common slack, continuous-objective extrema, and checked polynomial compilation.
- Use one filler for the tightly coupled elementary example cluster; derive closure from the midpoint witness and the generic closure theorem.