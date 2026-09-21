## Done
- Added `Scalar.lean`: exact scalar checker plus rational scalar/vector/matrix certificate APIs.
- Added `ChunkedSum.lean`: bounded `CertifiedChunk`, disjoint-cover `ChunkedSumCertificate`, binary `IntervalFoldCertificate`, and chunked dot-product API.
- Added `Recurrence.lean`: coordinatewise and finite-trace certificates, `toFiniteIterateCertificate`, and stationary-reward adapters, including minorization.
- Reused existing `RatInterval`, `IntervalVector`, `IntervalMatrix`, `intervalDot`, `FiniteIterateCertificate`, and stationary soundness APIs. Library/Mathlib searches found `Finset.sum_union`-style results and `List.rel_sum`; no external primary source was named.
- `lake build CausalSmith.Substrate.ChunkedFiniteIntervalCertificates.Recurrence` succeeds with only the 15 intended `sorry` warnings. No forbidden evaluator or research-module import occurs.

## Remaining
- `Scalar.lean`: `scalarSubintervalCheck_sound`, `ScalarIntervalCertificate.sound`, `FiniteVectorCertificate.sound`, `FiniteMatrixCertificate.sound`.
- `ChunkedSum.lean`: `IntervalFoldCertificate.refines_sum`, `.contains_sum`, `listSum_subinterval`, `sum_eq_sum_chunks`, `ChunkedSumCertificate.sound`, `.contains`, `ChunkedDotCertificate.sound`, `.contains`.
- `Recurrence.lean`: `CoordinateRecurrenceCertificate.sound`, `ChunkedFiniteIterateCertificate.table_sound`, `.adapter_rows`.

## Blocked
- None.

## Decisions
- Numeric work is confined to bounded chunk leaves (`indices.card ≤ chunkSize`); chunk outputs are assembled through opaque binary-addition proofs rather than a global Boolean reduction.
- Chunks are a list of finite index sets with explicit pairwise-disjointness and coverage proofs, supporting arbitrary finite index types.
- The public adapter preserves the established finite-iterate interface instead of duplicating stationary semantics.
- Proof strategies are recorded beside each open theorem in the Lean files; statements must remain unchanged and non-vacuous.