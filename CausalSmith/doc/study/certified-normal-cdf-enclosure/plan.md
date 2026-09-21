## Done
- `Basic.lean`, `PowerSeries.lean`, `Normalization.lean`, `Exponential.lean`, and `Checker.lean` are proof-complete.
- `Tail.lean`: Mills inequalities, density enclosure, and `millsTailInterval_sound` are closed.
- Reuse searches confirmed the local symmetry, interval-composition, Gaussian-integral, normalization, and exponential APIs. Primary references checked: [NIST DLMF §7.6](https://dlmf.nist.gov/7.6) and [§7.8](https://dlmf.nist.gov/7.8).
- Ground truth: the top-level build succeeds (3135 jobs); direct Lean checks of `Central.lean` and `Tail.lean` succeed with exactly one `sorry` warning each.

## Remaining
- `Central.lean`: `centralCheck_sound`.
- `Tail.lean`: `tailCheck_sound`.

## Blocked
- None.

## Decisions
- Preserve the genuine rational certificate API, exact cutoff/range/width checks, symmetry transport, and checked normalization/exponential subcertificates.
- Dispatch two independent fillers, one per remaining file; no further decomposition is warranted because each obligation is a direct composition of already-proven lowest-layer lemmas.
- Do not import research/staging modules or alter definitions and theorem statements.