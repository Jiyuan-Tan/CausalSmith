## Done
- Ground truth confirms `Basic.lean`, `Conditioning.lean`, `Pencil.lean`, `SpectralMatching.lean`, `Projectors.lean`, and `Recovery.lean` contain no placeholders.
- Fresh LSP diagnostics, direct Lean checking, and the targeted umbrella build succeed; only the two declared `Main.lean` sorry warnings remain.
- Representative contraction, conditioning, pencil, projector, and recovery theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Library search recovered the existing singular-value infrastructure and Mathlib `stdOrthonormalBasis`; Goyal–Vempala–Xiao arXiv:1306.5825 was re-fetched as LaTeX and confirms the nonnormal Bauer–Fike/robust-pencil design.
- Added a dependency-ordered proof roadmap beside the final theorem without changing its API.

## Remaining
- `Main.lean` (2): `localInverse_constants_pos`, `exists_permutation_factorMatrix_frobeniusNorm_le`.

## Blocked
- No external blocker. The headline proof must construct an orthonormal compression of the lifted range and assemble the already-proved quantitative chain.

## Decisions
- Preserve every hypothesis, conclusion, explicit constant, both spectral gaps, and the nonnormal diagonalizable-pencil contract.
- Use `stdOrthonormalBasis` on the lifted range subtype, reindexed through the finrank equality obtained from lifted injectivity.
- Dispatch one filler because both remaining declarations share `Main.lean` and the same import closure; parallel edits/builds would be unsafe.
- Permit private helpers only inside `Main.lean`; do not import research or paper modules.