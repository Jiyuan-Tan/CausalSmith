## Done
- `Basic.lean`: slice types, inclusion filtration, cardinality, uniform inner product/mean, and top-degree spanning; zero source sorries.
- `Harmonics.lean`: canonical harmonic layers/projections, projection properties, orthogonality, degree-zero mean, and full/centered decompositions; zero source sorries.
- `Kneser.lean`: inclusion-monomial action, inclusion–exclusion triangularity, filtration preservation, lower-filtration residual, self-adjointness, `kneserAdjacency_eigen`, and `kneserAdjacency_harmonicProjection` are proved.
- Ground truth: direct `lake env lean .../Kneser.lean` succeeds with no errors; exactly three source sorries remain.
- Re-fetched arXiv:1709.09011 source; its Kneser eigenvalue is `(-1)^k * choose (n-M-k) (M-k)`, matching the API.

## Remaining
- `Kneser.lean`: `normalizedKneser_eigenvalue_eq`.
- `Kneser.lean`: `normalizedKneserAdjacency_eigen` and `normalizedKneserAdjacency_harmonicProjection`.

## Blocked
- None.

## Decisions
- Use one filler for the three tightly coupled normalization declarations in the same file; parallel edits would conflict, while the final two results are immediate corollaries of the first.
- Causalean search found no reusable normalization theorem. Mathlib search confirmed `Nat.descFactorial_eq_factorial_mul_choose` and `Nat.choose_eq_descFactorial_div_factorial` as the relevant algebraic building blocks.
- Keep the existing general statements unchanged: `2*M ≤ n` implies all required binomial and falling-factorial denominators are nonzero.