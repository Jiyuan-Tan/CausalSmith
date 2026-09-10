## Done
- `Deterministic.lean`: proved `entrywise_to_quadratic`, `entrywise_gram_lower_bound`, `localizedGram_good_of_entrywise`, and `localizedGram_failure_subset_deviations`.
- `BernsteinUnion.lean`: proved coordinate-dependent `iid_sum_bernstein_union_bound` under `Measure.pi`.
- `LocalizedMoments.lean`: proved all six bounded-weight/feature integrability, centered-envelope, and order-`p` second-moment lemmas.
- `LocalizedGram.lean`: proved `localized_empiricalGram_coercive_of_pos` and `localized_empiricalGram_coercive` with the explicit `N * p` rate.
- Ground-truth verification this round: LSP reports no diagnostics; direct `lake env lean` elaboration of every module succeeds; source grep finds no `sorry`, `admit`, or `axiom`; `#print axioms` for all 13 theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Re-ran Causalean and Mathlib searches. Reused inputs remain `bernstein_abs_ge` and finite-product transport; the existing family/matrix result is Chebyshev-based. Mathlib has `measureReal_iUnion_fintype_le`, though the established proof's explicit transported union argument is already closed.
- Re-fetched the named OUP primary source: the book and Basic Inequalities chapter metadata are accessible, but theorem text remains behind institutional access.

## Remaining
- None; the API contract and all supporting lemmas are proved.

## Blocked
- None.

## Decisions
- Use real-valued measure (`Measure.real`) to match existing scalar Bernstein and keep the finite union bound algebra in `ℝ`.
- Use count threshold `Np/2` and entry threshold `λNp/(4d)`; these yield positivity and the exact realized-count coercivity factor `λ/2`.
- The common rate is `min (1/20) (λ² / (16 d (4 d B⁴ + B² λ)))`; the prefactor `2(1+d²)` absorbs `p = 0` without adding a small-`Np` premise.
- The finite coordinate type is `Option (κ × κ)`, jointly controlling the count and all `d²` Gram entries under the same product law.
- No filler dispatch is needed: ground truth is fully proved and ready for review.
