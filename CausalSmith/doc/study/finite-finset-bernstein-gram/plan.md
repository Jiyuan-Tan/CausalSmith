## Done
- `Deterministic.lean`: proved all four deterministic perturbation and failure-event inclusion results.
- `BernsteinUnion.lean`: proved coordinate-dependent `iid_sum_bernstein_union_bound` under `Measure.pi`.
- `LocalizedMoments.lean`: proved all six bounded-weight/feature integrability, envelope, and order-`p` moment lemmas.
- `LocalizedGram.lean`: proved `localized_empiricalGram_coercive_of_pos` and `localized_empiricalGram_coercive` with the explicit `N * p` rate.
- Ground-truth verification this round: LSP reports no diagnostics; direct `lake env lean` elaboration of every module succeeds; source grep finds no `sorry`, `admit`, or `axiom`; `#print axioms` for all 13 theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Re-ran Causalean and Mathlib searches. Reused inputs remain `bernstein_abs_ge` and finite-product transport; the existing family/matrix result is Chebyshev-based.
- Re-fetched the named OUP primary source; metadata is accessible, but theorem text remains behind institutional access.

## Remaining
- None; the API contract and all supporting lemmas are proved.

## Blocked
- None.

## Decisions
- Use `Measure.real` to match scalar Bernstein and keep union-bound algebra in `ℝ`.
- Use count threshold `Np/2` and entry threshold `λNp/(4d)`, yielding positive realized count and coercivity factor `λ/2`.
- Use rate `min (1/20) (λ² / (16 d (4 d B⁴ + B² λ)))` and prefactor `2(1+d²)`; the latter absorbs `p = 0` without a small-`Np` premise.
- Use coordinate type `Option (κ × κ)` to control the count and all `d²` Gram entries jointly.
- No filler dispatch is needed; ground truth is fully proved and ready for review.