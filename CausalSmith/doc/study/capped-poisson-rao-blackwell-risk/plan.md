## Done
- `PrefixLaw.lean`: all declarations closed, including capped-prefix measurability and `map_totalizedPrefix_restrict_nonoverflow`.
- `Tail.lean`: both quarter-mean overflow bounds are closed from `poisson_upper_bernstein`.
- `Risk.lean`: measurable construction, auxiliary Markov kernel/product law, kernel-mean integral characterization, restricted-risk bridges, general interval transfer, and unit-interval transfer are all closed.
- Fresh direct `lake env lean` checks pass for all three modules; Lean sources contain no `sorry`, `admit`, or `axiom`.
- `#print axioms` for headline law, tail, and risk theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Library searches reconfirmed reuse of `finitePoissonSampleLaw_restrict_count_eq`, `sqRisk_kernelMean_le_comp`, `poisson_upper_bernstein`, and Mathlib's regrouping/finite-sum variance APIs.

## Remaining
- None; ready for review/promotion.

## Blocked
- None.

## Decisions
- Keep visible overflow as `Unit ⊕ FiniteSample X`; totalization is used only under restricted measures.
- Retain `(fixed sample, count)` as the auxiliary-kernel output so existing kernel-mean Jensen contraction applies.
- Add no product-regrouping wrapper: `measurePreserving_arrowProdEquivProdArrow` and existing variance machinery already cover it.
- No primary paper was named; canonical local theorem sources and the public Poisson Bernstein implementation are the operative references.