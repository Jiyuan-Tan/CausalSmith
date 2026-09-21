## Done
- Ground-truth audit found one focused 694-line module, `Main.lean`, with no `sorry`, `admit`, or declared `axiom`.
- The module provides all requested measurability APIs, the one-mark conditional Hoeffding lemma, kernel-native and observation-law product MGF bounds, the retained-design product factorization, and both exact two-sided tail bounds.
- `product_observation_law_map_design_outcome` derives the full-design conditional product kernel from the i.i.d. observation law; conditional independence is not assumed.
- Fresh `lake env lean CausalSmith/Substrate/RandomDesignWeightedHoeffding/Main.lean` and `lake build CausalSmith.Substrate.RandomDesignWeightedHoeffding.Main` both exited 0 with lint warnings only.
- Axiom audits for all six substantive public theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
- Re-searched Causalean for conditional Hoeffding, finite-product sub-Gaussian, and attached-kernel tail APIs; the implementation reuses the relevant existing concentration and transport results.
- Verified Hoeffding’s 1963 canonical citation and DOI metadata; publisher/JSTOR full-text endpoints were access-challenged. The implemented normalization is the standard `exp(s²(b-a)²/8)` lemma, yielding proxy `∑wᵢ²/4` and tail `2 exp(-2t²)`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Preserve arbitrary measurable design spaces, jointly full-design-dependent weights, the exact `1/4` proxy, exact `2 * exp (-2 * t^2)` bound, and the almost-sure positive-energy premise.
- Keep the kernel-native theorem together with the conditional-expectation/disintegration corollary and explicit observation-law factorization.
- Keep the single module: its definitions, factorization, MGF, and tail arguments form one coupled proof chain and remain below the 900-line split threshold.
- No filler subagent is needed; the dependency-clean module is fully proved and ready for review.