## Done
- Added `ConditionalAverage.lean`: polynomial representation plus continuity/measurability API for `conditionalAverageProcedure`.
- Added `Extension.lean`: ambient exact-table procedures and continuous/measurable clipped-extension API.
- Added `FiniteProductIntegral.lean`: `finitePmfDesign`, `finitePmfMeasure`, product-measure and risk-integral API.
- Added `MinimaxComparison.lean`: measurable exact-table risk/value, surjective reindexing, minimax squeeze, and convergence-to-equality API.
- Added umbrella module `MeasurableFiniteSideInformationMinimaxBridge.lean`.
- Searched the Causalean index first; reused promoted finite-side-information modules, `FiniteDesign.toMeasure`, `prodDesign_toMeasure_eq_pi`, and the existing minimax order API.
- Verified `lake build CausalSmith.Substrate.MeasurableFiniteSideInformationMinimaxBridge`: succeeds with only `sorry`/lint warnings.

## Remaining
- `ConditionalAverage.lean`: 3 sorries — `eval_conditionalAveragePolynomial`, `continuous_conditionalAverageProcedure`, `measurable_conditionalAverageProcedure`.
- `Extension.lean`: 3 sorries — `exists_continuous_clippedExtension`, `exists_continuous_ambientExactSideProcedure`, `exists_measurable_clippedAmbientExactSideProcedure`.
- `FiniteProductIntegral.lean`: 5 sorries — the three PMF/product integral identities and two risk identities.
- `MinimaxComparison.lean`: 11 sorries — generic reindexing, three statistical reindexing identities, two comparison inequalities, two squeeze lemmas, and the tendsto equality.

## Blocked
- None.

## Decisions
- Ambient estimators are bounded maps on the full table `C → ℝ`; admissibility requires Borel measurability label-sectionwise. This matches the existing curried finite-label procedure API.
- Use interval-valued Tietze extension from the closed simplex, giving a continuous (hence measurable) clipped extension rather than a merely piecewise measurable one.
- Realize PMFs through Causalean finite designs; use `prodDesign_toMeasure_eq_pi` instead of rebuilding product-measure theory.
- Keep pure surjective minimax reindexing separate from continuity transport, with a compact continuous-surjection convenience squeeze.
- No uniquely identified primary source was named; the stated reference is the general finite-decision-theory toolkit rather than a fetchable paper.