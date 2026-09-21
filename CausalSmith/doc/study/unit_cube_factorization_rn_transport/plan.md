## Done
- Ground-truth check: all declarations in `Substrate/UnitCubeFactorizationRnTransport/{Clamp,ReferenceMeasure,Factorization,RnTransport}.lean` compile and are sorry-free, with no `admit` or declared `axiom`.
- Added the paper-local construction chain in `Helpers/FiniteDensityBridge.lean`: closed `mechanismUnitCubeFactorization`, `mechanismInterventionDensity`, `mechanismRatioNumerator`, and `measurable_mechanismTargetRatio` using the substrate.
- Replaced the `ratio_nonancestor_zero` sorry with construction of `finiteDensityObservedWorldBridge_of_assumptions` and application of `FiniteDensityObservedWorldBridge.ratioLaw_eq_of_nonancestor`; no bridge premise was added and `simultaneous_confidence_edges` was unchanged.
- Library search and primary Mathlib-source inspection reconfirmed `Factorization.targetRatio_map_eq`, `Measure.restrict_pi_pi`, `withDensity_absolutelyContinuous'`, and `MeasurableEmbedding.rnDeriv_map` as the intended primitives.
- Targeted builds of the substrate umbrella, bridge helper, and `TExactRatioDecoder` succeed with sorry warnings only.

## Remaining
- `Helpers/FiniteDensityBridge.lean`: 6 holes in 5 declarations—observational/intervention measure identifications, `mechanismTargetRatio_toReal_eq`, observed intervention absolute continuity, and both identification fields of `finiteDensityObservedWorldBridge_of_assumptions`.
- `TExactRatioDecoder.lean`: `exact_ratio_decoder` retains its unrelated pre-existing sorry; `ratio_nonancestor_zero` is closed modulo the bridge construction.

## Blocked
- None. The bridge obligations form one dependency-coupled paper-local proof chain over the closed substrate.

## Decisions
- Keep reusable support/clamp/RN results in the substrate; keep `Mechanism`/`ObservedWorld` adaptation paper-local, with imports flowing only from the paper helper to the substrate.
- Use clamped `q` as the globally measurable numerator and recover the original `q/p` on the cube.
- Isolate observed-law absolute continuity before the ratio-law identifications so observational a.e. RN equality transfers to intervention environments without strengthening assumptions.
- Use one filler because all holes are in one module and the final identification fields depend on the earlier measure, ratio, and absolute-continuity lemmas.