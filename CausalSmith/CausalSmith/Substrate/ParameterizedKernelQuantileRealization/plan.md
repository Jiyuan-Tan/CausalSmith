## Done
- `Basic.lean`: `SupportedOnUnitInterval`, `kernelUnitQuantile`, `quantileRealization`, and pointwise `quantileRealization_mem_unitInterval` are closed.
- `Measurability.lean`: joint measurability, the real wrapper, and measurable sections are closed.
- `Law.lean`: `map_kernelUnitQuantile`, `map_quantileRealization`, and `ae_quantileRealization_mem_unitInterval` are closed.
- Round 3 forced source compilation and LSP diagnostics both succeed with no warnings or errors; the source scan finds no `sorry`, `admit`, or `axiom`.
- Axiom audit of every public declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Project search confirms Mathlib's kernel representation construction and Causalean's fixed-measure `quantile_map_uniform`; Kallenberg Lemma 4.22 was fetched and matches the measurable rational-supremum construction and CDF law.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Use Kallenberg's explicit `sSup {x ∈ [0,1] | κ_s([0,x]) < u}` rather than an existential selector; this gives a pointwise faithful carrier.
- Expose a subtype-valued core and a jointly measurable real wrapper using `Set.projIcc`; state the requested canonical law with `volume.restrict (Set.Icc 0 1)`.
- The law is proved directly by `Measure.ext_of_Iic`, splitting thresholds below, inside, and above `[0,1]`; the real-line law is the measure-preserving coercion corollary.
- The completed API is genuine and non-vacuous: the only substantive assumption is the requested fiberwise support equality, and range is pointwise stronger than almost sure.
