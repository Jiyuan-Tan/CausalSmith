## Done

- Ground-truth audit: `Main.lean` contains both required public APIs with complete proofs and no `sorry`, `admit`, or `axiom` declarations.
- Verification: direct `lake env lean CausalSmith/Substrate/MeasurableCompactArgminSelection/Main.lean` succeeds with zero errors; only two non-fatal `letI` style warnings remain.
- Axiom checks: both public theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `borelMeasurable_compact_argmin_selector`: constructs an exact measurable compact-action minimizer using dense approximants, measurable compact-fiber hit tests, a Cauchy sequence, and its measurable limit.
- `borelMeasurable_nearestPoint_selector`: provides a total measurable nearest-point rule with membership in `K` and exact equality to `Metric.infDist`.
- Library search found compact minimum-attainment and measurable-limit tools but no reusable general measurable-extrema selector; the Causalean hits were specialized selectors.
- Primary source rechecked: Brown--Purves (1973), Corollary 1 gives an exact Borel minimizer on the attainment set under σ-compact sections and lower-semicontinuous action sections; nonempty compact `K` and continuity make that set total here.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Preserve the faithful general API: standard-Borel parameter space, fixed nonempty compact finite-dimensional Euclidean action set, joint measurability, and continuous action sections.
- Keep the nearest-point result total and exact without uniqueness or convexity assumptions.
- Retain the local constructive proof because the available Mathlib/Causalean libraries do not expose the required general measurable selector.
- Send no filler subagents: the module is ready for review.