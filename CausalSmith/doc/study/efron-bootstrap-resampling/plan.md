## Done
- `Basic.lean`: empirical measure, resampling law, bootstrap law, and probability-measure results are closed.
- `FiniteRepresentation.lean`: atomic resampling representation and finite-average integration formula are closed.
- `Moments.lean`: both exact bootstrap mean/second-moment identities are closed.
- `Measurability.lean`: `bootstrapCDF_eq_average_indicators`, `measurable_bootstrapCDF`, and `bootstrapCDF_rightContinuous` are closed.
- Ground-truth build succeeds; exactly 4 substrate `sorry`s remain.
- Rechecked Causalean/Mathlib APIs and fetched Efron (1979); §2 supports the empirical-law/product-resampling design.

## Remaining
- `IIDSampleLink.lean`: `variance_empiricalMeasure_eq_empiricalVar`.
- `Measurability.lean`: `bootstrapLowerQuantile_eq_sInf_rat`, `bootstrapLowerQuantile_le_iff`, `measurable_bootstrapLowerQuantile`.

## Blocked
- None.

## Decisions
- Run two independent fillers, partitioned by file.
- Preserve the genuine endpoint `β = 1`; Causalean's existing quantile lemmas only cover `β < 1`, so finite bootstrap support must supply endpoint attainment.
- Keep all imports within Mathlib, Causalean, and this substrate tree.