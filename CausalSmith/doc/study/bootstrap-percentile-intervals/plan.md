## Done
- Ground truth verified this round: `lake build CausalSmith.Substrate.BootstrapPercentileIntervals` succeeds (`3294 jobs`, exit 0) with exactly 5 study-local `sorry`s and no hard errors.
- `Basic.lean` is complete: public statistics/laws/quantiles/CIs, `BootstrapAsymLinear`, event measurability, law identities, and the `IsAsymLinear` bridge.
- `LimitLemmas.lean` is complete: Kolmogorov triangle/conditional Slutsky, random-quantile convergence, random-endpoint coverage, and Gaussian interval masses.
- `Main.lean`: `sampling_tendsto_gaussian` and `bootstrap_tendsto_gaussian` are proved.
- Reuse search reconfirmed the Causalean quantile/Gaussian APIs and Mathlib convergence-in-measure/integrability infrastructure. Horowitz’s primary manuscript was fetched; Section 2 grounds uniform-CDF bootstrap consistency and the confidence-interval interpretation.

## Remaining
- `Main.lean` (4): `consistent`, `quantile_tendsto`, `percentileCI_coverage`, `basicCI_coverage`.
- `SampleMean.lean` (1): `BootstrapAsymLinear.sampleMean`.

## Blocked
- None. The dependency order is consistency/quantiles → coverage; the sample-mean constructor is file-independent and can be developed concurrently.

## Decisions
- Preserve every public statement and hypothesis; add no assumptions or weakened variants.
- Use one filler for all four same-file `Main.lean` conclusions to avoid overlapping edits, and a second filler for the independent `SampleMean.lean` constructor.
- The Lean LSP local-search helper still fails because `rg` is absent from its tool PATH; direct project `rg`, Causalean search, LeanSearch, and source inspection were used instead.
- No new helper scaffold is needed: the required generic limit and measurability lemmas are already closed in lower layers.