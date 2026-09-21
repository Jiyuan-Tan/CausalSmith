## Done
- Created `Basic.lean`, `AlmostSure.lean`, `Main.lean`, and the directory barrel.
- Added totalized bootstrap/empirical/sampling laws, exact positive-size bridges, a.s. variance/Lindeberg statements, general `ψ` headlines, and real-data specializations.
- Reused the promoted Efron-resampling, triangular-array CLT, Pólya/CDF, strong-law, and Mathlib CLT APIs.
- Fetched Bickel–Freedman (1981), Theorem 2.1; the scaffold formalizes its equal-size diagonal `m = n` required here.
- `lake build CausalSmith.Substrate.EfronBootstrapMeanClt` succeeds; LSP diagnostics report only the 21 intended `sorry` warnings.

## Remaining
- `Basic.lean` (9): `centeredBootstrapSum_eq_sqrt_mul_finAverage_sub`, `measurable_centeredBootstrapSum`, `centeredEmpiricalLaw_isProbabilityMeasure`, `integral_id_centeredEmpiricalLaw`, `memLp_id_centeredEmpiricalLaw`, `integral_sq_centeredEmpiricalLaw_eq_empiricalVar`, `setIntegral_sq_centeredEmpiricalLaw_eq_average`, `bootstrapMeanLaw_toMeasure`, `bootstrapMeanLaw_eq_iidRowNormalizedSumLaw`.
- `AlmostSure.lean` (7): `integral_squaredTail_tendsto_zero`, the three SLLN lemmas, `empiricalVar_tendsto_ae`, `centeredEmpiricalSecondMoment_tendsto_ae`, `centeredEmpiricalLindeberg_tendsto_ae`.
- `Main.lean` (5): sampling CLT, bootstrap CLT, Kolmogorov consistency, and two real-data specializations.

## Blocked
- None.

## Decisions
- Totalize row and bootstrap laws at `n = 0` by `δ₀`; positive-size bridge lemmas expose the literal Efron law, so the at-top results exactly cover `n ≥ 1`.
- Use `populationVariance ψ P := (Var_P ψ).toNNReal`, matching `gaussianReal`; no redundant probability-law typeclass is exposed in headline hypotheses because an `IIDSample` supplies it.
- Keep the measurable-space `ψ` theorem primary and derive real observations with `ψ = id`.
- Search found no existing headline theorem. LeanSearch identified tail-integral/DCT infrastructure; local MCP search failed because its service PATH lacked `rg`, so declarations were checked directly with repository `rg`, source inspection, and Loogle.