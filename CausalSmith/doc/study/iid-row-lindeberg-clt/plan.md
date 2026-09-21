## Done
- `Basic.lean`: row-sum/normalized-law definitions, measurability, and `charFun_iidRowSumLaw` are closed.
- `Scaled.lean`: both scaled CLT API declarations are closed via Lévy continuity and the isolated characteristic-function core; the uniform statement includes `σ2 = 0`.
- Added focused `CharacteristicFunction.lean` and `Scaling.lean`; wired the directory barrel.
- Reused Mathlib’s `charFun_map_sum_pi_eq_prod`, Lévy theorem, and Causalean’s quadratic exponential-remainder bound. Billingsley Thm. 27.2 was fetched and confirms changing row probability spaces are allowed.
- Verified `lake build CausalSmith.Substrate.IidRowLindebergClt`: succeeds with only seven `sorry` warnings.

## Remaining
- `Basic.lean`: `iidRowSumLaw_scaledRowMeasure_eq_normalized`.
- `CharacteristicFunction.lean`: `charFun_pow_tendsto_gaussian`.
- `Scaling.lean`: four pushforward moment/tail lemmas.
- `Unscaled.lean`: `iidRowNormalizedSumLaw_tendsto_gaussian`.

## Blocked
- None.

## Decisions
- Laws are exposed directly as `ProbabilityMeasure ℝ`; `NNReal` is the type denoted by the requested `ℝ≥0`.
- Use the characteristic-function route instead of constructing product filtrations and conditional expectations for the martingale-array CLT.
- The analytic core is uniform in the limiting variance, so `σ2 = 0` yields `gaussianReal 0 0 = dirac 0` without extra moments.
- The unscaled theorem is derived by pushing each row law through `x ↦ x / √n`; identities requiring `n ≠ 0` are used only eventually.