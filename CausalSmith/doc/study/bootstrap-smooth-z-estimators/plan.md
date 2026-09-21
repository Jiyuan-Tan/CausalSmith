## Done
- Ground truth verified: `lake build CausalSmith.Substrate.BootstrapSmoothZEstimators` completed all 3340 jobs with no errors and exactly six local `sorry`s; Lean LSP diagnostics agree.
- `Basic.lean`, `SamplingLinearization.lean`, `BootstrapLinearization.lean`, and `Main.lean` are closed. This includes both vector linearizations, `BootstrapAsymLinear.zEstimator`, and percentile/basic coverage.
- Axiom audits for the sampling linearization, bootstrap linearization, and main constructor report only `propext`, `Classical.choice`, and `Quot.sound`.
- Reuse searches confirmed the OLS consistency/singularity/normal-equation API and `feasibleGMM_asymLinear_of_smoothMoment_of_sampleFn`; Mathlib supplies finite-sum measurability and matrix-inverse measurability infrastructure.
- Re-fetched Newey--McFadden Theorem 3.1 and its proof; its Taylor expansion, Jacobian convergence, inversion, and asymptotic-linear representation match the implemented substrate.

## Remaining
- `OLS.lean` (4): `measurable_olsSampleEstimator`, `olsSampleEstimator_sampleVector`, `olsSampleEstimator_solvesInProbability`, `BootstrapAsymLinear.olsContrast`.
- `FeasibleGMM.lean` (2): `feasibleGMM_bootstrapLinearization_of_smoothMoment`, `BootstrapAsymLinear.feasibleGMM`.

## Blocked
- None. The feasible-GMM conditional expansion is the sole research-scale remaining proof and has not yet had a failed filler attempt.

## Decisions
- Use two fillers, partitioned by file to avoid concurrent edit conflicts.
- Preserve every current theorem statement and bundled hypothesis; add no Donsker/equicontinuity or extra measurability assumptions.
- OLS should reuse existing Causalean consistency, singular-Gram probability, normal-equation, smooth-regularity, and influence-identification results.
- Feasible GMM should combine the existing data-side theorem with a conditional adaptation of its deterministic absorption argument, using the already-proved bootstrap weak-law/tightness machinery.