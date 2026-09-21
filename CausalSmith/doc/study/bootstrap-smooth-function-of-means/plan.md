## Done
- Ground truth verified: `lake build CausalSmith.Substrate.BootstrapSmoothFunctionOfMeans` succeeds (3314 jobs), with zero `sorry`, `admit`, or `axiom` declarations.
- All public theorems pass the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.
- Split `smoothRemainder_isLittleO` into `SmoothRemainder.lean`; every substrate file is now below 600 lines (`Linearization.lean` is 574).
- Added the new module to the directory barrel and added 1–3 crosslinked headline declarations per theorem-bearing file to `doc/library_review/Stat.json`; JSON validation succeeds.
- Restored the corrected exact Chebyshev API: `bootstrapMean_chebyshev` and `bootstrapMeanVec_coordinate_chebyshev` require `n ≠ 0`.
- Reused `Tendsto_inProb.of_isLittleOp_one` after the required Causalean search instead of retaining the duplicate local proof.
- Fetched the [Bickel–Freedman primary article](https://projecteuclid.org/journals/annals-of-statistics/volume-9/issue-6/Some-Asymptotic-Theory-for-the-Bootstrap/10.1214/aos/1176345637.full).

## Remaining
- None.

## Blocked
- None.

## Decisions
- The reviewer’s request to totalize the Chebyshev bound at `n = 0` is stale relative to the explicit 2026-09-17 correction; the substrate does not manufacture an empty-sample bootstrap law.
- Preserve all estimator, measurability, moment, differentiability, and positive-variance hypotheses unchanged.
- Ready for review: the module is complete, non-vacuous, under the file-size limit, documented, and fully verified.