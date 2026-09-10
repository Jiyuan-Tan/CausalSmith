## Done

- `FinitePosterior.lean`: all declarations are proved, including guarded posterior normalization/safety, disintegration, numerator identity, exact square completion, posterior-mean optimality, the risk infimum, and finite-design Bayes-risk identification.
- `ContinuousMixture.lean`: all declarations are proved, including induced-design loss compatibility, mixed Bayes-risk identification, and explicit integrated-risk lower-bound transfers.
- Ground-truth verification: indexed-library search found and the module reuses `inducedFiniteDesign_expectedLoss_eq_mixedKernelLoss` and `realBayesRisk_eq_inducedFiniteDesignBayesRisk`; both source files pass direct `lake env lean`, and the targeted module build succeeds.
- Source audit finds no `sorry`, `admit`, `native_decide`, or custom `axiom`; headline `#print axioms` results contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Null-fiber posterior weights are zero; posterior normalization is restricted to positive fibers, with separate zero-fiber safety.
- Singleton kernel probabilities, risks, and infima stay in native `ℝ`; no `ENNReal` bridge is introduced.
- Observation-dependent targets use `t : S → X → ℝ`; `statewiseSquaredLoss` connects estimators to existing finite-design and mixture APIs.
- Continuous transfer keeps estimatorwise compatibility and lower-bound premises explicit. No concrete external primary source was named; canonical in-repository results were used.
