## Done
- Proved `martingaleArrayCLT` and the characteristic-function core `martingaleArrayCharFun_tendsto`.
- Proved Lyapunov corollaries from conditional and unconditional fourth-moment sums, including deterministic predictable variance.
- Closed all supporting modules: `Basic`, `ExponentialBounds`, `ProbabilityBounds`, `Lyapunov`, `ConditionalTaylor`, `StoppedBudget`, `ConditionalTelescoping`, `GaussianBounds`, `PredictableVarianceBounds`, `RemainderBudget`, `StoppedArray`, `CompensatedStep`, and `CompensatedTelescoping`.
- Library and Mathlib searches found no existing martingale-array CLT; reused Mathlib conditional-expectation, characteristic-function, Gaussian, and Lévy infrastructure.
- Fresh arXiv LaTeX for Li–Zhao 2602.21998 confirms the normalized martingale-array variance/Lindeberg framework and Brown/Hall–Heyde references.
- Forced a fresh rebuild of every substrate module after removing their exact generated artifacts: `Main` built successfully with zero errors.
- LSP diagnostics are error-free. Source audit finds zero `sorry`, `admit`, custom `axiom`, or `opaque` declarations. `#print axioms` for all four public CLTs reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Preserve varying row spaces and row lengths, conditional Lindeberg convergence in probability, predictable-variance normalization, and the absence of independence assumptions.
- Expose both conditional and deterministic/unconditional fourth-moment bridges plus deterministic predictable-variance convergence.
- The API is genuine and non-vacuous; proceed to review with no filler dispatch.