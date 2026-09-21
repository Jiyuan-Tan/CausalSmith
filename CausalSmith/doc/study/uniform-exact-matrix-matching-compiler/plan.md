## Done
- Ground-truth audit: direct Lean checks of `RegisterProgram.lean` and `Main.lean`, plus `lake build CausalSmith.Substrate.UniformExactMatrixMatchingCompiler.Main`, succeed with warnings only.
- `Basic.lean`, `LinearAlgebra.lean`, `Machine.lean`, `Matching.lean`, and `GreedyCompletion.lean` remain closed; `greedyCompletionTail_eq_canonical` has no `sorryAx`.
- Decomposed the repeatedly unsuccessful `basisSelectionStage`: added explicit scratch selector registers, `CompletionSelectorStage`, and `BasisSerializationStage`; the `basisSelectionStage` wrapper is now proved by composition and budget addition.
- Library searches found no reusable exact Gaussian register compiler or matching machine. Fetched the pinned Mathlib `db584cd6` primary sources for transvection reduction and Hall matching; both provide mathematical existence infrastructure, not execution-linked code.

## Remaining
- `RegisterProgram.lean`: `completionSelectorStage`, implementing the exact incremental echelon scan.
- `RegisterProgram.lean`: `basisSerializationStage`, serializing selector bits into the canonical completed basis.
- `RegisterProgram.lean`: `inverseKernelStage`, `supportMatchingStage`, and `forestSerializationStage`.

## Blocked
- No mathematical inconsistency found. The execution layer remains a serial proof chain: selector → basis serialization → inverse/kernel → support/matching → forest serialization.
- The consumer theorem still contains `sorryAx` exactly through these five disclosed stage implementations.

## Decisions
- Preserve the genuine lexicographically canonical completion, dimension-only program code, matrix-entry-only numerical inputs, explicit output maps, rational preservation, and stated cubic budgets.
- The former monolithic basis-selection obligation was not retried. Its selector computation and serialization were separated with semantic interfaces and independent cost shares of `300000*n^3` and `100000*n^3`.
- Dispatch only the lowest open stage this round because all later implementations share the same import/proof chain and live file.