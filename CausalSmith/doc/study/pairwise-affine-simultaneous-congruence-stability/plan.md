## Done
- Ground-truth audit completed for all five modules; every source file directly elaborates successfully, and `lake build CausalSmith.Substrate.PairwiseAffineSimultaneousCongruenceStability.Main` succeeds with warnings only.
- Source grep confirms zero `sorry`, `admit`, or `axiom` declarations.
- `#print axioms` for `selectedTriple_offDiagonal_control`, `diagonalBranch_control`, `opNorm_sub_le_of_pairwise_affine`, and `opNorm_sub_le_condition_specialization` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Verified the genuine API: pair-dependent affine witnesses, selected-triple Cramer estimates, diagonal normalization, L² aggregation, local branch selection from a positive ordinary neighborhood, operator-norm stability, and the exact requested condition-specialized constant.
- Library search confirmed reuse of the neutral `Causalean.Discovery.LinearDisentanglement.Quantitative` infrastructure. The [BACKSHIFT primary source](https://arxiv.org/abs/1506.02494) was checked from its LaTeX source; its coordinate-pair identifiability condition supports pair-specific witnesses rather than a global full-dimensional minor.
- Imports remain confined to Mathlib, Causalean, and this substrate tree; all files remain focused and documented.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Retain `PairwiseAffineSeparated` with a separate environment triple for each distinct coordinate pair; introduce no global affine determinant.
- Retain the explicit positive reference-neighborhood hypothesis: residual smallness alone cannot distinguish remote exact permutation/scaling branches. The transition identity branch is derived from that ordinary neighborhood and the residual threshold, not assumed by the headline theorem.
- Use norm/inverse envelopes in the generic theorem and determinant/condition envelopes in the specialization. The specialized bound expands exactly to `16 * (6*M/γ) * sqrt(p*(p-1)*(1+L^2)) * L^3 * ε` with `L = ((p!)*κ^(p-1))^(1/p)`.