# Substrate requirement: rank-one-spectral-projector-smoothness

## Goal
Build reusable, paper-agnostic finite-dimensional real-matrix substrate proving local C¹ regularity and locally bounded derivative for an isolated top rank-one spectral projector and its induced truncated pseudoinverse, without assuming continuity of an eigenvector selector.

## Provides (API contract)
- Ordered eigenvalue roots for a real symmetric 2-by-2 matrix `G = [[a,b],[b,d]]`, given by the quadratic formula.
- An algebraic top projector on `lambda₂ G < lambda₁ G`, defined by `(G - lambda₂ G • 1) / (lambda₁ G - lambda₂ G)`.
- A theorem that this expression is the orthogonal projector onto the top eigenspace and equals the projector formed from any normalized ordered top eigenvector, hence is basis/sign independent.
- Local continuous differentiability of the ordered roots and algebraic projector on the strict-gap region.
- For `G = H * H.transpose` with positive top eigenvalue, formulas identifying rank-one truncation and pseudoinverse with `P * H` and `H.transpose * P / lambda₁ G`.
- Local continuous differentiability, with locally bounded derivative, of `(H,z,b) |-> dotProduct z ((H.transpose * P / lambda₁ G).mulVec b)`.

## Statement / milestones
The minimal sufficient 2-by-2 theorem is preferred. For real symmetric `G`, prove on the open region `lambda₂ G < lambda₁ G` that the algebraic quotient projector is the top orthogonal projector and is independent of normalized top-eigenvector sign/basis choice. Prove the ordered roots and projector are C¹ locally there. For `G = H * H.transpose` and `0 < lambda₁ G`, derive the rank-one truncation and pseudoinverse formulas above. Conclude that the induced bilinear Wald functional in `(H,z,b)` is C¹ locally and that its derivative is bounded on some neighborhood of each point in the region.

An equivalent general isolated-eigenspace or Riesz-projector result is acceptable only when the required 2-by-2 rank-one corollaries are immediate.

## Standard reference
Standard finite-dimensional symmetric-matrix spectral theory, the simple-eigenvalue spectral projector formula, and elementary Fréchet calculus on finite-dimensional normed spaces.

## Intended reuse
The immediate consumer is the fixed-baseline Wald localization in `thm:no-uniform-studentized-wald-adaptation` for a `Fin 2` matrix whose Gram eigenvalues are `1/4` and `0`. The paper-local wrapper must show that its choice-based `topProjection` and `truncatedPseudoInverse` agree near that baseline with the algebraic projector/pseudoinverse, making `regularWaldFunctional` C¹ there with locally bounded derivative. The reusable module must not import any `CausalSmith/*_Research` module.

## May assume / must derive
May assume real symmetry, a strict simple top-eigenvalue gap, and positivity of the top eigenvalue where division is used. Must derive basis/sign independence, the algebraic projector identity, local C¹ regularity, truncated-SVD/pseudoinverse formulas, and local derivative boundedness. Do not assume that a particular eigenvector selector is continuous.

## Non-goals
Do not generalize beyond the useful 2-by-2 rank-one setting unless the general proof is genuinely cheaper. Do not change the consuming theorem statement or add a paper assumption.

## Known building blocks
Likely useful imports include `Mathlib.Analysis.Matrix.Spectrum`, `Mathlib.Analysis.Calculus.FDeriv.Basic`, `Mathlib.Analysis.Calculus.FDeriv.Mul`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`, and finite-dimensional matrix norm/continuous-linear-map modules. Existing singular-value Weyl continuity controls eigenvalues only and does not supply projector, pseudoinverse, or derivative regularity.

Verification must include a green targeted module build, zero `sorry`/`admit`/new axioms, clean `#print axioms`, and promotion of the complete non-research dependency closure.
