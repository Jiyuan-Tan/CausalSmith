# Local smoothness of an isolated rank-one spectral projector

Slug: `rank-one-spectral-projector-smoothness`

Build reusable, paper-agnostic finite-dimensional real matrix substrate for the
top rank-one spectral projector and its induced truncated pseudoinverse near a
strictly separated positive Gram eigenvalue.  The result must not assume that a
particular eigenvector selector is continuous: it must prove that the projector
is basis/sign independent on the simple-eigenvalue region and identify it with
an algebraic/resolvent formula there.

The minimal sufficient 2-by-2 version is acceptable and preferred.  For a real
symmetric matrix `G = [[a,b],[b,d]]`, define the ordered eigenvalue roots by the
quadratic formula and the top projector on the open region
`lambda₂ G < lambda₁ G` by

```lean
(G - lambda₂ G • 1) / (lambda₁ G - lambda₂ G).
```

Prove, on that region:

1. this matrix is the orthogonal projector onto the top eigenspace and equals
   the projection formed from any normalized ordered top eigenvector;
2. the ordered roots and projector are continuously differentiable locally;
3. when `G = H * H.transpose` and the top eigenvalue is positive, the rank-one
   truncation and pseudoinverse are given by `P * H` and
   `H.transpose * P / lambda₁ G` respectively;
4. consequently `(H,z,b) |-> dotProduct z ((H.transpose * P / lambda₁ G).mulVec b)`
   is continuously differentiable locally, with its derivative locally bounded.

An equivalent general isolated-eigenspace/Riesz-projector theorem is also
acceptable if the 2-by-2 rank-one corollary below is immediate.

Required local discharge wrapper in
`SCM_ProxyTargetspanTransport_Research/Helpers/TruncatedSVD.lean`:

```lean
-- For H0 : Matrix (Fin 2) (Fin 2) Real with Gram eigenvalues 1/4 and 0,
-- the choice-based topProjection/truncatedPseudoInverse at rank one agree on
-- a neighbourhood of H0 with the algebraic projector/pseudoinverse above;
-- regularWaldFunctional is C^1 there and its derivative is locally bounded.
```

This wrapper must be strong enough to discharge the fixed-baseline Wald
localization step used by
`thm:no-uniform-studentized-wald-adaptation`, without changing that theorem's
statement or adding an assumption.

Proposed imports:

- `Mathlib.Analysis.Matrix.Spectrum`
- `Mathlib.Analysis.Calculus.FDeriv.Basic`
- `Mathlib.Analysis.Calculus.FDeriv.Mul`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- finite-dimensional matrix norm/continuous-linear-map modules as needed

Research-folder prerequisites to extract/generalize before the study:

- `gramMatrix`, `topProjection`, `truncatedSVD`, `truncatedPseudoInverse`, and
  `regularWaldFunctional` currently live in
  `Helpers/TruncatedSVD.lean`.  The reusable study module must not import a
  `CausalSmith/*_Research` module; prove the algebraic theorem independently
  and leave only thin equality/specialization wrappers in the paper module.
- The paper's baseline is the explicit `Fin 2` rank-one Gram matrix with
  eigenvalues `1/4` and `0`.  Do not generalize beyond what is useful unless
  the general statement is genuinely cheaper.
- Existing singular-value Weyl continuity controls eigenvalues only; it does
  not establish projector, pseudoinverse, or derivative regularity.

Verification requirements: targeted module build green, zero
`sorry`/`admit`/new axioms, and `#print axioms` clean.  Promote the complete
non-research dependency closure and relay the final Causalean theorem path so
the local wrapper can replace the blocker.
