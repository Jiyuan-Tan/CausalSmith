# Substrate requirement: singular-value-weyl

## Goal
Build the reusable indexed Weyl perturbation inequality for singular values of finite-dimensional real linear maps.

## Provides (API contract)
- A paper-agnostic theorem for finite-dimensional real inner-product spaces and linear maps `T E`, valid for every natural index `j`:
  `|((T + E).singularValues j) - (T.singularValues j)| ≤ ‖E‖`.
- An equivalent generic finite real matrix theorem is acceptable only if the exact linear-map theorem or its immediate thin specialization is exposed.

## Statement / milestones
Use Mathlib's `LinearMap.singularValues`, including its zero extension beyond finite rank. Prove the indexed two-sided perturbation bound for every `j`. The result must not assume injectivity, square shape, simple singular values, or a spectral gap. Develop general min–max/variational support lemmas if the existing API requires them.

## Standard reference
The Weyl/Mirsky singular-value perturbation inequality: each ordered singular value is 1-Lipschitz in operator norm. Standard finite-dimensional matrix analysis via the min–max characterization of singular values.

## Intended reuse
The CausalSmith run `stat_proxy_effectlaw_eigencollision_frontier/v1` needs the thin local wrapper
`|singularValue (A + H) j - singularValue A j| ≤ ‖matrixCLM H‖`
for rectangular matrices. The promoted result should be reusable throughout Causalean for spectral perturbation, rank thresholds, and weak-identification arguments.

## May assume / must derive
May assume finite-dimensional real inner-product spaces and existing Mathlib adjoint/singular-value definitions. Must derive the result for all natural indices, including zero-extension indices, without injectivity, square-shape, simplicity, or eigengap assumptions.

## Non-goals
Do not import any `CausalSmith/*_Research` module. Do not specialize the reusable theorem to the paper's `RectMatrix`, `matrixCLM`, or local `singularValue`; those remain a thin consumer wrapper.

## Known building blocks
- `Mathlib.Analysis.InnerProductSpace.SingularValues`
- `Mathlib.Analysis.InnerProductSpace.Adjoint`
- finite-dimensional self-adjoint spectral/min–max results as available

The paper-local `singular_value_variational_lower` handles only the final signal singular value under injectivity and is not sufficient; generalize the underlying idea only if useful. Verification requires a green targeted build, zero `sorry`/`admit`, and no new axioms under `#print axioms`.
