# Indexed singular-value Weyl perturbation

Slug: `singular-value-weyl`

Build a reusable, paper-agnostic theorem for finite-dimensional real Euclidean spaces: for linear maps `T` and `E` and every natural index `j`,

```lean
|((T + E).singularValues j) - (T.singularValues j)| ≤ ‖E‖
```

An equivalent matrix theorem is acceptable if it is stated over generic finite real matrices and the exact local wrapper below is immediate. The result must use Mathlib's `LinearMap.singularValues`, including its zero extension beyond finite rank, and must not assume injectivity, square shape, simple singular values, or a spectral gap.

Required local discharge wrapper:

```lean
lemma singular_value_weyl {rows cols j : ℕ} (A H : RectMatrix rows cols) :
    |singularValue (A + H) j - singularValue A j| ≤ ‖matrixCLM H‖
```

Proposed imports:

- `Mathlib.Analysis.InnerProductSpace.SingularValues`
- `Mathlib.Analysis.InnerProductSpace.Adjoint`
- finite-dimensional self-adjoint spectral/min–max modules as needed

Research-folder prerequisites to extract/generalize before the study:

- `RectMatrix`, `matrixCLM`, and `singularValue` currently live in `Helpers/SpectralSubstrate.lean`; prefer proving the reusable theorem directly for `LinearMap` so only a thin paper compatibility wrapper remains.
- The existing local `singular_value_variational_lower` proves only a lower bound for the final signal singular value under injectivity. It may be generalized as supporting min–max infrastructure, but it does not imply the indexed two-sided perturbation result.
- The study substrate must not import any `CausalSmith/*_Research` module.

Verification requirements: targeted module build green, zero `sorry`/`admit`, and `#print axioms` showing no new axioms. Promote the whole non-research dependency closure together, then relay the final Causalean theorem path so the local wrapper can replace the blocker.
