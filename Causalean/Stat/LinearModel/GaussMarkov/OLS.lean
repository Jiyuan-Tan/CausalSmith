/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.GaussMarkov.LeastNorm

/-! # Ordinary Least Squares Weights

This file defines the ordinary least-squares weight vector `olsWeight X c` for
estimating a specified linear combination `c'β` from a finite design matrix `X`.
The definition uses the ordinary inverse of the normal-equations matrix
`Xᵀ * X`; the design-balance identity therefore assumes
`IsUnit (Xᵀ * X).det`, the finite full-column-rank condition.

The public facts are `olsWeight_vecMul_eq`, which proves
`olsWeight X c ᵥ* X = c`, and `olsWeight_quadVar_spherical_le`, which applies
`quadVar_spherical_le_of_colSpan` to compare the OLS weight's quadratic form
with every weight satisfying the same identity. These facts alone do not prove
unbiasedness because they do not include a mean model. -/

@[expose] public section

namespace Causalean.Stat.GaussMarkov

open Matrix

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param] [DecidableEq Param]

/-- For [finite observation and parameter index sets, with parameter indices that can be
distinguished](hyp:Obs,Param), [a real design matrix](hyp:X), and
[a real vector specifying a linear combination of the parameters](hyp:c), the
[ordinary-least-squares weight vector](goal) is $X(X^\mathsf{T}X)^{-1}c$.

This uses Lean's ordinary matrix inverse of `XᵀX`, not a Moore-Penrose
pseudoinverse; the design-balance theorem below separately assumes
`IsUnit (Xᵀ * X).det`. -/
noncomputable def olsWeight (X : Matrix Obs Param ℝ) (c : Param → ℝ) : Obs → ℝ :=
  X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ c)

/-- The OLS weight lies in the column span of `X`. -/
lemma olsWeight_mem_colSpan (X : Matrix Obs Param ℝ) (c : Param → ℝ) :
    olsWeight X c = X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ c) := rfl

/-- For [an invertible normal-equations matrix `XᵀX`](hyp:h), [the OLS weight
satisfies the design-balance identity `olsWeight X c ᵥ* X = c`](goal). -/
lemma olsWeight_vecMul_eq {X : Matrix Obs Param ℝ} (c : Param → ℝ)
    (h : IsUnit (Xᵀ * X).det) : olsWeight X c ᵥ* X = c := by
  have h1 : ∀ g : Param → ℝ, (X *ᵥ g) ᵥ* X = (Xᵀ * X) *ᵥ g := by
    intro g
    rw [← mulVec_transpose, mulVec_mulVec]
  calc olsWeight X c ᵥ* X
      = (Xᵀ * X) *ᵥ ((Xᵀ * X)⁻¹ *ᵥ c) := by rw [olsWeight, h1]
    _ = ((Xᵀ * X) * (Xᵀ * X)⁻¹) *ᵥ c := by rw [mulVec_mulVec]
    _ = (1 : Matrix Param Param ℝ) *ᵥ c := by rw [mul_nonsing_inv (Xᵀ * X) h]
    _ = c := one_mulVec c

/-- **OLS-weight quadratic-form ordering under a spherical matrix.** For [an
invertible normal-equations matrix `Xᵀ X`](hyp:h) and [a spherical matrix
`S = σ² I`](hyp:hS), among all weight vectors `w` satisfying [the same
design-balance identity `w ᵥ* X = c`](hyp:hU), [the quadratic form at
`olsWeight X c` is no larger than at `w`](goal). -/
theorem olsWeight_quadVar_spherical_le [DecidableEq Obs]
    {X : Matrix Obs Param ℝ} (c : Param → ℝ)
    (h : IsUnit (Xᵀ * X).det) {S : Matrix Obs Obs ℝ} {σ : ℝ}
    (hS : SphericalErrors S σ) {w : Obs → ℝ} (hU : w ᵥ* X = c) :
    quadVar S (olsWeight X c) ≤ quadVar S w :=
  quadVar_spherical_le_of_colSpan hS (olsWeight_mem_colSpan X c)
    (olsWeight_vecMul_eq c h) hU

end Causalean.Stat.GaussMarkov
