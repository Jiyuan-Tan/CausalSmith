/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Ridge.Finite
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Ridge regression — closed form

For `λ > 0` the ridge Gram matrix `XᵀX + λI` is positive definite, hence
invertible, so the ridge coefficient `β̂ = (XᵀX + λI)⁻¹ Xᵀy` is the unique
solution of the ridge normal equations — no full-rank assumption on `X` needed.
Here `λ` is the penalty on the unnormalized sum-of-squares objective: for the
average-loss convention with penalty `λavg`, pass `λ = |Obs| · λavg`.
-/

@[expose] public section

namespace Causalean.ML

open Matrix BigOperators

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param] [DecidableEq Param]

/-- [The closed-form ridge coefficient](goal) applies
[the inverse regularized Gram to the design--outcome cross-product](step:1). It uses
[a design matrix and outcome vector](hyp:X,y) over
[finite observation and decidable coefficient indices](hyp:Obs,Param) with
[ridge penalty weight](hyp:lam). The inverse is ordinary when the
regularized matrix is invertible; the unnormalized convention makes an averaged-loss penalty
equal to this weight divided by the observation count. -/
noncomputable def ridgeCoef
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (lam : ℝ) : Param → ℝ :=
  ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ))⁻¹ *ᵥ (Xᵀ *ᵥ y)

set_option linter.unusedFintypeInType false in
/-- [A positive ridge penalty makes the design Gram positive definite](goal) for
[the finite design matrix](hyp:X) over [the observation and coefficient indices](hyp:Obs,Param),
because [the penalty is positive](hyp:hlam). -/
theorem ridgeGram_posDef
    (X : Matrix Obs Param ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)).PosDef := by
  have hpsd : (Xᵀ * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self X)
  have hI : (lam • (1 : Matrix Param Param ℝ)).PosDef := by
    exact Matrix.PosDef.smul Matrix.PosDef.one hlam
  exact Matrix.PosDef.posSemidef_add hpsd hI

/-- [The closed-form ridge coefficient satisfies the ridge normal equations](goal) for
[the finite design and outcome vectors](hyp:X,y) over
[the observation and coefficient indices](hyp:Obs,Param) when
[the ridge penalty is strictly positive](hyp:hlam). -/
theorem ridgeCoef_normalEq
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)) *ᵥ ridgeCoef X y lam = Xᵀ *ᵥ y := by
  let G : Matrix Param Param ℝ := (Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)
  have hGpos : G.PosDef := by
    dsimp [G]
    exact ridgeGram_posDef X hlam
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  dsimp [ridgeCoef, G]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGdet, Matrix.one_mulVec]

/-- [The closed-form ridge coefficient uniquely solves the normal equations](goal):
[any candidate coefficient vector](hyp:β) for [the finite design and response vectors](hyp:X,y)
over [the observation and coefficient indices](hyp:Obs,Param) must
equal it when [the ridge penalty is strictly positive](hyp:hlam) and
[the candidate satisfies the equations](hyp:hNE). -/
theorem ridgeCoef_unique
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) {lam : ℝ} (hlam : 0 < lam)
    {β : Param → ℝ}
    (hNE : ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)) *ᵥ β = Xᵀ *ᵥ y) :
    β = ridgeCoef X y lam := by
  let G : Matrix Param Param ℝ := (Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)
  have hGpos : G.PosDef := by
    dsimp [G]
    exact ridgeGram_posDef X hlam
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  have hclosed : G *ᵥ ridgeCoef X y lam = Xᵀ *ᵥ y := by
    dsimp [G]
    exact ridgeCoef_normalEq X y hlam
  have hsame : G *ᵥ β = G *ᵥ ridgeCoef X y lam := by
    dsimp [G] at hclosed ⊢
    rw [hNE, hclosed]
  have hcancel := congrArg (fun v : Param → ℝ => G⁻¹ *ᵥ v) hsame
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hGdet, Matrix.one_mulVec] using hcancel

end Causalean.ML
