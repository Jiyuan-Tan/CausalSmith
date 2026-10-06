/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.GaussMarkov.QuadForm

/-! # Least-Norm Covariance Ordering

This file proves algebraic quadratic-form orderings for weights satisfying the
same design-balance identity `w ᵥ* X = c`. A column-span weight has no larger
quadratic form under a spherical matrix, and a weight whose image under a
positive-semidefinite matrix lies in the column span has no larger quadratic
form under that matrix. The statements do not include a mean model and therefore
do not themselves establish estimator unbiasedness.

The main public results are `quadVar_spherical_le_of_colSpan` and
`quadVar_le_of_mulVec_mem_colSpan`. The supporting lemma
`colSpan_dotProduct_leftNull` records the orthogonality between the column span
of `X` and the left null space that drives the Pythagorean comparison. -/

public section

namespace Causalean.Stat.GaussMarkov

open Matrix

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param]

/-- Column span is Euclidean-orthogonal to the left null space: if `z` lies in the
left null space of `X` (`z ᵥ* X = 0`), then any column-span vector `X *ᵥ g` is
orthogonal to `z`. -/
lemma colSpan_dotProduct_leftNull {X : Matrix Obs Param ℝ} {g : Param → ℝ}
    {z : Obs → ℝ} (hz : z ᵥ* X = 0) : (X *ᵥ g) ⬝ᵥ z = 0 := by
  rw [dotProduct_comm, dotProduct_mulVec, hz, zero_dotProduct]

/-- Nonnegativity of the Euclidean self dot product. -/
lemma dotProduct_self_nonneg' (v : Obs → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **Spherical quadratic-form ordering.** Fix a design matrix `X`, a target
combination `c`, and suppose [the matrix `S` is spherical:
`S = σ² I` for some scale `σ`](hyp:hS). Among all weight vectors `w` satisfying
[the same design-balance identity `w ᵥ* X = c`](hyp:hUStar,hU), if [`wStar` lies
in the column span of `X`, `wStar = X *ᵥ g`](hyp:hStar), then [the quadratic
form `wStarᵀ S wStar` is no larger than `wᵀ S w`](goal). -/
theorem quadVar_spherical_le_of_colSpan [DecidableEq Obs]
    {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    {S : Matrix Obs Obs ℝ} {σ : ℝ} (hS : SphericalErrors S σ)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hStar : wStar = X *ᵥ g)
    (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    quadVar S wStar ≤ quadVar S w := by
  -- `z := w - wStar` lies in the left null space of `X`.
  have hz : (w - wStar) ᵥ* X = 0 := by rw [sub_vecMul, hU, hUStar, sub_self]
  -- The column-span weight is orthogonal to `z`.
  have hortho : wStar ⬝ᵥ (w - wStar) = 0 := by
    have h := colSpan_dotProduct_leftNull (g := g) hz
    rwa [← hStar] at h
  -- Pythagoras: `‖w - wStar‖² = ‖w‖² - ‖wStar‖²`.
  have hcomm : w ⬝ᵥ wStar = wStar ⬝ᵥ w := dotProduct_comm w wStar
  have hcross : wStar ⬝ᵥ w = wStar ⬝ᵥ wStar := by
    have h := hortho; rw [dotProduct_sub] at h; linarith
  have key : (w - wStar) ⬝ᵥ (w - wStar) = w ⬝ᵥ w - wStar ⬝ᵥ wStar := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
    linarith
  have hznn := dotProduct_self_nonneg' (w - wStar)
  have hle : wStar ⬝ᵥ wStar ≤ w ⬝ᵥ w := by linarith
  rw [quadVar_spherical hS, quadVar_spherical hS]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg σ)

/-- **Positive-semidefinite quadratic-form ordering.** Fix a design matrix `X`,
a target combination `c`, and [a positive-semidefinite matrix `S`](hyp:hS).
Among all weight vectors `w` satisfying [the same design-balance identity
`w ᵥ* X = c`](hyp:hUStar,hU), if [the image `S *ᵥ wStar` lies in the column
span of `X`](hyp:hGLS), then [the quadratic form `wStarᵀ S wStar` is no larger
than `wᵀ S w`](goal). -/
theorem quadVar_le_of_mulVec_mem_colSpan {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    {S : Matrix Obs Obs ℝ} (hS : S.PosSemidef)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hGLS : S *ᵥ wStar = X *ᵥ g)
    (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    quadVar S wStar ≤ quadVar S w := by
  have hsymm : Sᵀ = S := by
    have h := hS.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  set z := w - wStar with hzdef
  have hz : z ᵥ* X = 0 := by rw [hzdef, sub_vecMul, hU, hUStar, sub_self]
  -- Both `Σ`-inner-product cross terms vanish.
  have term1 : z ⬝ᵥ S *ᵥ wStar = 0 := by
    rw [hGLS, dotProduct_mulVec, hz, zero_dotProduct]
  have term2 : wStar ⬝ᵥ S *ᵥ z = 0 := by
    rw [dotProduct_mulVec, ← hsymm, vecMul_transpose, hGLS]
    exact colSpan_dotProduct_leftNull hz
  have hwz : w = wStar + z := by rw [hzdef]; abel
  have hexpand : quadVar S w = quadVar S wStar + quadVar S z := by
    simp only [quadVar]
    rw [hwz, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, term1, term2]
    ring
  rw [hexpand]
  have := quadVar_nonneg hS z
  linarith

end Causalean.Stat.GaussMarkov
