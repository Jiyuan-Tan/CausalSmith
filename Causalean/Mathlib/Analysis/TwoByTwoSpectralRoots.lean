import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Ordered roots of a real two-by-two matrix

This module supplies explicit ordered roots, their spectral interpretation for symmetric matrices, and their local continuous differentiability away from a repeated root.  The formulas are defined on all real two-by-two matrices, so the strict-gap region is open without choosing an eigenvector.
-/

open Matrix
open scoped Matrix.Norms.Elementwise

namespace Causalean.Mathlib.Analysis

/-- Given [a real two-by-two matrix](hyp:G), [the discriminant governing its two ordered quadratic-formula roots](goal) is the squared diagonal difference plus four times the squared upper off-diagonal entry. -/
def rootDiscriminant (G : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (G 0 0 - G 1 1) ^ 2 + 4 * (G 0 1) ^ 2

/-- Given [a real two-by-two matrix](hyp:G), [its larger quadratic-formula root](goal) is half the trace plus half the nonnegative square root of the discriminant. -/
noncomputable def lambda₁ (G : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (G 0 0 + G 1 1 + Real.sqrt (rootDiscriminant G)) / 2

/-- Given [a real two-by-two matrix](hyp:G), [its smaller quadratic-formula root](goal) is half the trace minus half the nonnegative square root of the discriminant. -/
noncomputable def lambda₂ (G : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (G 0 0 + G 1 1 - Real.sqrt (rootDiscriminant G)) / 2

/-- [The strict-gap region](goal) consists of real two-by-two matrices whose lower quadratic-formula root is strictly below their upper root. -/
def strictGapSet : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {G | lambda₂ G < lambda₁ G}

/-- For [a real two-by-two matrix](hyp:G), [its explicit discriminant is nonnegative](goal). -/
theorem rootDiscriminant_nonneg (G : Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ rootDiscriminant G := by
  unfold rootDiscriminant
  positivity

/-- For [a real two-by-two matrix](hyp:G), [the difference between its upper and lower roots is the nonnegative square root of its discriminant](goal). -/
theorem lambda₁_sub_lambda₂ (G : Matrix (Fin 2) (Fin 2) ℝ) :
    lambda₁ G - lambda₂ G = Real.sqrt (rootDiscriminant G) := by
  unfold lambda₁ lambda₂
  ring

/-- For [a real two-by-two matrix](hyp:G), [its lower explicit root does not exceed its upper explicit root](goal). -/
theorem lambda₂_le_lambda₁ (G : Matrix (Fin 2) (Fin 2) ℝ) :
    lambda₂ G ≤ lambda₁ G := by
  rw [← sub_nonneg, lambda₁_sub_lambda₂]
  exact Real.sqrt_nonneg _

/-- For [a real two-by-two matrix](hyp:G), [having distinct ordered roots is equivalent to strict positivity of its discriminant](goal). -/
theorem mem_strictGapSet_iff_discriminant_pos (G : Matrix (Fin 2) (Fin 2) ℝ) :
    G ∈ strictGapSet ↔ 0 < rootDiscriminant G := by
  change lambda₂ G < lambda₁ G ↔ 0 < rootDiscriminant G
  rw [← sub_pos, lambda₁_sub_lambda₂, Real.sqrt_pos]

/-- For [a real two-by-two matrix](hyp:G), [the two explicit roots add to its trace](goal). -/
theorem lambda₁_add_lambda₂ (G : Matrix (Fin 2) (Fin 2) ℝ) :
    lambda₁ G + lambda₂ G = G 0 0 + G 1 1 := by
  unfold lambda₁ lambda₂
  ring

/-- Given [a real two-by-two matrix](hyp:G) that [is symmetric](hyp:hG), [the product of its two explicit roots equals its determinant](goal). -/
theorem lambda₁_mul_lambda₂ {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G.IsHermitian) :
    lambda₁ G * lambda₂ G = G.det := by
  have hsym : G 1 0 = G 0 1 := by
    simpa using hG.apply 0 1
  have hsqrt : Real.sqrt (rootDiscriminant G) ^ 2 = rootDiscriminant G :=
    Real.sq_sqrt (rootDiscriminant_nonneg G)
  rw [Matrix.det_fin_two, hsym]
  unfold lambda₁ lambda₂ rootDiscriminant at *
  nlinarith

/-- Given [a real symmetric two-by-two matrix](hyp:G,hG) and [one of the two root labels](hyp:i), [subtracting that labelled explicit root from the diagonal has zero determinant](goal). -/
theorem det_sub_lambda_mul_one_eq_zero {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (i : Fin 2) :
    (G - (if i = 0 then lambda₁ G else lambda₂ G) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
  have hsym : G 1 0 = G 0 1 := by
    simpa using hG.apply 0 1
  have hsqrt : Real.sqrt (rootDiscriminant G) ^ 2 = rootDiscriminant G :=
    Real.sq_sqrt (rootDiscriminant_nonneg G)
  fin_cases i <;>
    rw [Matrix.det_fin_two] <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, lambda₁, lambda₂] <;>
    rw [hsym] <;>
    unfold rootDiscriminant at * <;>
    nlinarith

/-- Given [a real symmetric two-by-two matrix](hyp:G,hG), [a real number](hyp:μ), [a nonzero two-vector](hyp:v,hv), and [an eigenvector relation for that number](hyp:heig), [the number is one of the two explicit ordered roots](goal). -/
theorem eigenvalue_eq_lambda₁_or_lambda₂ {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) {μ : ℝ} {v : Fin 2 → ℝ} (hv : v ≠ 0)
    (heig : G.mulVec v = μ • v) :
    μ = lambda₁ G ∨ μ = lambda₂ G := by
  have hsym : G 1 0 = G 0 1 := by
    simpa using hG.apply 0 1
  have h0 := congrFun heig 0
  have h1 := congrFun heig 1
  simp [Matrix.mulVec] at h0 h1
  rw [hsym] at h1
  have hdet : (G 0 0 - μ) * (G 1 1 - μ) - G 0 1 * G 0 1 = 0 := by
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        funext i
        fin_cases i <;> assumption
      rw [hv0] at h0 h1
      simp only [mul_zero, zero_add] at h0 h1
      apply (mul_eq_zero.mp ?_).resolve_right hv1
      linear_combination (G 0 0 - μ) * h1 - G 0 1 * h0
    · apply (mul_eq_zero.mp ?_).resolve_right hv0
      linear_combination (G 1 1 - μ) * h0 - G 0 1 * h1
  have hsum := lambda₁_add_lambda₂ G
  have hprod := lambda₁_mul_lambda₂ hG
  rw [Matrix.det_fin_two, hsym] at hprod
  have hfactor : (μ - lambda₁ G) * (μ - lambda₂ G) = 0 := by
    calc
      _ = μ ^ 2 - μ * (lambda₁ G + lambda₂ G) + lambda₁ G * lambda₂ G := by
        ring
      _ = μ ^ 2 - μ * (G 0 0 + G 1 1) +
          (G 0 0 * G 1 1 - G 0 1 * G 0 1) := by
        rw [hsum, hprod]
      _ = 0 := by
        nlinarith [hdet]
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    linarith
  · right
    linarith

/-- Given [a real two-by-two matrix](hyp:G) with [a strict gap between its explicit roots](hyp:hG), [the upper root varies continuously differentiably near that matrix](goal). -/
theorem contDiffAt_lambda₁ {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G ∈ strictGapSet) :
    ContDiffAt ℝ 1 lambda₁ G := by
  have hdisc : ContDiffAt ℝ 1 rootDiscriminant G := by
    unfold rootDiscriminant
    fun_prop
  have hpos : 0 < rootDiscriminant G :=
    (mem_strictGapSet_iff_discriminant_pos G).mp hG
  have hsqrt := hdisc.sqrt (ne_of_gt hpos)
  unfold lambda₁
  exact (((contDiff_apply_apply ℝ ℝ (0 : Fin 2) (0 : Fin 2)).contDiffAt.add
    (contDiff_apply_apply ℝ ℝ (1 : Fin 2) (1 : Fin 2)).contDiffAt).add hsqrt).div_const 2

/-- Given [a real two-by-two matrix](hyp:G) with [a strict gap between its explicit roots](hyp:hG), [the lower root varies continuously differentiably near that matrix](goal). -/
theorem contDiffAt_lambda₂ {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G ∈ strictGapSet) :
    ContDiffAt ℝ 1 lambda₂ G := by
  have hdisc : ContDiffAt ℝ 1 rootDiscriminant G := by
    unfold rootDiscriminant
    fun_prop
  have hpos : 0 < rootDiscriminant G :=
    (mem_strictGapSet_iff_discriminant_pos G).mp hG
  have hsqrt := hdisc.sqrt (ne_of_gt hpos)
  unfold lambda₂
  exact (((contDiff_apply_apply ℝ ℝ (0 : Fin 2) (0 : Fin 2)).contDiffAt.add
    (contDiff_apply_apply ℝ ℝ (1 : Fin 2) (1 : Fin 2)).contDiffAt).sub hsqrt).div_const 2

/-- [The region of real two-by-two matrices with distinct explicit roots is open](goal). -/
theorem isOpen_strictGapSet : IsOpen strictGapSet := by
  have hdisc : Continuous rootDiscriminant := by
    unfold rootDiscriminant
    fun_prop
  rw [show strictGapSet = {G | 0 < rootDiscriminant G} by
    ext G
    exact mem_strictGapSet_iff_discriminant_pos G]
  exact isOpen_lt continuous_const hdisc

/-- [The upper explicit root is continuously differentiable throughout the strict-gap region](goal). -/
theorem contDiffOn_lambda₁ : ContDiffOn ℝ 1 lambda₁ strictGapSet := by
  intro G hG
  exact (contDiffAt_lambda₁ hG).contDiffWithinAt

/-- [The lower explicit root is continuously differentiable throughout the strict-gap region](goal). -/
theorem contDiffOn_lambda₂ : ContDiffOn ℝ 1 lambda₂ strictGapSet := by
  intro G hG
  exact (contDiffAt_lambda₂ hG).contDiffWithinAt

end Causalean.Mathlib.Analysis
