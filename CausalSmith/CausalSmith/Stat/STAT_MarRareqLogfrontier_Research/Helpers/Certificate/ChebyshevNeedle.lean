module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! Chebyshev needle bounds used by the light-cell analysis. -/

public section

open Polynomial Set

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: cheb_secant
/-- Given [the specified inputs and assumptions](hyp:k,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma cheb_secant (k : ℕ) (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    0 ≤ 1 - (Chebyshev.T ℝ (k : ℤ)).eval x ∧
    1 - (Chebyshev.T ℝ (k : ℤ)).eval x ≤ (k : ℝ)^2 * (1 - x) := by
  have hT := Chebyshev.abs_eval_T_real_le_one (k : ℤ)
    (show |x| ≤ 1 by exact abs_le.mpr ⟨hx.1, hx.2⟩)
  have hderiv (y : ℝ) (hy : y ∈ Ico x 1) :
      |(derivative (Chebyshev.T ℝ (k : ℤ))).eval y| ≤ (k : ℝ)^2 := by
    have hyy : |y| ≤ 1 := abs_le.mpr ⟨le_trans hx.1 hy.1, le_of_lt hy.2⟩
    have hh := Chebyshev.abs_iterate_derivative_T_real_le (k : ℤ) 1 hyy
    simpa [Chebyshev.derivative_T_eval_one] using hh
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y : ℝ => (Chebyshev.T ℝ (k : ℤ)).eval y)
      (f' := fun y : ℝ => (derivative (Chebyshev.T ℝ (k : ℤ))).eval y)
      (a := x) (b := 1) (C := (k : ℝ)^2)
      (fun y _ => (Chebyshev.T ℝ (k : ℤ)).hasDerivWithinAt y (Icc x 1))
      (by intro y hy; simpa only [Real.norm_eq_abs] using hderiv y hy)
      (1 : ℝ) (show (1 : ℝ) ∈ Icc x 1 from ⟨hx.2, le_refl _⟩)
  constructor
  · have := (abs_le.mp hT).2
    linarith
  · rw [Chebyshev.T_eval_one] at hmv
    have := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hmv)).2
    linarith

end CausalSmith.Stat.MarRareqLogfrontier
