import Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Main
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Examples of polynomial-over-affine integral analyticity

This file verifies the API on a scalar integral over a compact real interval.
-/

open MeasureTheory Set

namespace Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity

/-- [The scalar integral of one plus the parameter times the integration variable, divided by two plus that product, is real analytic on the open interval from minus one to one](goal). -/
theorem analyticOnNhd_integral_one_add_tx_div_two_add_tx :
    AnalyticOnNhd ℝ
      (fun t : ℝ ↦ ∫ x in Set.Icc (0 : ℝ) 1, (1 + t * x) / (2 + t * x))
      (Set.Ioo (-1 : ℝ) 1) := by
  let c : Fin 2 → ℝ → ℝ := fun i x ↦ if i = 0 then 1 else x
  have h := @analyticOnNhd_setIntegral_polynomial_div_affine
    ℝ Real.measurableSpace volume (Set.Icc (0 : ℝ) 1)
    measurableSet_Icc measure_Icc_lt_top.ne
    1 c (fun _ ↦ 2) (fun x ↦ 2 + x)
    (Set.Ioo (-1 : ℝ) 1) 1 1 (fun _ ↦ 1)
    isOpen_Ioo (by norm_num) (by norm_num)
    (by
      intro i
      fin_cases i
      · simp [c]
      · change Measurable (fun x : ℝ ↦ x)
        fun_prop)
    (by fun_prop) (by fun_prop)
    (by
      intro i x hx
      fin_cases i
      · norm_num [c]
      · simpa [c, abs_of_nonneg hx.1] using hx.2)
    (by
      intro x hx
      simpa [abs_of_nonneg hx.1] using hx.2)
    (by
      intro t ht x hx
      have htx : -1 < t * x := by
        by_cases ht0 : 0 ≤ t
        · exact (by norm_num : (-1 : ℝ) < 0).trans_le (mul_nonneg ht0 hx.1)
        · have htle : t ≤ t * x := by
            have hmul := mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge ht0)
            simpa using hmul
          exact ht.1.trans_le htle
      have hsep : 1 ≤ 2 + t * x := by linarith
      rw [show affineDenominator (fun _ : ℝ ↦ 2) (fun x ↦ 2 + x) t x =
          2 + t * x by
        unfold affineDenominator
        ring]
      exact hsep.trans (le_abs_self _))
  have hfun :
      (fun t : ℝ ↦ ∫ x in Set.Icc (0 : ℝ) 1,
        polynomialNumerator 1 c t x /
          affineDenominator (fun _ : ℝ ↦ 2) (fun x ↦ 2 + x) t x) =
      (fun t : ℝ ↦ ∫ x in Set.Icc (0 : ℝ) 1, (1 + t * x) / (2 + t * x)) := by
    funext t
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp
    rw [show polynomialNumerator 1 c t x = 1 + t * x by
      simp [polynomialNumerator, c, Finset.univ_fin2]
      ring]
    rw [show affineDenominator (fun _ : ℝ ↦ 2) (fun x ↦ 2 + x) t x =
        2 + t * x by
      unfold affineDenominator
      ring]
  rw [hfun] at h
  exact h

end Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity
