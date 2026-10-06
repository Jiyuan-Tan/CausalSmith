module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Kernels
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Finite-moment point-CATE frontier: Helpers/TruncationMoments. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- On the discarded tail, the p-moment dominates the absolute truncation error. -/
-- @node: truncation_tail_pointwise
lemma truncation_tail_pointwise (p T y : ℝ) (hp : 1 < p) (hT : 0 < T) :
    |y - trunc T y| ≤ T^(1-p) * |y|^p := by
  by_cases hy : |y| ≤ T
  · simp only [trunc, if_pos hy, sub_self, abs_zero]
    positivity
  · have hypos : 0 < |y| := hT.trans (lt_of_not_ge hy)
    have hr : |y|^(1-p) ≤ T^(1-p) :=
      Real.rpow_le_rpow_of_nonpos hT (le_of_not_ge hy) (by linarith)
    calc
      |y - trunc T y| = |y| := by simp [trunc, hy]
      _ = |y|^(1-p) * |y|^p := by
        rw [← Real.rpow_add hypos, sub_add_cancel, Real.rpow_one]
      _ ≤ T^(1-p) * |y|^p := mul_le_mul_of_nonneg_right hr (by positivity)

/-- On the retained region, the p-moment dominates the truncated square. -/
-- @node: truncation_square_pointwise
lemma truncation_square_pointwise (p T y : ℝ) (hp : 0 < p ∧ p ≤ 2) (hT : 0 < T) :
    (trunc T y)^2 ≤ T^(2-p) * |y|^p := by
  by_cases hy : |y| ≤ T
  · by_cases hz : y = 0
    · subst y
      simp [trunc, hT.le, Real.zero_rpow hp.1.ne']
    · have hypos : 0 < |y| := abs_pos.mpr hz
      have hr : |y|^(2-p) ≤ T^(2-p) :=
        Real.rpow_le_rpow (abs_nonneg y) hy (by linarith)
      calc
        (trunc T y)^2 = |y|^2 := by simp [trunc, hy, sq_abs]
        _ = |y|^(2-p) * |y|^p := by
          rw [← Real.rpow_add hypos, sub_add_cancel, Real.rpow_two]
        _ ≤ T^(2-p) * |y|^p := mul_le_mul_of_nonneg_right hr (by positivity)
  · simp only [trunc, if_neg hy, zero_pow (by decide : 2 ≠ 0)]
    positivity

/-- A probability p-moment bound gives first-moment finiteness, a Jensen bound, truncation bias,
and the truncated second moment, including the finite-variance endpoint. -/
-- @node: truncation_moment_bounds
lemma truncation_moment_bounds (p T : ℝ) (hp : 1 < p ∧ p ≤ 2) (hT : 1 ≤ T)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂Q ≤ 10) :
  Integrable (fun y : ℝ => y) Q ∧ |∫ y, y ∂Q| ≤ (10 : ℝ)^(1/p) ∧
  |(∫ y, y ∂Q) - ∫ y, trunc T y ∂Q| ≤ 10 * T^(1-p) ∧
  (∫ y, (trunc T y)^2 ∂Q) ≤ 10 * T^(2-p) := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp.1
  have hpnonneg : 0 ≤ p := hp0.le
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hm : AEStronglyMeasurable (fun y : ℝ => y) Q := by fun_prop
  have hmp : Integrable (fun y : ℝ => |y|^p) Q := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 ?_⟩
    exact hQ.trans_lt (by norm_num)
  have hfirst : Integrable (fun y : ℝ => y) Q := by
    have h := integrable_norm_rpow_of_le hm (by norm_num : (0 : ℝ) ≤ 1) hp0.le hp.1.le
      (by simpa only [Real.norm_eq_abs] using hmp)
    apply (integrable_norm_iff hm).1
    simpa using h
  have hmoment : (∫ y, |y|^p ∂Q) ≤ 10 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 10)]
    rw [ofReal_integral_eq_lintegral_ofReal hmp (ae_of_all _ fun y => by positivity)]
    simpa using hQ
  have ht : Integrable (trunc T) Q := by
    apply hfirst.mono (by fun_prop)
    exact ae_of_all _ fun y => by
      by_cases hy : |y| ≤ T <;> simp [trunc, hy, Real.norm_eq_abs]
  refine ⟨hfirst, ?_, ?_, ?_⟩
  · have hlp : MemLp (fun y : ℝ => y) (ENNReal.ofReal p) Q := by
      apply (integrable_norm_rpow_iff hm (by simp [hp0]) (by simp)).1
      simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hmp
    have hcomp := eLpNorm_le_eLpNorm_of_exponent_le
      (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by simpa using ENNReal.ofReal_le_ofReal hp.1.le) hm
    rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
        (memLp_one_iff_integrable.2 hfirst),
      MemLp.eLpNorm_eq_integral_rpow_norm (by simp [hp0]) (by simp) hlp] at hcomp
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, ENNReal.toReal_ofReal hp0.le,
      Real.norm_eq_abs] at hcomp
    have hj : (∫ y, |y| ∂Q) ≤ (∫ y, |y|^p ∂Q)^(1/p) := by
      simpa only [one_div] using (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcomp
    calc
      |∫ y, y ∂Q| ≤ ∫ y, |y| ∂Q := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y : ℝ => y)
      _ ≤ (∫ y, |y|^p ∂Q)^(1/p) := hj
      _ ≤ (10 : ℝ)^(1/p) := Real.rpow_le_rpow (integral_nonneg fun y => by positivity)
        hmoment (by positivity)
  · rw [← integral_sub hfirst ht]
    calc
      |∫ y, y - trunc T y ∂Q| ≤ ∫ y, |y - trunc T y| ∂Q := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun y : ℝ => y - trunc T y)
      _ ≤ ∫ y, T^(1-p) * |y|^p ∂Q :=
        integral_mono (hfirst.sub ht).abs (hmp.const_mul _) fun y =>
          truncation_tail_pointwise p T y hp.1 hT0
      _ = T^(1-p) * ∫ y, |y|^p ∂Q := integral_const_mul _ _
      _ ≤ 10 * T^(1-p) := by nlinarith [Real.rpow_pos_of_pos hT0 (1-p)]
  · have hs : Integrable (fun y => (trunc T y)^2) Q := by
      apply (hmp.const_mul (T^(2-p))).mono' (by fun_prop)
      exact ae_of_all _ fun y => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (trunc T y))] using
          truncation_square_pointwise p T y ⟨hp0, hp.2⟩ hT0
    calc
      (∫ y, (trunc T y)^2 ∂Q) ≤ ∫ y, T^(2-p) * |y|^p ∂Q :=
        integral_mono hs (hmp.const_mul _) fun y =>
          truncation_square_pointwise p T y ⟨hp0, hp.2⟩ hT0
      _ = T^(2-p) * ∫ y, |y|^p ∂Q := integral_const_mul _ _
      _ ≤ 10 * T^(2-p) := by nlinarith [Real.rpow_pos_of_pos hT0 (2-p)]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
