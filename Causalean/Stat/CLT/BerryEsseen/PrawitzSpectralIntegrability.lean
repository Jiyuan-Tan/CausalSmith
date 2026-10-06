module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenSmoothing
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! # Integrability of the four Gaussian Prawitz spectral terms

Finite first moment cancels the low-frequency characteristic-function
discrepancy. The principal correction is bounded, and the two remaining
terms stay away from zero. These analytic side conditions are separated
from Gaussian sine inversion and the final signed spectral comparison.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a probability law with finite first moment](hyp:μ,hfirst) and
[positive ordered cutoffs U0 ≤ U](hyp:U0,U,hU0,hcut), [each of the four
Prawitz spectral integrands is integrable on its frequency region: the
filtered characteristic-function discrepancy on [0, U0], the filtered
characteristic-function modulus on [U0, U], the Gaussian principal
correction on [0, U0], and the Gaussian tail integrand on (U0, ∞)](goal). -/
theorem prawitz_four_terms_integrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ)
    (U0 U : ℝ) (hU0 : 0 < U0) (hcut : U0 ≤ U) :
    IntervalIntegrable (fun t : ℝ =>
      ‖prawitzKernel (t / U)‖ *
        ‖charFun μ t - charFun (gaussianReal 0 1) t‖) volume 0 U0 ∧
    IntervalIntegrable (fun t : ℝ =>
      ‖prawitzKernel (t / U)‖ * ‖charFun μ t‖) volume U0 U ∧
    IntervalIntegrable (fun t : ℝ =>
      ‖prawitzKernel (t / U) / (U : ℂ) -
        Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
        Real.exp (-(t ^ 2 / 2))) volume 0 U0 ∧
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) / t)
      (Set.Ioi U0) := by
  have hU : 0 < U := hU0.trans_le hcut
  -- The total piecewise formula is measurable, including its assigned endpoints.
  have hkernel : Measurable prawitzKernel := by
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact Measurable.ite measurableSet_Iio measurable_const
        (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
    unfold prawitzKernel
    apply Measurable.ite
    · exact (measurableSet_eq_fun measurable_id measurable_const).union
        (measurableSet_lt measurable_const (measurable_id.abs))
    · fun_prop
    · fun_prop
  have hscaled : Measurable (fun t : ℝ => prawitzKernel (t / U)) :=
    hkernel.comp (by fun_prop)
  have hband (t : ℝ) (ht : 0 < t) (htU : t ≤ U) :
      0 < |t / U| ∧ |t / U| ≤ 1 := by
    rw [abs_of_pos (div_pos ht hU)]
    exact ⟨div_pos ht hU, (div_le_one hU).mpr htU⟩
  have hkbound (t : ℝ) (ht : 0 < t) (htU : t ≤ U) :
      ‖prawitzKernel (t / U)‖ ≤ U / (2 * Real.pi) / t + 1 / 2 := by
    have hb := prawitzKernel_norm_le (t / U) (hband t ht htU).1
      (hband t ht htU).2
    rw [abs_of_pos (div_pos ht hU)] at hb
    convert hb using 1
    field_simp
  have hquot : IntervalIntegrable (fun t : ℝ =>
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) volume 0 U0 := by
    apply (charFun_normal_quotient_intervalIntegrable μ hfirst U0).mono_set
    rw [Set.uIcc_of_le hU0.le, Set.uIcc_of_le (by linarith : -U0 ≤ U0)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hdiff : IntervalIntegrable (fun t : ℝ =>
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖) volume 0 U0 := by
    exact ((continuous_charFun (μ := μ)).sub
      (continuous_charFun (μ := gaussianReal 0 1))).norm.intervalIntegrable 0 U0
  -- Ioc domains exclude zero a.e. without assuming continuity of the kernel.
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hU0.le).mpr
    apply ((hquot.const_mul (U / (2 * Real.pi))).add
      (hdiff.const_mul (1 / 2))).1.mono'
    · exact ((hscaled.norm).mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      have hb := mul_le_mul_of_nonneg_right
        (hkbound t ht.1 (ht.2.trans hcut))
        (norm_nonneg (charFun μ t - charFun (gaussianReal 0 1) t))
      rw [abs_of_pos ht.1]
      convert hb using 1 <;> first | rfl | ring
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hcut).mpr
    apply (intervalIntegrable_const (c := U / (2 * Real.pi) / U0 + 1 / 2)
      (a := U0) (b := U) (μ := volume)).1.mono'
    · exact (hscaled.norm.mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc
        _ ≤ ‖prawitzKernel (t / U)‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_charFun_le_one t) (norm_nonneg _)
        _ ≤ U / (2 * Real.pi) / t + 1 / 2 := by
          simpa using hkbound t (hU0.trans ht.1) ht.2
        _ ≤ U / (2 * Real.pi) / U0 + 1 / 2 := by
          gcongr
          exact ht.1.le
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hU0.le).mpr
    apply (intervalIntegrable_const (c := 1 / (2 * U))
      (a := 0) (b := U0) (μ := volume)).1.mono'
    · have hm : Measurable (fun t : ℝ =>
          ‖prawitzKernel (t / U) / (U : ℂ) -
            Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
            Real.exp (-(t ^ 2 / 2))) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have heq : prawitzKernel (t / U) / (U : ℂ) -
          Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
          (prawitzKernel (t / U) -
            Complex.I / ((2 * Real.pi * (t / U) : ℝ) : ℂ)) / (U : ℂ) := by
        push_cast
        have hUc : (U : ℂ) ≠ 0 := by exact_mod_cast hU.ne'
        field_simp [hUc]
      have hb := prawitzKernel_principal_correction_norm_le (t / U)
        (hband t ht.1 (ht.2.trans hcut)).1 (hband t ht.1 (ht.2.trans hcut)).2
      have hc : ‖prawitzKernel (t / U) / (U : ℂ) -
          Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤ 1 / (2 * U) := by
        rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU]
        calc
          _ ≤ (1 / 2) / U := (div_le_div_iff_of_pos_right hU).mpr hb
          _ = _ := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
      calc
        _ ≤ (1 / (2 * U)) * Real.exp (-(t ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
        _ ≤ (1 / (2 * U)) * 1 := by
          gcongr
          apply Real.exp_le_one_iff.mpr
          exact neg_nonpos.mpr (by positivity)
        _ = _ := mul_one _
  · have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) volume := by
      convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
      funext t
      congr 1
      ring
    apply (hg.div_const U0).integrableOn.mono'
    · exact (by fun_prop : Measurable (fun t : ℝ =>
        Real.exp (-(t ^ 2 / 2)) / t)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (hU0.trans ht))]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hU0 ht.le

end Causalean.Stat.CLT.BerryEsseen
