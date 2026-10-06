module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TruncationMoments
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Conditional first moments and truncation-error energies for the observable field. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Integrating a clipped response against either original Borel kernel is measurable. -/
-- @node: measurable_truncatedMean
@[fun_prop] lemma measurable_truncatedMean (law : ObservedLaw) (T : ℝ) :
    Measurable (truncatedMean law T) := by
  unfold truncatedMean
  have hi (a : Bool) : Measurable (fun x => ∫ y, trunc T y ∂law.Q a x) := by
    first | fun_prop | exact (measurable_trunc T).stronglyMeasurable.integral_kernel.measurable
  exact (law.e_measurable.mul (hi true)).add
    ((measurable_const.sub law.e_measurable).mul (hi false))

/-- The original marginal mean and each clipped mean are bounded by the raw moment envelope,
and their difference has the conditional tail bound. -/
-- @node: marginal_mean_truncation_bounds
lemma marginal_mean_truncation_bounds (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (T : ℝ) (hT : 1 ≤ T) :
    ∀ᵐ x ∂design, |law.g x| ≤ (10 : ℝ)^(1/κ.p) ∧
      |truncatedMean law T x| ≤ (10 : ℝ)^(1/κ.p) ∧
      |truncatedMean law T x-law.g x| ≤ 10*T^(1-κ.p) := by
  have h0 := law.mean0_version
  have h1 := law.mean1_version
  rw [hm.uniform] at h0 h1
  filter_upwards [hm.conditionalMoment, h0, h1] with x hx hx0 hx1
  have hbound (a : Bool) := truncation_moment_bounds κ.p T hκ.1 hT (law.Q a x) (hx a)
  have hclip (a : Bool) : |∫ y, trunc T y ∂law.Q a x| ≤ (10 : ℝ)^(1/κ.p) := by
    have hi : Integrable (trunc T) (law.Q a x) := by
      apply (hbound a).1.mono (by fun_prop)
      exact Filter.Eventually.of_forall fun y => by
        by_cases hy : |y| ≤ T <;> simp [trunc, hy, Real.norm_eq_abs]
    -- Apply the first-moment comparison to the clipped response's distribution.
    have hmap : ∫⁻ y, ENNReal.ofReal (|y|^κ.p) ∂(law.Q a x).map (trunc T) ≤ 10 := by
      rw [lintegral_map (by fun_prop) (by fun_prop)]
      apply le_trans (lintegral_mono (fun y => ?_)) (hx a)
      by_cases hy : |y| ≤ T
      · simp [trunc, hy]
      · simp [trunc, hy, Real.zero_rpow (by linarith [hκ.1.1] : κ.p ≠ 0)]
    letI : IsProbabilityMeasure ((law.Q a x).map (trunc T)) := Measure.isProbabilityMeasure_map (by fun_prop)
    have hc := truncation_moment_bounds κ.p T hκ.1 hT ((law.Q a x).map (trunc T)) hmap
    rw [integral_map (by fun_prop) (by fun_prop)] at hc
    exact hc.2.1
  have he := law.e_range x
  have hg : law.g x = law.e x * (∫ y, y ∂law.Q true x) +
      (1-law.e x) * (∫ y, y ∂law.Q false x) := by
    rw [← hx0, ← hx1]
    unfold ObservedLaw.g
    ring
  have hmix (u v C : ℝ) (hu : |u| ≤ C) (hv : |v| ≤ C) :
      |law.e x*u+(1-law.e x)*v| ≤ C := by
    calc
      _ ≤ |law.e x*u|+|(1-law.e x)*v| := abs_add_le _ _
      _ = law.e x*|u|+(1-law.e x)*|v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg he.1, abs_of_nonneg (sub_nonneg.mpr he.2)]
      _ ≤ law.e x*C+(1-law.e x)*C := add_le_add
        (mul_le_mul_of_nonneg_left hu he.1) (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr he.2))
      _ = C := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact hmix _ _ _ (hbound true).2.1 (hbound false).2.1
  · exact hmix _ _ _ (hclip true) (hclip false)
  · have hd : truncatedMean law T x-law.g x =
        law.e x*((∫ y, trunc T y ∂law.Q true x)-(∫ y, y ∂law.Q true x)) +
        (1-law.e x)*((∫ y, trunc T y ∂law.Q false x)-(∫ y, y ∂law.Q false x)) := by
      rw [hg]; unfold truncatedMean; ring
    rw [hd]
    apply hmix
    · simpa only [abs_sub_comm] using (hbound true).2.2.1
    · simpa only [abs_sub_comm] using (hbound false).2.2.1

/-- An almost-everywhere absolute envelope bounds the unnormalized window energy. -/
-- @node: window_energy_of_abs_bound
lemma window_energy_of_abs_bound (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (f : unitInterval → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ᵐ x ∂design, |f x| ≤ C) :
    MemLp f 2 (design.restrict (window h)) ∧
      (∫ x in window h, (f x)^2 ∂design) ≤ h*C^2 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hlp : MemLp f 2 (design.restrict (window h)) := by
    apply MemLp.of_bound (by fun_prop) C
    exact (ae_restrict_of_ae hb).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx
  refine ⟨hlp, ?_⟩
  calc
    _ ≤ ∫ _x in window h, C^2 ∂design := by
      apply integral_mono_ae hlp.integrable_sq (integrable_const _)
      filter_upwards [ae_restrict_of_ae hb] with x hx
      have hc : 0 ≤ C := (abs_nonneg _).trans hx
      have ha := abs_le.mp hx
      nlinarith [sq_nonneg (C-f x), sq_nonneg (C+f x)]
    _ = h*C^2 := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
      simp only [smul_eq_mul, mul_comm]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
