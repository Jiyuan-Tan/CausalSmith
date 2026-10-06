module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.ProjectionFieldMoments
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TLocalCovarianceBias

/-! Conditional tail bounds paired with the smooth propensity in the numerator bias. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- An almost-everywhere window envelope controls its normalized integral. -/
-- @node: upper_normalized_integral_bound_ae
lemma upper_normalized_integral_bound_ae (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (f : unitInterval → ℝ) (C : ℝ)
    (hb : ∀ᵐ x ∂(design.restrict (window h)), |f x| ≤ C) :
    |h⁻¹ * ∫ x in window h, f x ∂design| ≤ C := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hnorm : ∀ᵐ x ∂(design.restrict (window h)), ‖f x‖ ≤ C :=
    hb.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx
  have hn := norm_integral_le_of_norm_le_const hnorm
  have hmass : (design.restrict (window h)).real univ = h := by
    simp [Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
  rw [hmass, Real.norm_eq_abs] at hn
  rw [abs_mul, abs_of_pos (inv_pos.mpr hh.1)]
  calc
    _ ≤ h⁻¹ * (C * h) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hh.1.le)
    _ = C := by field_simp [hh.1.ne']

/-- The armwise raw moment envelope bounds the treated conditional truncation error. -/
-- @node: upper_treated_truncation_bound
lemma upper_treated_truncation_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (T : ℝ) (hT : 1 ≤ T) :
    ∀ᵐ x ∂design,
      |law.e x * ((∫ y, trunc T y ∂law.Q true x) - law.m1 x)| ≤ 10*T^(1-κ.p) := by
  have hmean := law.mean1_version
  rw [hm.uniform] at hmean
  filter_upwards [hm.conditionalMoment, hmean] with x hx hm1
  have ht := (truncation_moment_bounds κ.p T hκ.1 hT (law.Q true x) (hx true)).2.2.1
  change |law.e x * ((∫ y, trunc T y ∂law.Q true x) - (law.m0 x + law.tau x))| ≤ _
  rw [hm1, abs_mul, abs_of_nonneg (law.e_range x).1]
  have hb : |(∫ y, trunc T y ∂law.Q true x) - ∫ y, y ∂law.Q true x| ≤
      10*T^(1-κ.p) := by simpa only [abs_sub_comm] using ht
  calc
    _ ≤ law.e x * (10*T^(1-κ.p)) := mul_le_mul_of_nonneg_left hb (law.e_range x).1
    _ ≤ 10*T^(1-κ.p) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (law.e_range x).2
        (by positivity : 0 ≤ 10*T^(1-κ.p))

/-- The localized raw treated term contributes one conditional tail envelope. -/
-- @node: upper_treated_truncation_integral_bound
lemma upper_treated_truncation_integral_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (T : ℝ) (hT : 1 ≤ T) :
    |h⁻¹ * ∫ x in window h,
      law.e x * ((∫ y, trunc T y ∂law.Q true x) - law.m1 x) ∂design| ≤
      10*T^(1-κ.p) := by
  exact upper_normalized_integral_bound_ae h hh _ _
    (ae_restrict_of_ae (upper_treated_truncation_bound κ hκ law hm T hT))

/-- The coarse projected propensity contributes one marginal conditional tail envelope. -/
-- @node: upper_coarse_truncation_integral_bound
lemma upper_coarse_truncation_integral_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (T : ℝ) (hT : 1 ≤ T) :
    |h⁻¹ * ∫ x in window h,
      projOp h 0 law.e x * (truncatedMean law T x-law.g x) ∂design| ≤
      10*T^(1-κ.p) := by
  have he := covariance_memLp_of_bound h law.e law.e_measurable 20 hm.propensityHolder.2.1
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  apply upper_normalized_integral_bound_ae h hh
  filter_upwards [ae_restrict_of_ae (marginal_mean_truncation_bounds κ hκ law hm T hT),
    ae_restrict_mem hw] with x hx hxw
  have hp := covariance_projOp_range h hh 0 law.e he 0 1 law.e_range x hxw
  rw [abs_mul, abs_of_nonneg hp.1]
  calc
    _ ≤ projOp h 0 law.e x * (10*T^(1-κ.p)) := mul_le_mul_of_nonneg_left hx.2.2 hp.1
    _ ≤ 10*T^(1-κ.p) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp.2
        (by positivity : 0 ≤ 10*T^(1-κ.p))

/-- Each positive band pairs a conditional tail envelope with propensity oscillation. -/
-- @node: upper_band_truncation_integral_bound
lemma upper_band_truncation_integral_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1) (he : holderBall a law.e)
    (j : ℕ) (hj : 1 ≤ j) (T : ℝ) (hT : 1 ≤ T) :
    |h⁻¹ * ∫ x in window h,
      bandOp h j law.e x * (truncatedMean law T x-law.g x) ∂design| ≤
      400 * cellLen h j^a * T^(1-κ.p) := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hd : 0 < cellLen h j := by unfold cellLen; exact div_pos hh.1 (by positivity)
  apply upper_normalized_integral_bound_ae h hh
  filter_upwards [ae_restrict_of_ae (marginal_mean_truncation_bounds κ hκ law hm T hT),
    ae_restrict_mem hw] with x hx hxw
  rw [abs_mul]
  calc
    _ ≤ (40*cellLen h j^a) * (10*T^(1-κ.p)) :=
      mul_le_mul (bandOp_holder_bound h hh a law.e ha he j hj x hxw) hx.2.2
        (abs_nonneg _) (by positivity)
    _ = 400 * cellLen h j^a * T^(1-κ.p) := by ring

/-- The raw, coarse, and band truncation errors give exactly the public numerator
truncation ledger, without imposing any regularity on clipped conditional means. -/
-- @node: upper_conditional_truncation_bias
lemma upper_conditional_truncation_bias (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1) (he : holderBall a law.e)
    (J : ℕ) (T : Fin (J + 1) → ℝ) (hT : ∀ j, 1 ≤ T j) :
    |(h⁻¹ * ∫ x in window h,
        law.e x * ((∫ y, trunc (T 0) y ∂law.Q true x)-law.m1 x) ∂design) -
      (h⁻¹ * ∫ x in window h,
        projOp h 0 law.e x * (truncatedMean law (T 0) x-law.g x) ∂design) -
      ∑ j : Fin J, h⁻¹ * ∫ x in window h,
        bandOp h (j.val+1) law.e x *
          (truncatedMean law (T j.succ) x-law.g x) ∂design| ≤
      20*T 0^(1-κ.p) + 400*(∑ j : Fin J, cellLen h (j.val+1)^a*T j.succ^(1-κ.p)) := by
  have hr := upper_treated_truncation_integral_bound κ hκ law hm h hh (T 0) (hT 0)
  have hc := upper_coarse_truncation_integral_bound κ hκ law hm h hh (T 0) (hT 0)
  have hb (j : Fin J) := upper_band_truncation_integral_bound κ hκ law hm h hh
    a ha he (j.val+1) (by omega) (T j.succ) (hT j.succ)
  calc
    _ ≤ |(h⁻¹ * ∫ x in window h,
          law.e x * ((∫ y, trunc (T 0) y ∂law.Q true x)-law.m1 x) ∂design) -
        (h⁻¹ * ∫ x in window h,
          projOp h 0 law.e x * (truncatedMean law (T 0) x-law.g x) ∂design)| +
        |∑ j : Fin J, h⁻¹ * ∫ x in window h,
          bandOp h (j.val+1) law.e x *
            (truncatedMean law (T j.succ) x-law.g x) ∂design| := abs_sub _ _
    _ ≤ (10*T 0^(1-κ.p)+10*T 0^(1-κ.p)) +
        ∑ j : Fin J, 400*cellLen h (j.val+1)^a*T j.succ^(1-κ.p) := by
      apply add_le_add
      · exact (abs_sub _ _).trans (add_le_add hr hc)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hb j)
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
