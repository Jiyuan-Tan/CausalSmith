module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicProjectionBias
public import Mathlib.Algebra.Order.Chebyshev

/-! # Second moment of the exact cubic projection bias

The spatial L1 pilot moments and the exact single-residual cancellation
bound give the squared cubic bias, retaining both resolution powers in
roadmap (13) before dyadic sample-rate conversion.
-/

public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Squaring an affine finite-error bound costs twice the squared offset
and twice the coordinate count times the sum of coordinate second moments.  Under [the displayed assumptions and inputs](hyp:Ω,r,e,a,b,R,he,hm,hr), [the stated conclusion holds](goal). -/
-- @node: affine_seven_error_second_moment
lemma affine_seven_error_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ℝ) (e : Fin 7 → Ω → ℝ) (a b R : ℝ)
    (he : ∀ i, Integrable (fun ω => e i ω ^ 2) μ)
    (hm : ∀ i, (∫ ω, e i ω ^ 2 ∂μ) ≤ R)
    (hr : ∀ ω, |r ω| ≤ a * ∑ i, e i ω + b) :
    (∫ ω, r ω ^ 2 ∂μ) ≤ 2 * a ^ 2 * (7 : ℝ) ^ 2 * R + 2 * b ^ 2 := by
  have hpoint (ω : Ω) : r ω ^ 2 ≤
      2 * a ^ 2 * 7 * (∑ i, e i ω ^ 2) + 2 * b ^ 2 := by
    have hs : (∑ i, e i ω) ^ 2 ≤ (7 : ℝ) * ∑ i, e i ω ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin 7 => e i ω))
    have hp := pow_le_pow_left₀ (abs_nonneg (r ω)) (hr ω) 2
    rw [sq_abs] at hp
    have hw := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * a ^ 2)
    nlinarith [sq_nonneg (a * ∑ i, e i ω - b)]
  calc
    _ ≤ ∫ ω, 2 * a ^ 2 * 7 * (∑ i, e i ω ^ 2) + 2 * b ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        (((integrable_finsetSum Finset.univ (fun i _ => he i)).const_mul _).add
          (integrable_const _))
      exact Filter.Eventually.of_forall hpoint
    _ = 2 * a ^ 2 * 7 * (∑ i, ∫ ω, e i ω ^ 2 ∂μ) + 2 * b ^ 2 := by
      rw [integral_add ((integrable_finsetSum Finset.univ (fun i _ => he i)).const_mul _)
        (integrable_const _), integral_const_mul,
        integral_finsetSum Finset.univ (fun i _ => he i)]
      simp
    _ ≤ 2 * a ^ 2 * 7 * (∑ _i : Fin 7, R) + 2 * b ^ 2 := by
      gcongr
      exact hm i
    _ = _ := by simp; ring

/-- Dyadic rounding and the exact block size control every nonnegative
power of the inverse cubic resolution, with the constants in roadmap (13).  Under [the displayed assumptions and inputs](hyp:n,hn,p,hp), [the stated conclusion holds](goal). -/
-- @node: cubicResolution_inverse_rpow_sample_rate
lemma cubicResolution_inverse_rpow_sample_rate (n : ℕ) (hn : threshold ≤ n)
    (p : ℝ) (hp : 0 ≤ p) :
    (1 / (cubicResolution n : ℝ)) ^ p ≤
      (2 : ℝ) ^ p * (5 : ℝ) ^ p * (n : ℝ) ^ (-p) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hl : (n : ℝ) / 5 / 2 ≤ (cubicResolution n : ℝ) := by
    have h := (dyadicResolution_power_bounds n hn 1 (by norm_num)).1
    simp only [Real.rpow_one] at h
    exact (div_le_div_of_nonneg_right (block_size_lower n hn 0) (by norm_num)).trans h
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) / 5 / 2)
    hl (neg_nonpos.mpr hp)
  calc
    _ = (cubicResolution n : ℝ) ^ (-p) := by
      rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
        Real.rpow_neg (by positivity)]
      simp only [one_div]
    _ ≤ ((n : ℝ) / 5 / 2) ^ (-p) := h
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num),
        Real.div_rpow hnpos.le (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp

/-- The squared spatial L1 pilot error is integrable: joint measurability
and clipping provide a uniform bound on the unit covariate interval.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,i), [the stated conclusion holds](goal). -/
-- @node: integrable_pilot_error_L1_sq
lemma integrable_pilot_error_L1_sq (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (i : Fin 7) :
    Integrable (fun ω => (∫ x in covariateSpace,
      |markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i|) ^ 2)
      (dataLaw P n n) := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]; infer_instance
  let ν := volume.restrict covariateSpace
  let : IsProbabilityMeasure ν := ⟨by simp [ν, covariateSpace]⟩
  let F := covariateSpace.indicator
    (fun x => markedDensityVector c_f C_f L P n hP x i)
  let g := fun (ω : TwoSample n n) (x : ℝ) => |F x - pilot c_f C_f ω x i|
  have hg : Measurable (Function.uncurry g) := by
    have hF := measurable_markedDensityVector_indicator c_f C_f L P n hP i
    dsimp [g, Function.uncurry]
    fun_prop
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hb (ω : TwoSample n n) : ∀ᵐ x ∂ν, |g ω x| ≤ 2 * C_f := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    dsimp [g, F]
    rw [Set.indicator_of_mem hx, abs_abs]
    simpa only [two_mul] using (abs_sub _ _).trans (add_le_add
      (clippingRectangle_coordinate_abs_le c_f C_f hP.sourceBounds.1.1 hC _
        (markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx) i)
      (clippingRectangle_coordinate_abs_le c_f C_f hP.sourceBounds.1.1 hC _
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x) i))
  have heq (ω : TwoSample n n) :
      (∫ x in covariateSpace,
        |markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i|) =
      ∫ x, g ω x ∂ν := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    dsimp [g, F]
    rw [Set.indicator_of_mem hx]
  simp_rw [heq]
  apply Integrable.of_bound (hg.stronglyMeasurable.integral_prod_right.pow 2).aestronglyMeasurable
    ((2 * C_f) ^ 2)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have habs : |∫ x, g ω x ∂ν| ≤ 2 * C_f :=
    (abs_integral_le_integral_abs.trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (integrable_const (2 * C_f)) (hb ω))).trans_eq (by simp)
  simpa only [sq_abs, Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- The exact spatial cubic bias has the two second-moment terms of
roadmap (13): the squared resolution modulus times the pilot L1 rate,
and the sixth power of that modulus. No stochastic content is assumed.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubic_spatial_projection_bias_integrated_sq_resolution_bound
lemma cubic_spatial_projection_bias_integrated_sq_resolution_bound
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    let B := 3 * (1 + C_f) * L * (1 / (cubicResolution n : ℝ)) ^ holderExponent
    let a := (fourthDerivativeEnvelope c_f C_f / 2) * (7 : ℝ) ^ 2 * B ^ 2
    let b := (fourthDerivativeEnvelope c_f C_f / 6) * (7 : ℝ) ^ 3 * B ^ 3
    let A2 := 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
      (2 : ℝ) ^ (5 / 4 : ℝ) * (3 * (1 + C_f) * L) ^ 2 * (5 : ℝ) ^ (1 / 5 : ℝ)
    (∫ ω, ((∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∫ x in covariateSpace,
        (dPhi3 A (pilot c_f C_f ω x) i j k / 6) *
          (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
          (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j) *
          (markedDensityVector c_f C_f L P n hP x k - pilot c_f C_f ω x k)) -
        cubicProjectionMean c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) ≤
      2 * a ^ 2 * (7 : ℝ) ^ 2 * (A2 * (n : ℝ) ^ (-(1 / 5 : ℝ))) + 2 * b ^ 2 := by
  dsimp only
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]; infer_instance
  apply affine_seven_error_second_moment (dataLaw P n n)
    _ (fun i ω => ∫ x in covariateSpace,
      |markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i|)
  · exact fun i => integrable_pilot_error_L1_sq c_f C_f L P n hn hP i
  · intro i
    simpa only [abs_sub_comm] using pilot_error_L1_second_moment c_f C_f L P n hn hP i
  · intro ω
    exact cubic_spatial_projection_bias_abs_le_L1 c_f C_f L P n hn hP ω A

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
