module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicBiasRate
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.RemainderMajorant
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SpatialProjectionBridge

/-! # Combined spatial Taylor and projection bias

This module proves roadmap (14) for the exact integrated Taylor remainder
and the exact quadratic and cubic projection errors, with constant 3(BR+BQ+BC).
The identification with the full statistic's conditional bias remains separate.
-/

@[expose] public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The integrated exact third-order Taylor remainder.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated object is defined](goal). -/
-- @node: spatialTaylorRemainder
noncomputable def spatialTaylorRemainder (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) : ℝ :=
  ∫ x in covariateSpace,
    (let v := pilot c_f C_f ω x
     let h := markedDensityVector c_f C_f L P n hP x - v
     Phi A (markedDensityVector c_f C_f L P n hP x) - (Phi A v +
       iteratedFDeriv ℝ 1 (Phi A) v ![h] +
       iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
       iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6))

/-- The spatial cubic Taylor term minus its exact projection mean.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated object is defined](goal). -/
-- @node: spatialCubicProjectionBias
noncomputable def spatialCubicProjectionBias (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) : ℝ :=
  (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∫ x in covariateSpace,
    (dPhi3 A (pilot c_f C_f ω x) i j k / 6) *
      (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
      (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j) *
      (markedDensityVector c_f C_f L P n hP x k - pilot c_f C_f ω x k)) -
    cubicProjectionMean c_f C_f L P n hP ω A

/-- Three real summands cost at most three times their squared norms.  Under [the displayed assumptions and inputs](hyp:r,q,c), [the stated conclusion holds](goal). -/
-- @node: sq_three_bias_terms_le
lemma sq_three_bias_terms_le (r q c : ℝ) :
    (r + q + c) ^ 2 ≤ 3 * (r ^ 2 + q ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (r - q), sq_nonneg (r - c), sq_nonneg (q - c)]

/-- Roadmap (14): the exact spatial Taylor remainder plus the quadratic
and cubic projection errors has the paper's combined squared-bias bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: combined_spatial_projection_bias_second_moment
lemma combined_spatial_projection_bias_second_moment
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    let H := 3 * (1 + C_f) * L
    let M := fourthDerivativeEnvelope c_f C_f
    let A2 := 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
      (2 : ℝ) ^ (5 / 4 : ℝ) * H ^ 2 * (5 : ℝ) ^ (1 / 5 : ℝ)
    let BR := (M / 24) ^ 2 * (7 : ℝ) ^ (8 : ℕ) * pilotEighthConstant C_f L
    let BQ := (7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (5 : ℝ) ^ (2 / 3 : ℝ)
    let C1 := (M / 2) * (7 : ℝ) ^ 2 * H ^ 2
    let C2 := (M / 6) * (7 : ℝ) ^ 3 * H ^ 3
    let BC := 2 * (C1 ^ 2 * (7 : ℝ) ^ 2 * A2 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (5 : ℝ) ^ (1 / 2 : ℝ) + C2 ^ 2 * (2 : ℝ) ^ (3 / 4 : ℝ) *
      (5 : ℝ) ^ (3 / 4 : ℝ))
    (∫ ω, (spatialTaylorRemainder c_f C_f L P n hP ω A +
      quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A +
      spatialCubicProjectionBias c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) ≤
      3 * (BR + BQ + BC) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  dsimp only
  let μ := dataLaw P n n
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]; infer_instance
  let H := 3 * (1 + C_f) * L
  let M := fourthDerivativeEnvelope c_f C_f
  let A2 := 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
    (2 : ℝ) ^ (5 / 4 : ℝ) * H ^ 2 * (5 : ℝ) ^ (1 / 5 : ℝ)
  let BR := (M / 24) ^ 2 * (7 : ℝ) ^ (8 : ℕ) * pilotEighthConstant C_f L
  let BQ := (7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
    (5 : ℝ) ^ (2 / 3 : ℝ)
  let C1 := (M / 2) * (7 : ℝ) ^ 2 * H ^ 2
  let C2 := (M / 6) * (7 : ℝ) ^ 3 * H ^ 3
  let BC := 2 * (C1 ^ 2 * (7 : ℝ) ^ 2 * A2 * (2 : ℝ) ^ (1 / 2 : ℝ) *
    (5 : ℝ) ^ (1 / 2 : ℝ) + C2 ^ 2 * (2 : ℝ) ^ (3 / 4 : ℝ) * (5 : ℝ) ^ (3 / 4 : ℝ))
  let rate := (n : ℝ) ^ (-(2 / 3 : ℝ))
  let q := 1 / (cubicResolution n : ℝ)
  let a := C1 * (q ^ holderExponent) ^ 2
  let b := C2 * (q ^ holderExponent) ^ 3
  let e (i : Fin 7) (ω : TwoSample n n) := ∫ x in covariateSpace,
    |markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i|
  let S (ω : TwoSample n n) := 2 * a ^ 2 * 7 * (∑ i : Fin 7, e i ω ^ 2) + 2 * b ^ 2
  have he (i : Fin 7) : Integrable (fun ω => e i ω ^ 2) μ :=
    integrable_pilot_error_L1_sq c_f C_f L P n hn hP i
  have hS : Integrable S μ :=
    ((integrable_finsetSum Finset.univ (fun i _ => he i)).const_mul _).add
      (integrable_const _)
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hA2 : 0 ≤ A2 := by dsimp [A2]; positivity
  have hSm : (∫ ω, S ω ∂μ) ≤ BC * rate := by
    calc
      _ = 2 * a ^ 2 * 7 * (∑ i : Fin 7, ∫ ω, e i ω ^ 2 ∂μ) + 2 * b ^ 2 := by
        dsimp only [S]
        rw [integral_add ((integrable_finsetSum Finset.univ (fun i _ => he i)).const_mul _)
          (integrable_const _), integral_const_mul,
          integral_finsetSum Finset.univ (fun i _ => he i)]
        simp
      _ ≤ 2 * a ^ 2 * 7 * (∑ _i : Fin 7, A2 * (n : ℝ) ^ (-(1 / 5 : ℝ))) +
          2 * b ^ 2 := by
        gcongr
        simpa only [e, A2, H, abs_sub_comm] using
          pilot_error_L1_second_moment c_f C_f L P n hn hP i
      _ = 2 * a ^ 2 * (7 : ℝ) ^ 2 * (A2 * (n : ℝ) ^ (-(1 / 5 : ℝ))) +
          2 * b ^ 2 := by simp; ring
      _ ≤ _ := cubic_bias_resolution_terms_sample_rate n hn C1 C2 A2 hA2
  have hSp (ω : TwoSample n n) : spatialCubicProjectionBias c_f C_f L P n hP ω A ^ 2 ≤ S ω := by
    have habs := cubic_spatial_projection_bias_abs_le_L1 c_f C_f L P n hn hP ω A
    have habs' : |spatialCubicProjectionBias c_f C_f L P n hP ω A| ≤
        a * ∑ i : Fin 7, e i ω + b := by
      convert habs using 1 <;> first | rfl | dsimp [a, b, C1, C2, H, M, q]; ring
    have hp := pow_le_pow_left₀ (abs_nonneg _) habs' 2
    rw [sq_abs] at hp
    have hs : (∑ i : Fin 7, e i ω) ^ 2 ≤ (7 : ℝ) * ∑ i : Fin 7, e i ω ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 7 => e i ω))
    have hw := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * a ^ 2)
    dsimp only [S]
    nlinarith [sq_nonneg (a * ∑ i : Fin 7, e i ω - b)]
  have hRm := pilotRemainderMajorant_sample_rate c_f C_f L P n hn hP
  have hRi := (pilotRemainderMajorant_integrable_sq_and_moment c_f C_f L P n hn hP).1
  calc
    _ ≤ ∫ ω, 3 * (pilotRemainderMajorant c_f C_f L P n hP ω ^ 2 + BQ * rate + S ω) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        (((hRi.add (integrable_const _)).add hS).const_mul _)
      filter_upwards [] with ω
      apply (sq_three_bias_terms_le _ _ _).trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add _ (hSp ω)
      apply add_le_add _ (quadraticCellProjectionBias_sq_sample_rate c_f C_f L P n hn hP ω A)
      simpa only [sq_abs, spatialTaylorRemainder] using pow_le_pow_left₀ (abs_nonneg _)
        (pilot_remainder_integral_abs_le_majorant c_f C_f L P n hn hP A ω) 2
    _ = 3 * ((∫ ω, pilotRemainderMajorant c_f C_f L P n hP ω ^ 2 ∂μ) +
        BQ * rate + ∫ ω, S ω ∂μ) := by
      have hadd := integral_add (hRi.add (integrable_const (BQ * rate))) hS
      have hadd2 := integral_add hRi (integrable_const (BQ * rate))
      simp only [Pi.add_apply] at hadd hadd2
      rw [integral_const_mul]
      rw [hadd, hadd2]
      simp [μ]
    _ ≤ 3 * (BR * rate + BQ * rate + BC * rate) := by
      gcongr
    _ = _ := by ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
