module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactFluctuation

/-! # Final mean-square assembly for the exact cubic estimator -/

public section

open MeasureTheory
open Causalean.Mathlib.Probability.Independence
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The pilot plug-in integral only uses the training sample.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,A), [the stated conclusion holds](goal). -/
@[fun_prop]
lemma stronglyMeasurable_pilotIntegral (c_f C_f : ℝ) (n : ℕ) (A : Bool) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => pilotIntegral c_f C_f ω A) := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  have heq (ω : TwoSample n n) :
      pilotIntegral c_f C_f ω A =
        (pilotResolution n : ℝ)⁻¹ * ∑ l : Fin (pilotResolution n),
          Phi A (pilot c_f C_f ω (midpoint (pilotResolution n) l)) := by
    rw [pilotIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← integral_Icc_eq_integral_Ioc]
    simpa [covariateSpace] using
      integral_pilot_composition_eq_cell_sum c_f C_f hK (dvd_refl _) ω (Phi A)
  simp_rw [heq]
  apply stronglyMeasurable_const.mul
  apply Finset.stronglyMeasurable_fun_sum
  intro l _
  unfold Phi
  fun_prop

/-- The exact projected estimator mean only uses the training sample.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
@[fun_prop]
lemma stronglyMeasurable_projectedEstimatorMean
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => projectedEstimatorMean c_f C_f L P n hP ω A) := by
  unfold projectedEstimatorMean
  exact (((stronglyMeasurable_pilotIntegral c_f C_f n A).add
    (stronglyMeasurable_linearProjectionMean c_f C_f L P n hn hP A)).add
    (stronglyMeasurable_quadraticProjectionMean c_f C_f L P n hn hP A)).add
    (stronglyMeasurable_cubicProjectionMean c_f C_f L P n hn hP A)

/-- The squared error of the exact projected mean is integrable.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma integrable_projectedEstimatorMean_sub_transport_sq
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    Integrable (fun ω : TwoSample n n =>
      (projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A) ^ 2)
      (dataLaw P n n) := by
  let μ := dataLaw P n n
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  let H := 3 * (1 + C_f) * L
  let M := fourthDerivativeEnvelope c_f C_f
  let A2 := 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
    (2 : ℝ) ^ (5 / 4 : ℝ) * H ^ 2 * (5 : ℝ) ^ (1 / 5 : ℝ)
  let BQ := (7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
    (5 : ℝ) ^ (2 / 3 : ℝ)
  let C1 := (M / 2) * (7 : ℝ) ^ 2 * H ^ 2
  let C2 := (M / 6) * (7 : ℝ) ^ 3 * H ^ 3
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
  have hSp (ω : TwoSample n n) :
      spatialCubicProjectionBias c_f C_f L P n hP ω A ^ 2 ≤ S ω := by
    have habs := cubic_spatial_projection_bias_abs_le_L1 c_f C_f L P n hn hP ω A
    have habs' : |spatialCubicProjectionBias c_f C_f L P n hP ω A| ≤
        a * ∑ i : Fin 7, e i ω + b := by
      convert habs using 1 <;> first | rfl | dsimp [a, b, C1, C2, H, M, q]; ring
    have hp := pow_le_pow_left₀ (abs_nonneg _) habs' 2
    rw [sq_abs] at hp
    have hs : (∑ i : Fin 7, e i ω) ^ 2 ≤ (7 : ℝ) * ∑ i : Fin 7, e i ω ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun i : Fin 7 => e i ω))
    have hw := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * a ^ 2)
    dsimp only [S]
    nlinarith [sq_nonneg (a * ∑ i : Fin 7, e i ω - b)]
  have hRi :=
    (pilotRemainderMajorant_integrable_sq_and_moment c_f C_f L P n hn hP).1
  have hmajorant : Integrable (fun ω =>
      3 * (pilotRemainderMajorant c_f C_f L P n hP ω ^ 2 + BQ * rate + S ω)) μ :=
    (((hRi.add (integrable_const _)).add hS).const_mul _)
  have hm : trainingSigma n ≤ (inferInstance : MeasurableSpace (TwoSample n n)) := by
    rw [trainingSigma_eq_comap_flatTrainingProj]
    exact ((measurable_finsetCoordProj (flatBlock n 0)).comp
      (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable).comap_le
  refine hmajorant.mono' ?_ ?_
  · exact ((((stronglyMeasurable_projectedEstimatorMean c_f C_f L P n hn hP A).mono hm).sub
      stronglyMeasurable_const).pow 2).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      projectedEstimatorMean_sub_transport_eq_spatial_bias, neg_sq]
    apply (sq_three_bias_terms_le _ _ _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add _ (hSp ω)
    apply add_le_add _
      (quadraticCellProjectionBias_sq_sample_rate c_f C_f L P n hn hP ω A)
    simpa only [sq_abs, spatialTaylorRemainder] using pow_le_pow_left₀ (abs_nonneg _)
      (pilot_remainder_integral_abs_le_majorant c_f C_f L P n hn hP A ω) 2

/-- A variable minus its conditional expectation is conditionally centered.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,hm,X,hX), [the stated conclusion holds](goal). -/
lemma condExp_sub_condExp_eq_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Integrable X μ) :
    condExp m μ (X - condExp m μ X) =ᵐ[μ] (0 : Ω → ℝ) := by
  have hceint : Integrable (condExp m μ X) μ := integrable_condExp
  have hsub := condExp_sub hX hceint m
  have htower := condExp_condExp_of_le (μ := μ) (f := X) (le_refl m) hm
  filter_upwards [hsub, htower] with ω hsubω htowerω
  rw [hsubω]
  change condExp m μ X ω - condExp m μ (condExp m μ X) ω = 0
  rw [htowerω]
  simp

/-- Integrability follows from square integrability after conditional centering.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,X,hX), [the stated conclusion holds](goal). -/
lemma integrable_of_sub_condExp_memLp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp (fun ω => X ω - condExp m μ X ω) 2 μ) : Integrable X μ := by
  by_contra hn
  have hzero := condExp_of_not_integrable (m := m) hn
  have heq : (fun ω => X ω - condExp m μ X ω) =ᵐ[μ] X := by
    filter_upwards [] with ω
    rw [hzero]
    simp
  exact hn ((hX.integrable (by norm_num)).congr heq)

/-- The exact estimator fluctuation has zero training-conditional mean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma condExp_cubicEstimator_sub_projectedEstimatorMean_eq_zero
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    condExp (trainingSigma n) (dataLaw P n n)
      (fun ω : TwoSample n n => cubicEstimator c_f C_f ω A -
        projectedEstimatorMean c_f C_f L P n hP ω A) =ᵐ[dataLaw P n n]
      (0 : TwoSample n n → ℝ) := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  have hm : trainingSigma n ≤ (inferInstance : MeasurableSpace (TwoSample n n)) := by
    rw [trainingSigma_eq_comap_flatTrainingProj]
    exact ((measurable_finsetCoordProj (flatBlock n 0)).comp
      (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable).comap_le
  let Xl := fun ω : TwoSample n n => linearTerm c_f C_f ω A
  let Xq := fun ω : TwoSample n n => quadraticTerm c_f C_f ω A
  let Xc := fun ω : TwoSample n n => cubicTerm c_f C_f ω A
  let Zl := fun ω => Xl ω - condExp (trainingSigma n) (dataLaw P n n) Xl ω
  let Zq := fun ω => Xq ω - condExp (trainingSigma n) (dataLaw P n n) Xq ω
  let Zc := fun ω => Xc ω - condExp (trainingSigma n) (dataLaw P n n) Xc ω
  have hlp := (linear_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
  have hqp := (quadratic_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
  have hcp := (cubic_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
  have hli : Integrable Xl (dataLaw P n n) :=
    integrable_of_sub_condExp_memLp (trainingSigma n) (dataLaw P n n) (by simpa [Xl] using hlp)
  have hqi : Integrable Xq (dataLaw P n n) := hqp.integrable (by norm_num)
  have hci : Integrable Xc (dataLaw P n n) := hcp.integrable (by norm_num)
  have hzli : Integrable Zl (dataLaw P n n) := hli.sub integrable_condExp
  have hzqi : Integrable Zq (dataLaw P n n) := hqi.sub integrable_condExp
  have hzci : Integrable Zc (dataLaw P n n) := hci.sub integrable_condExp
  have hzl0' := condExp_sub_condExp_eq_zero (trainingSigma n) (dataLaw P n n) hm hli
  have hzq0' := condExp_sub_condExp_eq_zero (trainingSigma n) (dataLaw P n n) hm hqi
  have hzc0' := condExp_sub_condExp_eq_zero (trainingSigma n) (dataLaw P n n) hm hci
  have hzl0 : condExp (trainingSigma n) (dataLaw P n n) Zl =ᵐ[dataLaw P n n]
      (0 : TwoSample n n → ℝ) := by
    apply (condExp_congr_ae _).trans hzl0'
    filter_upwards [] with ω
    rfl
  have hzq0 : condExp (trainingSigma n) (dataLaw P n n) Zq =ᵐ[dataLaw P n n]
      (0 : TwoSample n n → ℝ) := by
    apply (condExp_congr_ae _).trans hzq0'
    filter_upwards [] with ω
    rfl
  have hzc0 : condExp (trainingSigma n) (dataLaw P n n) Zc =ᵐ[dataLaw P n n]
      (0 : TwoSample n n → ℝ) := by
    apply (condExp_congr_ae _).trans hzc0'
    filter_upwards [] with ω
    rfl
  have hsum : condExp (trainingSigma n) (dataLaw P n n)
      (fun ω => Zl ω + Zq ω + Zc ω) =ᵐ[dataLaw P n n]
      condExp (trainingSigma n) (dataLaw P n n) Zl +
        condExp (trainingSigma n) (dataLaw P n n) Zq +
        condExp (trainingSigma n) (dataLaw P n n) Zc :=
    (condExp_add (hzli.add hzqi) hzci (trainingSigma n)).trans
      ((condExp_add hzli hzqi (trainingSigma n)).add
        (Filter.Eventually.of_forall fun _ => rfl))
  have hsum0 : condExp (trainingSigma n) (dataLaw P n n)
      (fun ω => Zl ω + Zq ω + Zc ω) =ᵐ[dataLaw P n n]
      (0 : TwoSample n n → ℝ) := by
    filter_upwards [hsum, hzl0, hzq0, hzc0] with ω hs hl hq hc
    rw [hs]
    change condExp (trainingSigma n) (dataLaw P n n) Zl ω +
      condExp (trainingSigma n) (dataLaw P n n) Zq ω +
      condExp (trainingSigma n) (dataLaw P n n) Zc ω = 0
    rw [hl, hq, hc]
    simp
  exact (condExp_congr_ae
    (cubicEstimator_sub_projectedEstimatorMean_eq_centered_corrections
      c_f C_f L P n hn hP A)).trans hsum0

/-- The fluctuation is orthogonal to the training-measurable projected bias.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma integral_projected_bias_mul_fluctuation_eq_zero
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A) *
      (cubicEstimator c_f C_f ω A - projectedEstimatorMean c_f C_f L P n hP ω A)
      ∂dataLaw P n n) = 0 := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  let μ := dataLaw P n n
  let F := fun ω : TwoSample n n => cubicEstimator c_f C_f ω A -
    projectedEstimatorMean c_f C_f L P n hP ω A
  let B := fun ω : TwoSample n n =>
    projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A
  have hm : trainingSigma n ≤ (inferInstance : MeasurableSpace (TwoSample n n)) := by
    rw [trainingSigma_eq_comap_flatTrainingProj]
    exact ((measurable_finsetCoordProj (flatBlock n 0)).comp
      (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable).comap_le
  have hF : MemLp F 2 μ :=
    cubicEstimator_sub_projectedEstimatorMean_memLp c_f C_f L P n hn hP A
  have hBsm : StronglyMeasurable[trainingSigma n] B := by
    dsimp [B]
    exact (stronglyMeasurable_projectedEstimatorMean c_f C_f L P n hn hP A).sub
      stronglyMeasurable_const
  have hB : MemLp B 2 μ := by
    apply (memLp_two_iff_integrable_sq (μ := μ) (hBsm.mono hm).aestronglyMeasurable).2
    simpa [B, μ] using
      integrable_projectedEstimatorMean_sub_transport_sq c_f C_f L P n hn hP A
  have hprod : Integrable (B * F) μ := hB.integrable_mul hF
  have hpull := condExp_mul_of_stronglyMeasurable_left hBsm hprod
    (hF.integrable (by norm_num))
  have hF0 := condExp_cubicEstimator_sub_projectedEstimatorMean_eq_zero
    c_f C_f L P n hn hP A
  calc
    (∫ ω, B ω * F ω ∂μ) =
        ∫ ω, condExp (trainingSigma n) μ (B * F) ω ∂μ :=
      (integral_condExp (μ := μ) (f := B * F) hm).symm
    _ = ∫ ω, B ω * condExp (trainingSigma n) μ F ω ∂μ := integral_congr_ae hpull
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hF0] with ω hω
      rw [hω]
      simp

/-- Squared error is the sum of fluctuation risk and projected squared bias.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma cubicEstimator_mse_eq_fluctuation_add_projected_bias
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2
      ∂dataLaw P n n) =
    (∫ ω, (cubicEstimator c_f C_f ω A -
      projectedEstimatorMean c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) +
    ∫ ω, (projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A) ^ 2
      ∂dataLaw P n n := by
  let μ := dataLaw P n n
  let F := fun ω : TwoSample n n => cubicEstimator c_f C_f ω A -
    projectedEstimatorMean c_f C_f L P n hP ω A
  let B := fun ω : TwoSample n n =>
    projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A
  have hF : MemLp F 2 μ :=
    cubicEstimator_sub_projectedEstimatorMean_memLp c_f C_f L P n hn hP A
  have hBi : Integrable (fun ω => B ω ^ 2) μ := by
    simpa [B, μ] using
      integrable_projectedEstimatorMean_sub_transport_sq c_f C_f L P n hn hP A
  have hBsm : AEStronglyMeasurable B μ := by
    let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
    let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
    have hm : trainingSigma n ≤ (inferInstance : MeasurableSpace (TwoSample n n)) := by
      rw [trainingSigma_eq_comap_flatTrainingProj]
      exact ((measurable_finsetCoordProj (flatBlock n 0)).comp
        (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable).comap_le
    exact (((stronglyMeasurable_projectedEstimatorMean c_f C_f L P n hn hP A).mono hm).sub
      stronglyMeasurable_const).aestronglyMeasurable
  have hB : MemLp B 2 μ := (memLp_two_iff_integrable_sq hBsm).2 hBi
  have hcross : (∫ ω, B ω * F ω ∂μ) = 0 := by
    simpa [B, F, μ] using
      integral_projected_bias_mul_fluctuation_eq_zero c_f C_f L P n hn hP A
  have hexpand (ω : TwoSample n n) :
      (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2 =
        F ω ^ 2 + B ω ^ 2 + 2 * (B ω * F ω) := by
    dsimp [F, B]
    ring
  calc
    _ = ∫ ω, (F ω ^ 2 + B ω ^ 2 + 2 * (B ω * F ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hexpand ω
    _ = (∫ ω, F ω ^ 2 ∂μ) + (∫ ω, B ω ^ 2 ∂μ) +
        2 * ∫ ω, B ω * F ω ∂μ := by
      have hadd1 := integral_add (hF.integrable_sq.add hBi)
        ((hB.integrable_mul hF).const_mul 2)
      have hadd2 := integral_add hF.integrable_sq hBi
      simp only [Pi.add_apply, Pi.mul_apply] at hadd1 hadd2
      rw [hadd1, hadd2, integral_const_mul]
    _ = _ := by rw [hcross]; ring

/-- The exact fluctuation and projected-bias bounds assemble to the frozen
mean-square envelope.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma cubicEstimator_mse_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2
      ∂dataLaw P n n) ≤
      mseEnvelope c_f C_f L * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  let V := 3 * (10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 +
    60 * quadVarianceConstant c_f C_f + 310 * cubicVarianceConstant c_f C_f)
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
  let B := 3 * (BR + BQ + BC)
  have hv : (∫ ω, (cubicEstimator c_f C_f ω A -
      projectedEstimatorMean c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) ≤
      V * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    exact cubicEstimator_fluctuation_second_moment_sample_rate c_f C_f L P n hn hP A
  have hb : (∫ ω, (projectedEstimatorMean c_f C_f L P n hP ω A -
      transportedForm P A) ^ 2 ∂dataLaw P n n) ≤
      B * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    exact projectedEstimatorMean_squared_bias_sample_rate c_f C_f L P n hn hP A
  have hconst : V + B = mseEnvelope c_f C_f L := by
    dsimp [V, B, BR, BQ, BC, C1, C2, A2, H, M]
    unfold mseEnvelope pilotEighthConstant quadVarianceConstant cubicVarianceConstant
      fourthDerivativeEnvelope
    dsimp only
    ring
  rw [cubicEstimator_mse_eq_fluctuation_add_projected_bias
    c_f C_f L P n hn hP A]
  calc
    _ ≤ V * (n : ℝ) ^ (-(2 / 3 : ℝ)) +
        B * (n : ℝ) ^ (-(2 / 3 : ℝ)) := add_le_add hv hb
    _ = (V + B) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
    _ = _ := by rw [hconst]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
