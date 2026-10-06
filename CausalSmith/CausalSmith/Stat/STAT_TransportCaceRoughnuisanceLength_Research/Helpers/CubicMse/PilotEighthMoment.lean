module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotSecondMoment
public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

/-! # Eighth-moment closure for the exact clipped pilot

The bounded iid sum theorem cancels singleton index patterns and counts the
survivors. Scaling the bin sums, transferring them to the two-sample experiment,
and applying clipping and the dyadic resolution bounds gives equation (5).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Normalize the exact eighth-moment bound for a bounded iid bin sum.  Under [the displayed assumptions and inputs](hyp:Ω,n,K,S,hS,hK,f,hf,hb,V,hV,hv), [the stated conclusion holds](goal). -/
-- @node: iidBlockHeight_eighth_moment_le
lemma iidBlockHeight_eighth_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n K : ℕ}
    (S : Finset (Fin n)) (hS : 0 < S.card) (hK : 0 < K)
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ y, f y ∈ Icc (0 : ℝ) 1)
    (V : ℝ) (hV : 0 ≤ V) (hv : variance f μ ≤ V / K) :
    (∫ x, (iidBlockHeight K S f x - (K : ℝ) * ∫ y, f y ∂μ) ^ 8
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      (Nat.factorial 8 : ℝ) *
        (V ^ 4 * ((K : ℝ) / S.card) ^ 4 + V * ((K : ℝ) / S.card) ^ 7) := by
  have hm : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hid (x : Fin n → Ω) :
      iidBlockHeight K S f x - (K : ℝ) * ∫ y, f y ∂μ =
        ((K : ℝ) / S.card) * ∑ r ∈ S, (f (x r) - ∫ y, f y ∂μ) := by
    simp only [iidBlockHeight, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  simp_rw [hid, mul_pow]
  rw [integral_const_mul]
  have hsum := Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.iid_centered_bounded_sum_eighth_moment μ f hf (fun y => (hb y).1)
      (fun y => (hb y).2) S
  have hvar0 := variance_nonneg f μ
  have hscaled := mul_le_mul_of_nonneg_left hv hm.le
  have hpow := pow_le_pow_left₀ (mul_nonneg hm.le hvar0) hscaled 4
  calc
    _ ≤ ((K : ℝ) / S.card) ^ 8 * ((Nat.factorial 8 : ℝ) *
        (((S.card : ℝ) * variance f μ) ^ 4 + (S.card : ℝ) * variance f μ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((K : ℝ) / S.card) ^ 8 * ((Nat.factorial 8 : ℝ) *
        (((S.card : ℝ) * (V / K)) ^ 4 + (S.card : ℝ) * (V / K))) := by
      gcongr
    _ = _ := by field_simp <;> ring

/-- The one-record covariance envelope implies the roadmap's variance factor.  Under [the displayed assumptions and inputs](hyp:C,K,hK), [the stated conclusion holds](goal). -/
-- @node: bin_variance_envelope_le
lemma bin_variance_envelope_le (C : ℝ) {K : ℕ} (hK : 0 < K) :
    C / K + (C / K) ^ 2 ≤ (1 + C + C ^ 2) / K := by
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  apply (le_div_iff₀ hk).2
  field_simp
  nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hk1)]

/-- The exact source bin height has the eighth-moment bound in equation (3).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l,i), [the stated conclusion holds](goal). -/
-- @node: source_bin_height_eighth_moment_le
lemma source_bin_height_eighth_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (l : Fin K) (i : Fin 7) :
    (∫ x, (iidBlockHeight K S (sourceCellScore i K l) x -
      (K : ℝ) * ∫ o, sourceCellScore i K l o ∂sourceObsLaw P) ^ 8
      ∂Measure.pi (fun _ : Fin n => sourceObsLaw P)) ≤
      (Nat.factorial 8 : ℝ) *
        ((1 + C_f + C_f ^ 2) ^ 4 * ((K : ℝ) / S.card) ^ 4 +
          (1 + C_f + C_f ^ 2) * ((K : ℝ) / S.card) ^ 7) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  have hv := source_same_cell_covariance_le c_f C_f L P n K hP hK l i i
  rw [covariance_self (measurable_sourceCellScore i K l).aemeasurable] at hv
  apply iidBlockHeight_eighth_moment_le S hS hK _ (measurable_sourceCellScore i K l)
    (sourceCellScore_mem_unit_interval i K l) _
  · nlinarith [sq_nonneg C_f]
  · exact (le_abs_self _).trans (hv.trans (bin_variance_envelope_le C_f hK))

/-- The exact target bin height has the eighth-moment bound in equation (3).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l), [the stated conclusion holds](goal). -/
-- @node: target_bin_height_eighth_moment_le
lemma target_bin_height_eighth_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (l : Fin K) :
    (∫ x, (iidBlockHeight K S (targetCellScore K l) x -
      (K : ℝ) * ∫ o, targetCellScore K l o ∂targetXLaw P) ^ 8
      ∂Measure.pi (fun _ : Fin n => targetXLaw P)) ≤
      (Nat.factorial 8 : ℝ) *
        ((1 + C_f + C_f ^ 2) ^ 4 * ((K : ℝ) / S.card) ^ 4 +
          (1 + C_f + C_f ^ 2) * ((K : ℝ) / S.card) ^ 7) := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hv := target_same_cell_covariance_le c_f C_f L P n K hP hK l
  rw [covariance_self (measurable_targetCellScore K l).aemeasurable] at hv
  apply iidBlockHeight_eighth_moment_le S hS hK _ (measurable_targetCellScore K l)
    (targetCellScore_mem_unit_interval K l) _
  · nlinarith [sq_nonneg C_f]
  · exact (le_abs_self _).trans (hv.trans (bin_variance_envelope_le C_f hK))

/-- Transfer the eighth bin moment to the actual source sample channel.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,b,l,i,hi), [the stated conclusion holds](goal). -/
-- @node: source_markedHistogram_eighth_moment_le
lemma source_markedHistogram_eighth_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (l : Fin K) (i : Fin 7) (hi : i ≠ 0) :
    (∫ w, (markedHistogram w i K b (midpoint K l) - cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) ^ 8
      ∂dataLaw P n n) ≤ (Nat.factorial 8 : ℝ) *
      ((1 + C_f + C_f ^ 2) ^ 4 * ((K : ℝ) / blockSize n b) ^ 4 +
        (1 + C_f + C_f ^ 2) * ((K : ℝ) / blockSize n b) ^ 7) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hcard : 0 < (blockIdx n b).card := by
    rw [block_card]
    exact blockSize_pos_of_threshold n hn b
  have hmean : (K : ℝ) * (∫ o, sourceCellScore i K l o ∂sourceObsLaw P) =
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l := by
    rw [sourceCellScore_integral_eq_density c_f C_f L P n K hP hK l i hi]
    rfl
  simp_rw [markedHistogram_midpoint_source hn hK _ i hi]
  rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
  let g := fun x : Fin n → SourceObs =>
    (iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) x - cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) ^ 8
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hp := measurePreserving_fst
    (μ := Measure.pi (fun _ : Fin n => sourceObsLaw P))
    (ν := Measure.pi (fun _ : Fin n => targetXLaw P))
  have hm : AEStronglyMeasurable g
      (((Measure.pi (fun _ : Fin n => sourceObsLaw P)).prod
        (Measure.pi (fun _ : Fin n => targetXLaw P))).map Prod.fst) := by
    rw [hp.map_eq]
    exact hg.aestronglyMeasurable
  have htransfer := (integral_map hp.measurable.aemeasurable hm).symm
  rw [hp.map_eq] at htransfer
  change (∫ w, g w.1 ∂(Measure.pi (fun _ : Fin n => sourceObsLaw P)).prod
    (Measure.pi (fun _ : Fin n => targetXLaw P))) ≤ _
  rw [htransfer]
  have h := source_bin_height_eighth_moment_le c_f C_f L P n K hP hK
    (blockIdx n b) hcard l i
  simpa only [g, hmean, block_card] using h


/-- Transfer the eighth bin moment to the actual target sample channel.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,b,l), [the stated conclusion holds](goal). -/
-- @node: target_markedHistogram_eighth_moment_le
lemma target_markedHistogram_eighth_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (l : Fin K) :
    (∫ w, (markedHistogram w 0 K b (midpoint K l) - cellAverage P.fT K l) ^ 8
      ∂dataLaw P n n) ≤ (Nat.factorial 8 : ℝ) *
      ((1 + C_f + C_f ^ 2) ^ 4 * ((K : ℝ) / blockSize n b) ^ 4 +
        (1 + C_f + C_f ^ 2) * ((K : ℝ) / blockSize n b) ^ 7) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hcard : 0 < (blockIdx n b).card := by
    rw [block_card]
    exact blockSize_pos_of_threshold n hn b
  have hmean : (K : ℝ) * (targetXLaw P (cell K l)).toReal = cellAverage P.fT K l := by
    change (K : ℝ) * (targetXLaw P).real (cell K l) = _
    rw [← integral_indicator_one (measurableSet_cell K l)]
    change (K : ℝ) * (∫ y, targetCellScore K l y ∂targetXLaw P) = _
    rw [targetCellScore_integral_eq_density c_f C_f L P n K hP hK]
    rfl
  simp_rw [markedHistogram_midpoint_target hn hK]
  rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
  let g := fun x : Fin n → ℝ =>
    (iidBlockHeight K (blockIdx n b) (targetCellScore K l) x - cellAverage P.fT K l) ^ 8
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hp := measurePreserving_snd
    (μ := Measure.pi (fun _ : Fin n => sourceObsLaw P))
    (ν := Measure.pi (fun _ : Fin n => targetXLaw P))
  have hm : AEStronglyMeasurable g
      (((Measure.pi (fun _ : Fin n => sourceObsLaw P)).prod
        (Measure.pi (fun _ : Fin n => targetXLaw P))).map Prod.snd) := by
    rw [hp.map_eq]
    exact hg.aestronglyMeasurable
  have htransfer := (integral_map hp.measurable.aemeasurable hm).symm
  rw [hp.map_eq] at htransfer
  change (∫ w, g w.2 ∂(Measure.pi (fun _ : Fin n => sourceObsLaw P)).prod
    (Measure.pi (fun _ : Fin n => targetXLaw P))) ≤ _
  rw [htransfer]
  have h := target_bin_height_eighth_moment_le c_f C_f L P n K hP hK
    (blockIdx n b) hcard l
  have hscoreMean : (∫ y, targetCellScore K l y ∂targetXLaw P) =
      (targetXLaw P (cell K l)).toReal :=
    integral_indicator_one (measurableSet_cell K l)
  rw [hscoreMean] at h
  simpa only [g, hmean, block_card] using h


/-- All seven observable histogram channels obey equation (3).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,b,l,i), [the stated conclusion holds](goal). -/
-- @node: markedHistogram_eighth_moment_le
lemma markedHistogram_eighth_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (l : Fin K) (i : Fin 7) :
    (∫ w, (markedHistogram w i K b (midpoint K l) -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) ^ 8
      ∂dataLaw P n n) ≤ (Nat.factorial 8 : ℝ) *
      ((1 + C_f + C_f ^ 2) ^ 4 * ((K : ℝ) / blockSize n b) ^ 4 +
        (1 + C_f + C_f ^ 2) * ((K : ℝ) / blockSize n b) ^ 7) := by
  by_cases hi : i = 0
  · subst i
    simpa only [markedDensityVector, Matrix.cons_val_zero] using
      target_markedHistogram_eighth_moment_le c_f C_f L P n K hn hP hK b l
  · exact source_markedHistogram_eighth_moment_le c_f C_f L P n K hn hP hK b l i hi


/-- The bounded histogram makes its centered eighth power integrable for every fixed cell.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,l,c), [the stated conclusion holds](goal). -/
-- @node: integrable_markedHistogram_centered_eighth
lemma integrable_markedHistogram_centered_eighth (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 7) (b : Fin 4) (l : Fin K) (c : ℝ) :
    Integrable (fun w : TwoSample n n =>
      |markedHistogram w i K b (midpoint K l) - c| ^ 8) (dataLaw P n n) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hprob : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  letI := hprob
  apply (integrable_const (((K : ℝ) + |c|) ^ 8)).mono'
  · fun_prop
  · filter_upwards [] with w
    have hb := markedHistogram_mem_Icc hn hK w i b l
    have hab : |markedHistogram w i K b (midpoint K l) - c| ≤ K + |c| :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg hb.1]; linarith [hb.2])
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hab 8

-- @node: pilot_eighth_moment
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,i,x,hx), [the stated result about pilot eighth moment holds](goal). -/
lemma pilot_eighth_moment (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 7) (x : ℝ) (hx : x ∈ covariateSpace) :
    (∫ ω, |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ)
      ∂dataLaw P n n) ≤
      pilotEighthConstant C_f L * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  obtain ⟨l, hl⟩ := exists_cell_of_mem_covariateSpace hK x hx
  let m := cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i)
    (pilotResolution n) l
  let V := 1 + C_f + C_f ^ 2
  let B := 2 ^ (8 : ℕ) * (3 * (1 + C_f) * L) ^ (8 : ℕ) *
    (5 : ℝ) ^ (4 / 5 : ℝ) * (n : ℝ) ^ (-(4 / 5 : ℝ))
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hprob : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]; infer_instance
  letI := hprob
  have hi := integrable_markedHistogram_centered_eighth c_f C_f L P n
    (pilotResolution n) hn hP hK i 0 l m
  have hp (w : TwoSample n n) :=
    pilot_error_eighth_sample_rate_split c_f C_f L P n hn hP w l x hl i
  simp_rw [markedHistogram_eq_midpoint_on_cell hK _ i 0 l x hl] at hp
  have hbound := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun w => pow_nonneg (abs_nonneg _) 8))
    ((hi.const_mul (2 ^ (7 : ℕ))).add (integrable_const B))
    (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hi.const_mul (2 ^ (7 : ℕ))) (integrable_const B),
    integral_const_mul, integral_const] at hbound
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hbound
  have heven (z : ℝ) : |z| ^ (8 : ℕ) = z ^ (8 : ℕ) := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sq_abs, ← pow_mul]
  simp_rw [heven] at hbound ⊢
  have hv := markedHistogram_eighth_moment_le c_f C_f L P n (pilotResolution n)
    hn hP hK 0 l i
  have hscales := pilotResolution_eighth_fluctuation_scales n hn
  have hV : 0 ≤ V := by dsimp [V]; nlinarith [sq_nonneg (C_f + 1 / 2)]
  have hfluct := add_le_add
    (mul_le_mul_of_nonneg_left hscales.1 (pow_nonneg hV 4))
    (mul_le_mul_of_nonneg_left hscales.2 hV)
  have hscaled := mul_le_mul_of_nonneg_left hfluct
    (show 0 ≤ (2 : ℝ) ^ (7 : ℕ) * (Nat.factorial 8 : ℝ) by positivity)
  calc
    _ ≤ 2 ^ (7 : ℕ) * (∫ w,
        (markedHistogram w i (pilotResolution n) 0 (midpoint (pilotResolution n) l) - m) ^ 8
          ∂dataLaw P n n) + B := hbound
    _ ≤ 2 ^ (7 : ℕ) * ((Nat.factorial 8 : ℝ) *
        (V ^ 4 * ((pilotResolution n : ℝ) / blockSize n 0) ^ 4 +
          V * ((pilotResolution n : ℝ) / blockSize n 0) ^ 7)) + B :=
      add_le_add (mul_le_mul_of_nonneg_left hv
        (show (0 : ℝ) ≤ 2 ^ (7 : ℕ) by norm_num)) le_rfl
    _ ≤ pilotEighthConstant C_f L * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
      dsimp [pilotEighthConstant, V, B] at hscaled ⊢
      nlinarith only [hscaled]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
