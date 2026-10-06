module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotSampling

/-! # The clipped pilot's second-moment rate

The exact bin variance and Hölder projection bias give equation (5)'s
second-moment bound, with the constant A₂ used in the cubic projection bias.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Histogram heights are constant throughout each cell, including its endpoint convention.  Under [the displayed assumptions and inputs](hyp:n,K,hK,w,i,b,l,x,hx), [the stated conclusion holds](goal). -/
-- @node: markedHistogram_eq_midpoint_on_cell
lemma markedHistogram_eq_midpoint_on_cell {n K : ℕ} (hK : 0 < K)
    (w : TwoSample n n) (i : Fin 7) (b : Fin 4) (l : Fin K)
    (x : ℝ) (hx : x ∈ cell K l) :
    markedHistogram w i K b x = markedHistogram w i K b (midpoint K l) := by
  classical
  have hmem (r : Fin K) : x ∈ cell K r ↔ r = l := by
    constructor
    · intro hr
      by_contra hne
      exact Set.disjoint_left.mp (cell_disjoint hK hne) hr hx
    · rintro rfl
      exact hx
  unfold markedHistogram
  simp_rw [hmem, midpoint_mem_cell_iff hK]

/-- At a fixed point, the bounded bin statistic is measurable in the data.  Under [the displayed assumptions and inputs](hyp:n,i,K,b,x), [the stated conclusion holds](goal). -/
@[fun_prop]
-- @node: measurable_markedHistogram
lemma measurable_markedHistogram {n : ℕ} (i : Fin 7) (K : ℕ) (b : Fin 4) (x : ℝ) :
    Measurable (fun w : TwoSample n n => markedHistogram w i K b x) := by
  classical
  unfold markedHistogram
  split_ifs
  · fun_prop
  · apply Finset.measurable_sum
    intro l hl
    split_ifs
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro r hr
      apply Measurable.mul (measurable_channelMark i r)
      exact Measurable.ite ((measurableSet_cell K l).preimage
        (measurable_channelX i r)) measurable_const measurable_const
    · fun_prop

/-- A cell histogram lies between zero and its normalization K.  Under [the displayed assumptions and inputs](hyp:n,K,hn,hK,w,i,b,l), [the stated conclusion holds](goal). -/
-- @node: markedHistogram_mem_Icc
lemma markedHistogram_mem_Icc {n K : ℕ} (hn : threshold ≤ n) (hK : 0 < K)
    (w : TwoSample n n) (i : Fin 7) (b : Fin 4) (l : Fin K) :
    markedHistogram w i K b (midpoint K l) ∈ Icc (0 : ℝ) K := by
  classical
  have hm : (0 : ℝ) < blockSize n b :=
    Nat.cast_pos.mpr (blockSize_pos_of_threshold n hn b)
  have hscore (r : Fin n) :
      channelMark w i r * (if channelX w i r ∈ cell K l then 1 else 0) ∈ Icc (0 : ℝ) 1 := by
    split_ifs <;> simp_all [channelMark_mem_unit_interval w i r]
  have hs0 : 0 ≤ ∑ r ∈ blockIdx n b,
      channelMark w i r * (if channelX w i r ∈ cell K l then 1 else 0) :=
    Finset.sum_nonneg (fun r _ => (hscore r).1)
  have hs1 : (∑ r ∈ blockIdx n b,
      channelMark w i r * (if channelX w i r ∈ cell K l then 1 else 0)) ≤ blockSize n b := by
    calc
      _ ≤ ∑ _r ∈ blockIdx n b, (1 : ℝ) := Finset.sum_le_sum (fun r _ => (hscore r).2)
      _ = _ := by simp [block_card]
  unfold markedHistogram
  rw [if_neg (Nat.not_lt_of_ge hn), Finset.sum_eq_single l]
  · rw [if_pos (midpoint_mem_cell hK l)]
    constructor
    · exact mul_nonneg (div_nonneg (by positivity) hm.le) hs0
    · calc
        _ ≤ (K : ℝ) / blockSize n b * blockSize n b :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
        _ = K := by field_simp
  · intro r _ hr
    rw [if_neg (fun h => hr ((midpoint_mem_cell_iff hK l r).mp h))]
  · simp

/-- Fixed centered histogram squares are integrable; their deterministic bound supplies regularity.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,l,c), [the stated conclusion holds](goal). -/
-- @node: integrable_markedHistogram_centered_sq
lemma integrable_markedHistogram_centered_sq (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 7) (b : Fin 4) (l : Fin K) (c : ℝ) :
    Integrable (fun w : TwoSample n n =>
      (markedHistogram w i K b (midpoint K l) - c) ^ 2) (dataLaw P n n) := by
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hprob : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  let := hprob
  apply (integrable_const (((K : ℝ) + |c|) ^ 2)).mono'
  · fun_prop
  · filter_upwards [] with w
    have hb := markedHistogram_mem_Icc hn hK w i b l
    have hab : |markedHistogram w i K b (midpoint K l) - c| ≤ K + |c| := by
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hb.1]; linarith [hb.2])
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hab 2

/-- Clipping, bin variance, and the exact Hölder cell bias control pilot risk before rate substitution.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,i,l,x,hx), [the stated conclusion holds](goal). -/
-- @node: pilot_second_moment_cell_bound
lemma pilot_second_moment_cell_bound (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (i : Fin 7)
    (l : Fin (pilotResolution n)) (x : ℝ) (hx : x ∈ cell (pilotResolution n) l) :
    (∫ w, (pilot c_f C_f w x i - markedDensityVector c_f C_f L P n hP x i) ^ 2
      ∂dataLaw P n n) ≤
      2 * (1 + C_f + C_f ^ 2) * pilotResolution n / blockSize n 0 +
      2 * (3 * (1 + C_f) * L) ^ 2 * (1 / (pilotResolution n : ℝ)) ^ (1 / 4 : ℝ) := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  let m := cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i)
    (pilotResolution n) l
  let F := markedDensityVector c_f C_f L P n hP x i
  let B := 3 * (1 + C_f) * L * (1 / (pilotResolution n : ℝ)) ^ holderExponent
  have hb : |m - F| ≤ B := markedDensityVector_cell_bias c_f C_f L P n
    (pilotResolution n) hP hK l x hx i
  have hp (w : TwoSample n n) :
      (pilot c_f C_f w x i - F) ^ 2 ≤
        2 * (markedHistogram w i (pilotResolution n) 0 (midpoint (pilotResolution n) l) - m) ^ 2 + 2 * B ^ 2 := by
    have hc := pilot_error_le_histogram_error c_f C_f L P n hn hP w x
      (cell_subset_covariateSpace hK l hx) i
    have hsplit := abs_sub_le (markedHistogram w i (pilotResolution n) 0 x) m F
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hc 2
    have htriangle := pow_le_pow_left₀ (abs_nonneg _) hsplit 2
    have hsum := add_pow_le (abs_nonneg (markedHistogram w i (pilotResolution n) 0 x - m))
      (abs_nonneg (m - F)) 2
    have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    change |pilot c_f C_f w x i - F| ≤ |markedHistogram w i (pilotResolution n) 0 x - F| at hc
    rw [markedHistogram_eq_midpoint_on_cell hK w i 0 l x hx] at hpow htriangle hsum
    change |pilot c_f C_f w x i - F| ^ 2 ≤
      |markedHistogram w i (pilotResolution n) 0 (midpoint (pilotResolution n) l) - F| ^ 2 at hpow
    simp only [sq_abs, Nat.reduceSub, pow_one] at hpow htriangle hsum hb2
    nlinarith
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hprob : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]; infer_instance
  let := hprob
  have hi := integrable_markedHistogram_centered_sq c_f C_f L P n
    (pilotResolution n) hn hP hK i 0 l m
  have hbound := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun w => sq_nonneg (pilot c_f C_f w x i - F)))
    ((hi.const_mul 2).add (integrable_const (2 * B ^ 2)))
    (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hi.const_mul 2) (integrable_const (2 * B ^ 2)),
    integral_const_mul, integral_const] at hbound
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hbound
  have hv := markedHistogram_second_moment_le c_f C_f L P n (pilotResolution n)
    hn hP hK 0 l i
  have hB : B ^ 2 = (3 * (1 + C_f) * L) ^ 2 *
      (1 / (pilotResolution n : ℝ)) ^ (1 / 4 : ℝ) := by
    dsimp [B]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity :
      0 ≤ 1 / (pilotResolution n : ℝ))]
    norm_num [holderExponent]
  rw [hB] at hbound
  dsimp [m] at hbound
  refine hbound.trans ?_
  convert add_le_add_right (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2))
    (2 * ((3 * (1 + C_f) * L) ^ 2 * (1 / (pilotResolution n : ℝ)) ^ (1 / 4 : ℝ))) using 1 <;> ring

/-- The dyadic pilot bias has the exact second-moment constant from equation (6).  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: pilot_second_bias_scale_le
lemma pilot_second_bias_scale_le (n : ℕ) (hn : threshold ≤ n) :
    2 * (1 / (pilotResolution n : ℝ)) ^ (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (5 / 4 : ℝ) * (5 : ℝ) ^ (1 / 5 : ℝ) *
        (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / (pilotResolution n : ℝ))
    (pilotResolution_inv_le_sample_rate n hn) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5),
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)] at h
  norm_num at h
  have htwo : (2 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  rw [← mul_assoc 2, ← mul_assoc 2, htwo] at hscaled
  simpa only [one_div, mul_assoc] using hscaled

/-- Every covariate belongs to a histogram cell; the final cell includes one.  Under [the displayed assumptions and inputs](hyp:K,hK,x,hx), [the stated conclusion holds](goal). -/
-- @node: exists_cell_of_mem_covariateSpace
lemma exists_cell_of_mem_covariateSpace {K : ℕ} (hK : 0 < K)
    (x : ℝ) (hx : x ∈ covariateSpace) : ∃ l : Fin K, x ∈ cell K l := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  change 0 ≤ x ∧ x ≤ 1 at hx
  by_cases hx1 : x = 1
  · refine ⟨⟨K - 1, by omega⟩, ?_⟩
    have hlast : K - 1 + 1 = K := by omega
    simp only [cell, hlast, if_true, Set.mem_Icc, hx1]
    constructor
    · apply (div_le_one hKr).2
      exact_mod_cast (show K - 1 ≤ K by omega)
    · rfl
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hfloor : ⌊x * K⌋₊ < K := by
      apply (Nat.floor_lt (mul_nonneg hx.1 hKr.le)).2
      nlinarith
    refine ⟨⟨⌊x * K⌋₊, hfloor⟩, ?_⟩
    have hlo : (⌊x * K⌋₊ : ℝ) / K ≤ x := by
      apply (div_le_iff₀ hKr).2
      exact Nat.floor_le (mul_nonneg hx.1 hKr.le)
    have hhi : x < ((⌊x * K⌋₊ : ℝ) + 1) / K := by
      apply (lt_div_iff₀ hKr).2
      exact Nat.lt_floor_add_one (x * K)
    unfold cell
    split_ifs
    · exact ⟨hlo, hx.2⟩
    · exact ⟨hlo, hhi⟩

/-- The clipped pilot satisfies the second-moment part of equation (5),
with exactly A₂ from equation (6), uniformly over the seven channels and [0,1].  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,i,x,hx), [the stated conclusion holds](goal). -/
-- @node: pilot_second_moment
lemma pilot_second_moment (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (i : Fin 7)
    (x : ℝ) (hx : x ∈ covariateSpace) :
    (∫ w, (pilot c_f C_f w x i - markedDensityVector c_f C_f L P n hP x i) ^ 2
      ∂dataLaw P n n) ≤
      (2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
        (2 : ℝ) ^ (5 / 4 : ℝ) * (3 * (1 + C_f) * L) ^ 2 *
          (5 : ℝ) ^ (1 / 5 : ℝ)) * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  obtain ⟨l, hl⟩ := exists_cell_of_mem_covariateSpace hK x hx
  have hb := pilot_second_moment_cell_bound c_f C_f L P n hn hP i l x hl
  have hv := pilotResolution_ratio_rpow_le n hn 1 (by norm_num)
  rw [Real.rpow_one] at hv
  have hV : 0 ≤ 2 * (1 + C_f + C_f ^ 2) := by
    have hC := hP.sourceBounds.2.1
    positivity
  have hv' := mul_le_mul_of_nonneg_left hv hV
  have hd := mul_le_mul_of_nonneg_left (pilot_second_bias_scale_le n hn)
    (sq_nonneg (3 * (1 + C_f) * L))
  refine hb.trans ?_
  convert add_le_add hv' hd using 1 <;> ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
