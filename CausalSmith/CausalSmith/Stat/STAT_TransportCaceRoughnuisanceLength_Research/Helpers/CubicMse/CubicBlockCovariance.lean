module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.FlatHistogramBlocks

/-! # Uniform covariance bounds for flattened histogram blocks -/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:Ω,n,K,S,f,hf), [the stated result about measurable iid block height holds](goal). -/

@[fun_prop]
lemma measurable_iidBlockHeight {Ω : Type*} [MeasurableSpace Ω]
    {n K : ℕ} (S : Finset (Fin n)) (f : Ω → ℝ) (hf : Measurable f) :
    Measurable (iidBlockHeight K S f) := by
  unfold iidBlockHeight
  fun_prop
/-- Given [the supplied inputs](hyp:Ω,n,K,S,hS,f,hf,hunit), [the stated result about iid block height mem lp of unit interval holds](goal). -/

lemma iidBlockHeight_memLp_of_unit_interval
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n K : ℕ} (S : Finset (Fin n)) (hS : 0 < S.card) (f : Ω → ℝ)
    (hf : Measurable f) (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (iidBlockHeight K S f) 2 (Measure.pi (fun _ : Fin n => μ)) := by
  have hmeas := measurable_iidBlockHeight (K := K) S f hf
  apply MemLp.of_bound hmeas.aestronglyMeasurable K
  filter_upwards [] with x
  have hsum_nonneg : 0 ≤ ∑ r ∈ S, f (x r) :=
    Finset.sum_nonneg fun r _ => (hunit (x r)).1
  have hsum_le : (∑ r ∈ S, f (x r)) ≤ S.card := by
    simpa using Finset.sum_le_card_nsmul S (fun r => f (x r)) 1
      (fun r _ => (hunit (x r)).2)
  unfold iidBlockHeight
  change |(K : ℝ) / S.card * ∑ r ∈ S, f (x r)| ≤ K
  rw [abs_of_nonneg (mul_nonneg (by positivity) hsum_nonneg)]
  calc
    (K : ℝ) / S.card * ∑ r ∈ S, f (x r) ≤
        (K : ℝ) / S.card * S.card :=
      mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = K := by
      have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
      field_simp

/-- The covariance of two flattened block heights is bounded uniformly over
source and target channels on the same histogram cell.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,b,hb,l,i,j), [the stated conclusion holds](goal). -/
lemma flatBlockHeight_same_cell_covariance_le
    (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (hb : 0 < (blockIdx n b).card)
    (l : Fin K) (i j : Fin 7) :
    |cov[(fun x : (a : FlatIndex n) → FlatObs n a =>
        flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x)),
      (fun x : (a : FlatIndex n) → FlatObs n a =>
        flatBlockHeight j b l (finsetCoordProj (flatBlock n b) x));
      Measure.pi (flatLaw P n)]| ≤
      ((K : ℝ) * C_f + C_f ^ 2) / (blockIdx n b).card := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp_rw [flatBlockHeight_proj_target]
      rw [covariance_flatLaw_target c_f C_f L P n hP]
      · exact target_iidBlockHeight_same_cell_covariance_le
          c_f C_f L P n K hP hK (blockIdx n b) hb l
      · exact measurable_iidBlockHeight _ _ (measurable_targetCellScore K l)
      · exact measurable_iidBlockHeight _ _ (measurable_targetCellScore K l)
    · simp_rw [flatBlockHeight_proj_target, flatBlockHeight_proj_source j hj]
      rw [covariance_comm]
      rw [covariance_flatLaw_source_target_zero c_f C_f L P n hP]
      · simp
        have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
        positivity
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_sourceCellScore j K l)
          (sourceCellScore_mem_unit_interval j K l)
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_targetCellScore K l)
          (targetCellScore_mem_unit_interval K l)
  · by_cases hj : j = 0
    · subst j
      simp_rw [flatBlockHeight_proj_source i hi, flatBlockHeight_proj_target]
      rw [covariance_flatLaw_source_target_zero c_f C_f L P n hP]
      · simp
        have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
        positivity
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_sourceCellScore i K l)
          (sourceCellScore_mem_unit_interval i K l)
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_targetCellScore K l)
          (targetCellScore_mem_unit_interval K l)
    · simp_rw [flatBlockHeight_proj_source i hi, flatBlockHeight_proj_source j hj]
      rw [covariance_flatLaw_source c_f C_f L P n hP]
      · exact source_iidBlockHeight_same_cell_covariance_le
          c_f C_f L P n K hP hK (blockIdx n b) hb l i j
      · exact measurable_iidBlockHeight _ _ (measurable_sourceCellScore i K l)
      · exact measurable_iidBlockHeight _ _ (measurable_sourceCellScore j K l)

/-- The covariance of two flattened block heights is bounded uniformly over
source and target channels on distinct histogram cells.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,b,hb,l,r,hlr,i,j), [the stated conclusion holds](goal). -/
lemma flatBlockHeight_off_cell_covariance_le
    (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (hb : 0 < (blockIdx n b).card)
    {l r : Fin K} (hlr : l ≠ r) (i j : Fin 7) :
    |cov[(fun x : (a : FlatIndex n) → FlatObs n a =>
        flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x)),
      (fun x : (a : FlatIndex n) → FlatObs n a =>
        flatBlockHeight j b r (finsetCoordProj (flatBlock n b) x));
      Measure.pi (flatLaw P n)]| ≤
      C_f ^ 2 / (blockIdx n b).card := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp_rw [flatBlockHeight_proj_target]
      rw [covariance_flatLaw_target c_f C_f L P n hP]
      · exact target_iidBlockHeight_off_cell_covariance_le
          c_f C_f L P n K hP hK (blockIdx n b) hb hlr
      · exact measurable_iidBlockHeight _ _ (measurable_targetCellScore K l)
      · exact measurable_iidBlockHeight _ _ (measurable_targetCellScore K r)
    · simp_rw [flatBlockHeight_proj_target, flatBlockHeight_proj_source j hj]
      rw [covariance_comm]
      rw [covariance_flatLaw_source_target_zero c_f C_f L P n hP]
      · simp
        positivity
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_sourceCellScore j K r)
          (sourceCellScore_mem_unit_interval j K r)
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_targetCellScore K l)
          (targetCellScore_mem_unit_interval K l)
  · by_cases hj : j = 0
    · subst j
      simp_rw [flatBlockHeight_proj_source i hi, flatBlockHeight_proj_target]
      rw [covariance_flatLaw_source_target_zero c_f C_f L P n hP]
      · simp
        positivity
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_sourceCellScore i K l)
          (sourceCellScore_mem_unit_interval i K l)
      · exact iidBlockHeight_memLp_of_unit_interval _ hb _
          (measurable_targetCellScore K r)
          (targetCellScore_mem_unit_interval K r)
    · simp_rw [flatBlockHeight_proj_source i hi, flatBlockHeight_proj_source j hj]
      rw [covariance_flatLaw_source c_f C_f L P n hP]
      · exact source_iidBlockHeight_off_cell_covariance_le
          c_f C_f L P n K hP hK (blockIdx n b) hb hlr i j
      · exact measurable_iidBlockHeight _ _ (measurable_sourceCellScore i K l)
      · exact measurable_iidBlockHeight _ _ (measurable_sourceCellScore j K r)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
