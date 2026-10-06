module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicBlockCovariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotProjection
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Identification_Part1

/-! # Exact means and second moments of the pilot bin averages

This implements the mean and fluctuation calculation in equation (2) of the
marked-cubic proof for the bounded, observable bin scores. The eighth-moment
index-pattern calculation remains a separate step.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- A normalized block height has mean `K` times the one-record bin mean.  Under [the displayed assumptions and inputs](hyp:Ω,n,K,S,hS,f,hf), [the stated conclusion holds](goal). -/
-- @node: integral_iidBlockHeight
lemma integral_iidBlockHeight {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n K : ℕ}
    (S : Finset (Fin n)) (hS : 0 < S.card) (f : Ω → ℝ)
    (hf : Integrable f μ) :
    (∫ x, iidBlockHeight K S f x ∂Measure.pi (fun _ : Fin n => μ)) =
      (K : ℝ) * ∫ y, f y ∂μ := by
  have hcoord (r : Fin n) :
      (∫ x, f (x r) ∂Measure.pi (fun _ : Fin n => μ)) = ∫ y, f y ∂μ :=
    by
      have hp := measurePreserving_eval (fun _ : Fin n => μ) r
      have hm : AEStronglyMeasurable f
          ((Measure.pi (fun _ : Fin n => μ)).map (Function.eval r)) := by
        rw [hp.map_eq]
        exact hf.aestronglyMeasurable
      simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hm).symm
  have hint (r : Fin n) :
      Integrable (fun x : Fin n → Ω => f (x r)) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurePreserving_eval (fun _ : Fin n => μ) r).integrable_comp_of_integrable hf
  unfold iidBlockHeight
  rw [integral_const_mul, integral_finset_sum S (fun r _ => hint r)]
  simp_rw [hcoord]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  field_simp

/-- Centering at the exact bin mean turns the second moment into self-covariance.  Under [the displayed assumptions and inputs](hyp:Ω,n,K,S,hS,f,hf), [the stated conclusion holds](goal). -/
-- @node: iidBlockHeight_centered_second_moment
lemma iidBlockHeight_centered_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n K : ℕ}
    (S : Finset (Fin n)) (hS : 0 < S.card) (f : Ω → ℝ)
    (hf : Integrable f μ) :
    (∫ x, (iidBlockHeight K S f x - (K : ℝ) * ∫ y, f y ∂μ) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) =
    cov[iidBlockHeight K S f, iidBlockHeight K S f;
      Measure.pi (fun _ : Fin n => μ)] := by
  rw [covariance, integral_iidBlockHeight S hS f hf]
  simp only [pow_two]

/-- The exact source bin average obeys the roadmap's `V K / m` bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l,i), [the stated conclusion holds](goal). -/
-- @node: source_bin_height_second_moment_le
lemma source_bin_height_second_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (l : Fin K) (i : Fin 7) :
    (∫ x, (iidBlockHeight K S (sourceCellScore i K l) x -
      (K : ℝ) * ∫ o, sourceCellScore i K l o ∂sourceObsLaw P) ^ 2
      ∂Measure.pi (fun _ : Fin n => sourceObsLaw P)) ≤
      (1 + C_f + C_f ^ 2) * K / S.card := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  have hf := (memLp_two_of_mem_unit_interval (μ := sourceObsLaw P)
    (measurable_sourceCellScore i K l) (sourceCellScore_mem_unit_interval i K l)).integrable
      (by norm_num)
  rw [iidBlockHeight_centered_second_moment S hS _ hf]
  have hcov := source_iidBlockHeight_same_cell_covariance_le c_f C_f L P n K
    hP hK S hS l i i
  refine (le_abs_self _).trans (hcov.trans ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith [sq_nonneg C_f, mul_nonneg (sq_nonneg C_f) (sub_nonneg.mpr hKr)]

/-- The exact target bin average obeys the same `V K / m` bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l), [the stated conclusion holds](goal). -/
-- @node: target_bin_height_second_moment_le
lemma target_bin_height_second_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card) (l : Fin K) :
    (∫ x, (iidBlockHeight K S (targetCellScore K l) x -
      (K : ℝ) * (targetXLaw P (cell K l)).toReal) ^ 2
      ∂Measure.pi (fun _ : Fin n => targetXLaw P)) ≤
      (1 + C_f + C_f ^ 2) * K / S.card := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hf := (memLp_two_of_mem_unit_interval (μ := targetXLaw P)
    (measurable_targetCellScore K l) (targetCellScore_mem_unit_interval K l)).integrable
      (by norm_num)
  have hmean : (∫ y, targetCellScore K l y ∂targetXLaw P) =
      (targetXLaw P (cell K l)).toReal := by
    change (∫ y, (cell K l).indicator (fun _ => (1 : ℝ)) y ∂targetXLaw P) = _
    exact integral_indicator_one (measurableSet_cell K l)
  rw [← hmean, iidBlockHeight_centered_second_moment S hS _ hf]
  have hcov := target_iidBlockHeight_same_cell_covariance_le c_f C_f L P n K
    hP hK S hS l
  refine (le_abs_self _).trans (hcov.trans ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith [sq_nonneg C_f, mul_nonneg (sq_nonneg C_f) (sub_nonneg.mpr hKr)]

/-- The target bin probability is the integral of its marked density.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l), [the stated conclusion holds](goal). -/
-- @node: targetCellScore_integral_eq_density
lemma targetCellScore_integral_eq_density (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) :
    (∫ y, targetCellScore K l y ∂targetXLaw P) = ∫ y in cell K l, P.fT y := by
  rw [target_integral_eq_density_integral c_f C_f L P n hP]
  have hpoint : (fun y => P.fT y * targetCellScore K l y) =
      (cell K l).indicator P.fT := by
    funext y
    simp only [targetCellScore, Set.indicator]
    split_ifs <;> simp
  rw [hpoint, integral_indicator (measurableSet_cell K l),
    Measure.restrict_restrict_of_subset (cell_subset_covariateSpace hK l)]

/-- The target block height is unbiased for the exact Lebesgue cell average.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l), [the stated conclusion holds](goal). -/
-- @node: target_bin_height_mean_eq_cellAverage
lemma target_bin_height_mean_eq_cellAverage (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card) (l : Fin K) :
    (∫ x, iidBlockHeight K S (targetCellScore K l) x
      ∂Measure.pi (fun _ : Fin n => targetXLaw P)) = cellAverage P.fT K l := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hf := (memLp_two_of_mem_unit_interval (μ := targetXLaw P)
    (measurable_targetCellScore K l) (targetCellScore_mem_unit_interval K l)).integrable
      (by norm_num)
  rw [integral_iidBlockHeight S hS _ hf,
    targetCellScore_integral_eq_density c_f C_f L P n K hP hK]
  rfl

/-- The target histogram in the actual two-sample experiment satisfies equation (2).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,b,l), [the stated conclusion holds](goal). -/
-- @node: target_markedHistogram_second_moment_le
lemma target_markedHistogram_second_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (l : Fin K) :
    (∫ w, (markedHistogram w 0 K b (midpoint K l) - cellAverage P.fT K l) ^ 2
      ∂dataLaw P n n) ≤ (1 + C_f + C_f ^ 2) * K / blockSize n b := by
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
    (iidBlockHeight K (blockIdx n b) (targetCellScore K l) x - cellAverage P.fT K l) ^ 2
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
  have h := target_bin_height_second_moment_le c_f C_f L P n K hP hK
    (blockIdx n b) hcard l
  simpa only [g, hmean, block_card] using h

/-- Clipping the source mark preserves its observable mean, since outcomes lie in `[0,1]`.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i,hi), [the stated conclusion holds](goal). -/
-- @node: sourceCellScore_integral_eq_density
lemma sourceCellScore_integral_eq_density (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (i : Fin 7) (hi : i ≠ 0) :
    (∫ o, sourceCellScore i K l o ∂sourceObsLaw P) =
      ∫ y in cell K l, markedDensityVector c_f C_f L P n hP y i := by
  have hobs : Measurable (observeSource : Assigned → SourceObs) := by
    unfold observeSource covariate
    fun_prop
  have hy : ∀ᵐ o ∂sourceObsLaw P, o.2.2.2 ∈ Icc (0 : ℝ) 1 := by
    rw [sourceObsLaw]
    apply (ae_map_iff hobs.aemeasurable (by measurability)).2
    exact hP.outcome.2
  have hscore : (∫ o, sourceCellScore i K l o ∂sourceObsLaw P) =
      ∫ o in {o : SourceObs | o.1 ∈ cell K l}, coordinateMark i o ∂sourceObsLaw P := by
    have hset : MeasurableSet {o : SourceObs | o.1 ∈ cell K l} :=
      (measurableSet_cell K l).preimage measurable_fst
    rw [← integral_indicator hset]
    apply integral_congr_ae
    filter_upwards [hy] with o ho
    have hclip : max 0 (min 1 o.2.2.2) = o.2.2.2 := by
      rw [min_eq_right ho.2, max_eq_right ho.1]
    fin_cases i <;> simp_all [sourceCellScore, sourceCellMark, coordinateMark,
      Set.indicator, hclip]
  rw [hscore]
  have hB := measurableSet_cell K l
  have hsub := cell_subset_covariateSpace hK l
  fin_cases i
  · exact (hi rfl).elim
  · simpa [markedDensityVector, coordinateMark, boolReal, assignmentMass] using
      ((source_assignment_density c_f C_f L P n hP false _ hB hsub).trans
        (source_assignment_mark_integral P false _ hB).symm).symm
  · simpa [markedDensityVector, coordinateMark, boolReal, assignmentMass] using
      ((source_assignment_density c_f C_f L P n hP true _ hB hsub).trans
        (source_assignment_mark_integral P true _ hB).symm).symm
  · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass, boolReal] using
      (source_marked_arm_density c_f C_f L P n hP true false _ hB hsub).symm
  · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass, boolReal] using
      (source_marked_arm_density c_f C_f L P n hP true true _ hB hsub).symm
  · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass, boolReal] using
      (source_marked_arm_density c_f C_f L P n hP false false _ hB hsub).symm
  · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass, boolReal] using
      (source_marked_arm_density c_f C_f L P n hP false true _ hB hsub).symm

/-- Every source bin height is unbiased for its marked-density cell average.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l,i,hi), [the stated conclusion holds](goal). -/
-- @node: source_bin_height_mean_eq_cellAverage
lemma source_bin_height_mean_eq_cellAverage (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (l : Fin K) (i : Fin 7) (hi : i ≠ 0) :
    (∫ x, iidBlockHeight K S (sourceCellScore i K l) x
      ∂Measure.pi (fun _ : Fin n => sourceObsLaw P)) =
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  have hf := (memLp_two_of_mem_unit_interval (μ := sourceObsLaw P)
    (measurable_sourceCellScore i K l) (sourceCellScore_mem_unit_interval i K l)).integrable
      (by norm_num)
  rw [integral_iidBlockHeight S hS _ hf,
    sourceCellScore_integral_eq_density c_f C_f L P n K hP hK l i hi]
  rfl

/-- Every source histogram in the actual two-sample experiment satisfies equation (2).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,b,l,i,hi), [the stated conclusion holds](goal). -/
-- @node: source_markedHistogram_second_moment_le
lemma source_markedHistogram_second_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (l : Fin K) (i : Fin 7) (hi : i ≠ 0) :
    (∫ w, (markedHistogram w i K b (midpoint K l) - cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) ^ 2
      ∂dataLaw P n n) ≤ (1 + C_f + C_f ^ 2) * K / blockSize n b := by
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
    (iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) x - cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) ^ 2
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
  have h := source_bin_height_second_moment_le c_f C_f L P n K hP hK
    (blockIdx n b) hcard l i
  simpa only [g, hmean, block_card] using h

/-- All seven actual marked histogram channels satisfy the common cellwise second-moment bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,b,l,i), [the stated conclusion holds](goal). -/
-- @node: markedHistogram_second_moment_le
lemma markedHistogram_second_moment_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (b : Fin 4) (l : Fin K) (i : Fin 7) :
    (∫ w, (markedHistogram w i K b (midpoint K l) -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) ^ 2
      ∂dataLaw P n n) ≤ (1 + C_f + C_f ^ 2) * K / blockSize n b := by
  by_cases hi : i = 0
  · subst i
    simpa only [markedDensityVector, Matrix.cons_val_zero] using
      target_markedHistogram_second_moment_le c_f C_f L P n K hn hP hK b l
  · exact source_markedHistogram_second_moment_le c_f C_f L P n K hn hP hK b l i hi

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
