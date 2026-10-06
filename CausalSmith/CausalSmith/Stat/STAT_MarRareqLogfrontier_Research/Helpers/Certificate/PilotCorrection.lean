module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CellIntensity
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.MembershipRatio
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioAggregate

/-! Square integrability, independent membership weighting, and the light-cell
correction bounds in roadmap (22)--(23). -/

public section

open MeasureTheory ProbabilityTheory Set Finset Polynomial
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

attribute [local instance] markedObsLaw_isProbabilityMeasure
attribute [local instance] map_obs_isProbabilityMeasure
attribute [local instance] Classical.propDecidable

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonFactorialBranch
lemma memLp_poissonFactorialBranch (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (j : Cell d) :
    MemLp (poissonFactorialBranch n d q j) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  unfold poissonFactorialBranch
  split_ifs
  · apply memLp_finsetSum
    intro v hv
    have hA : MeasurableSet (streamEvent 2 j true true) :=
      Set.Finite.measurableSet (Set.toFinite _)
    have hB : MeasurableSet (streamEvent 2 j true false) :=
      Set.Finite.measurableSet (Set.toFinite _)
    have hmem := (memLp_two_iff_integrable_sq
      (measurable_weightedFactorial _ _ hA hB v).aestronglyMeasurable).2
        (integrable_sq_weightedFactorial (markedObsLaw P) ((n : ℝ≥0) / 2)
          _ _ hA hB (streamEvent_ones_subset_arrived 2 j) v
          (Finset.mem_Icc.mp hv).1)
    exact hmem.const_mul _
  · simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j,s), [the stated mathematical conclusion holds](goal). -/
-- @node: poissonSelectedCellEstimate_eq_ratio_add_correction
lemma poissonSelectedCellEstimate_eq_ratio_add_correction (n d : ℕ) (q : ℝ)
    (j : Cell d) (s : FiniteSample (ObsRecord d × Fin 3)) :
    poissonSelectedCellEstimate n d q j s = poissonRatioBranch j s +
      (if needleBranch n d q ∧
          eventCount s (streamEvent 1 j true false) ≤ needleRadius n q / 4
        then poissonFactorialBranch n d q j s - poissonRatioBranch j s else 0) := by
  unfold poissonSelectedCellEstimate
  split_ifs <;> ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j,s), [the stated mathematical conclusion holds](goal). -/
-- @node: norm_poissonSelectedCellEstimate_sub_ratio_le
lemma norm_poissonSelectedCellEstimate_sub_ratio_le (n d : ℕ) (q : ℝ)
    (j : Cell d) (s : FiniteSample (ObsRecord d × Fin 3)) :
    ‖poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s‖ ≤
      ‖poissonFactorialBranch n d q j s - poissonRatioBranch j s‖ := by
  unfold poissonSelectedCellEstimate
  split_ifs
  · exact le_rfl
  · simp only [sub_self, norm_zero]
    exact norm_nonneg _

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonSelectedCellEstimate_sub_ratio
lemma memLp_poissonSelectedCellEstimate_sub_ratio (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (j : Cell d) :
    MemLp (fun s ↦ poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  apply ((memLp_poissonFactorialBranch n d q P j).sub
    (memLp_poissonRatioBranch n d P j)).of_le
  · exact ((measurable_poissonSelectedCellEstimate n d q j).sub
      (measurable_poissonRatioBranch j)).aestronglyMeasurable
  · filter_upwards [] with s
    exact norm_poissonSelectedCellEstimate_sub_ratio_le n d q j s

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonSelectedCellEstimate_sub_ratio_le
lemma integral_sq_poissonSelectedCellEstimate_sub_ratio_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    (∫ s, (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      2 * ((∫ s, (poissonFactorialBranch n d q j s) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) + 1) := by
  have hH := (memLp_two_iff_integrable_sq
    (measurable_poissonFactorialBranch n d q j).aestronglyMeasurable).1
      (memLp_poissonFactorialBranch n d q P j)
  have hC := (memLp_two_iff_integrable_sq
    ((measurable_poissonSelectedCellEstimate n d q j).sub
      (measurable_poissonRatioBranch j)).aestronglyMeasurable).1
        (memLp_poissonSelectedCellEstimate_sub_ratio n d q P j)
  calc
    _ ≤ ∫ s, 2 * ((poissonFactorialBranch n d q j s) ^ 2 + 1)
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2) := by
      apply integral_mono hC ((hH.add (integrable_const 1)).const_mul 2)
      intro s
      have hD := poissonRatioBranch_mem_unitInterval j s
      have hDs : (poissonRatioBranch j s) ^ 2 ≤ 1 := by
        nlinarith [hD.1, hD.2]
      dsimp only [Pi.sub_apply, Pi.add_apply]
      unfold poissonSelectedCellEstimate
      split_ifs
      · have hsq := add_sq_le (a := poissonFactorialBranch n d q j s)
          (b := -poissonRatioBranch j s)
        simp only [neg_sq, ← sub_eq_add_neg] at hsq
        exact hsq.trans (by linarith)
      · simp only [sub_self, zero_pow (by decide : 2 ≠ 0)]
        positivity
    _ = _ := by rw [integral_const_mul, integral_add hH (integrable_const 1)]; simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hbranch,hlight), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonSelectedCellEstimate_sub_ratio_le_of_light
lemma integral_sq_poissonSelectedCellEstimate_sub_ratio_le_of_light
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hbranch : needleBranch n d q)
    (hlight : streamSize n * arrivedCell P j ≤ needleRadius n q) :
    (∫ s, (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      2 * (Real.exp (logScale n q / 8) + 1) := by
  apply (integral_sq_poissonSelectedCellEstimate_sub_ratio_le n d q P j).trans
  gcongr
  exact integral_sq_markedPoissonFactorialBranch_le_exp_of_light
    n d q P j hbranch hlight

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,F,hF), [the stated mathematical conclusion holds](goal). -/
-- @node: indepFun_poissonMemberWeight_pilot_estimation
lemma indepFun_poissonMemberWeight_pilot_estimation (n d : ℕ) (P : FullLaw d)
    (j : Cell d)
    (F : FiniteSample (ObsRecord d) × FiniteSample (ObsRecord d) → ℝ)
    (hF : Measurable F) :
    IndepFun (poissonMemberWeight n j)
      (fun s ↦ F (unshuffle s 1, unshuffle s 2))
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let W : FiniteSample (ObsRecord d) → ℝ := fun s ↦
    eventCount s (obsStreamEvent j false false) / streamSize n
  have hW : Measurable W :=
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))).div_const _
  have hcoords := (iIndepFun_pi (μ := fun _ : Fin 3 ↦
      finitePoissonSampleLaw (P.1.map obs) (((n : ℝ≥0) / 2) * (1 / 3)))
      (X := fun _ ↦ id) (fun _ ↦ measurable_id.aemeasurable)).indepFun_prodMk
        (fun _ ↦ measurable_pi_apply _) 1 2 0 (by decide) (by decide)
  have hind := hcoords.symm.comp hW hF
  rw [← map_unshuffle_markedObsLaw P ((n : ℝ≥0) / 2)] at hind
  have hWs (s : FiniteSample (ObsRecord d × Fin 3)) :
      W (unshuffle s 0) = poissonMemberWeight n j s := by
    simp only [W, poissonMemberWeight, eventCount_unshuffle]
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro a b ha hb
  have h := hind a b ha hb
  simp only [id_eq] at h
  have hpair : Measurable (fun s : Fin 3 → FiniteSample (ObsRecord d) ↦
      (s 1, s 2)) := (measurable_pi_apply 1).prodMk (measurable_pi_apply 2)
  rw [Measure.map_apply measurable_unshuffle
      ((ha.preimage (hW.comp (measurable_pi_apply 0))).inter (hb.preimage (hF.comp hpair))),
    Measure.map_apply measurable_unshuffle (ha.preimage (hW.comp (measurable_pi_apply 0))),
    Measure.map_apply measurable_unshuffle (hb.preimage (hF.comp hpair))] at h
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def, hWs] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: indepFun_poissonMemberWeight_selectedCorrection
lemma indepFun_poissonMemberWeight_selectedCorrection (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (j : Cell d) :
    IndepFun (poissonMemberWeight n j)
      (fun s ↦ poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let H : FiniteSample (ObsRecord d) → ℝ := fun s ↦
    if needleBranch n d q then
      ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1), needleCoeff n d q v *
        weightedFactorial (obsStreamEvent j true true) (obsStreamEvent j true false) v s
    else 0
  let D : FiniteSample (ObsRecord d) → ℝ := fun s ↦
    if 0 < eventCount s (obsStreamEvent j true false) then
      eventCount s (obsStreamEvent j true true) /
        eventCount s (obsStreamEvent j true false) else 0
  have hH : Measurable H := by
    dsimp [H]
    split_ifs
    · apply Finset.measurable_sum
      intro v hv
      exact (measurable_weightedFactorial _ _
        (Set.Finite.measurableSet (Set.toFinite _))
        (Set.Finite.measurableSet (Set.toFinite _)) v).const_mul _
    · fun_prop
  have hc (a o : Bool) : Measurable (fun s : FiniteSample (ObsRecord d) ↦
      (eventCount s (obsStreamEvent j a o) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
  have hD : Measurable D := by
    apply Measurable.ite
    · exact (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
        measurableSet_Ioi
    · exact (hc true true).div (hc true false)
    · fun_prop
  let F : FiniteSample (ObsRecord d) × FiniteSample (ObsRecord d) → ℝ := fun z ↦
    (if needleBranch n d q ∧
        eventCount z.1 (obsStreamEvent j true false) ≤ needleRadius n q / 4
      then H z.2 else D z.2) - D z.2
  have hF : Measurable F := by
    apply Measurable.sub _ (hD.comp measurable_snd)
    apply Measurable.ite
    · by_cases hb : needleBranch n d q
      · simp only [hb, true_and]
        exact ((hc true false).comp measurable_fst) measurableSet_Iic
      · simp [hb]
    · exact hH.comp measurable_snd
    · exact hD.comp measurable_snd
  have hDs (s : FiniteSample (ObsRecord d × Fin 3)) :
      D (unshuffle s 2) = poissonRatioBranch j s := by
    simp only [D, poissonRatioBranch, eventCount_unshuffle]
  have hHs (s : FiniteSample (ObsRecord d × Fin 3)) :
      H (unshuffle s 2) = poissonFactorialBranch n d q j s := by
    simp only [H, poissonFactorialBranch, weightedFactorial, eventCount_unshuffle]
  have hFs : (fun s ↦ F (unshuffle s 1, unshuffle s 2)) =
      (fun s ↦ poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) := by
    funext s
    simp only [F, eventCount_unshuffle, hDs, hHs, poissonSelectedCellEstimate]
  rw [← hFs]
  exact indepFun_poissonMemberWeight_pilot_estimation n d P j F hF

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonMemberWeight_mul_selectedCorrection
lemma memLp_poissonMemberWeight_mul_selectedCorrection
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    MemLp (fun s ↦ poissonMemberWeight n j s *
      (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hW := (memLp_two_iff_integrable_sq
    (measurable_poissonMemberWeight n d j).aestronglyMeasurable).1
      (memLp_poissonMemberWeight n d P j)
  have hC := (memLp_two_iff_integrable_sq
    ((measurable_poissonSelectedCellEstimate n d q j).sub
      (measurable_poissonRatioBranch j)).aestronglyMeasurable).1
        (memLp_poissonSelectedCellEstimate_sub_ratio n d q P j)
  have hi := (indepFun_poissonMemberWeight_selectedCorrection n d q P j).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h := hi.integrable_mul hW hC
  change Integrable (fun s ↦ (poissonMemberWeight n j s) ^ 2 *
    (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) ^ 2) _ at h
  apply (memLp_two_iff_integrable_sq
    ((measurable_poissonMemberWeight n d j).mul
      ((measurable_poissonSelectedCellEstimate n d q j).sub
        (measurable_poissonRatioBranch j))).aestronglyMeasurable).2
  simpa only [Pi.mul_apply, Pi.sub_apply, mul_pow] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonMemberWeight_mul_selectedCorrection
lemma integral_sq_poissonMemberWeight_mul_selectedCorrection
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) (hn : 0 < n) :
    (∫ s, (poissonMemberWeight n j s *
        (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      ((cellProb P j) ^ 2 + cellProb P j / streamSize n) *
        (∫ s, (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) ^ 2
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hi := (indepFun_poissonMemberWeight_selectedCorrection n d q P j).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h := hi.integral_fun_mul_eq_mul_integral
    ((measurable_poissonMemberWeight n d j).pow_const 2).aestronglyMeasurable
    (((measurable_poissonSelectedCellEstimate n d q j).sub
      (measurable_poissonRatioBranch j)).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def, id_eq] at h
  simp_rw [mul_pow]
  rw [h, integral_sq_poissonMemberWeight n d P j hn]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hn,hbranch,hlight), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonMemberWeight_mul_selectedCorrection_le_of_light
lemma integral_sq_poissonMemberWeight_mul_selectedCorrection_le_of_light
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) (hn : 0 < n)
    (hbranch : needleBranch n d q)
    (hlight : streamSize n * arrivedCell P j ≤ needleRadius n q) :
    (∫ s, (poissonMemberWeight n j s *
        (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      2 * ((cellProb P j) ^ 2 + cellProb P j / streamSize n) *
        (Real.exp (logScale n q / 8) + 1) := by
  rw [integral_sq_poissonMemberWeight_mul_selectedCorrection n d q P j hn]
  calc
    _ ≤ ((cellProb P j) ^ 2 + cellProb P j / streamSize n) *
        (2 * (Real.exp (logScale n q / 8) + 1)) :=
      mul_le_mul_of_nonneg_left
        (integral_sq_poissonSelectedCellEstimate_sub_ratio_le_of_light
          n d q P j hbranch hlight)
        (add_nonneg (sq_nonneg _) (div_nonneg measureReal_nonneg (by
          unfold streamSize; positivity)))
    _ = _ := by ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hbranch), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_light_integral_sq_poissonMemberWeight_mul_selectedCorrection_le
lemma sum_light_integral_sq_poissonMemberWeight_mul_selectedCorrection_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P)
    (hbranch : needleBranch n d q) :
    8 * (∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ streamSize n * arrivedCell P j ≤ needleRadius n q),
      ∫ s, (poissonMemberWeight n j s *
        (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      64 * d * (Real.exp (logScale n q / 8) + 1) *
        (needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
          needleRadius n q / (streamSize n * streamEffectiveSize n q)) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hP.n_pos
  have hm : 0 < streamSize n := by unfold streamSize; positivity
  have hN : 0 < streamEffectiveSize n q := by
    unfold streamEffectiveSize
    exact mul_pos hm hP.q_pos
  have hB : 0 ≤ needleRadius n q := by
    unfold needleRadius
    linarith [hbranch.1]
  let c : ℝ := 2 * (needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
      needleRadius n q / (streamSize n * streamEffectiveSize n q)) *
      (Real.exp (logScale n q / 8) + 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hj (j : Cell d) (hlight : streamSize n * arrivedCell P j ≤ needleRadius n q) :
      (∫ s, (poissonMemberWeight n j s *
        (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤ c := by
    have hp0 : 0 ≤ cellProb P j := measureReal_nonneg
    have hp : cellProb P j ≤ needleRadius n q / streamEffectiveSize n q := by
      apply (le_div_iff₀ hN).2
      have hi := streamEffectiveSize_mul_cellProb_le_arrivedStreamIntensity
        n d q P hP 2 j
      rw [coe_arrivedStreamIntensity] at hi
      simpa only [mul_comm] using hi.trans hlight
    have hmass : (cellProb P j) ^ 2 + cellProb P j / streamSize n ≤
        needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
          needleRadius n q / (streamSize n * streamEffectiveSize n q) := by
      calc
        _ ≤ (needleRadius n q / streamEffectiveSize n q) ^ 2 +
            (needleRadius n q / streamEffectiveSize n q) / streamSize n := by
          gcongr
        _ = _ := by rw [div_pow]; field_simp
    exact (integral_sq_poissonMemberWeight_mul_selectedCorrection_le_of_light
      n d q P j hn hbranch hlight).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmass (by norm_num)) (by positivity))
  calc
    _ ≤ 8 * ∑ _j : Cell d, c := by
      rw [Finset.sum_filter]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j hjmem
      split_ifs with hlight
      · exact hj j hlight
      · exact hc
    _ = _ := by simp [c]; ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,t,hbranch,ht), [the stated mathematical conclusion holds](goal). -/
-- @node: cheb_needle_intensity_abs_le
lemma cheb_needle_intensity_abs_le (n d : ℕ) (q t : ℝ)
    (hbranch : needleBranch n d q) (ht : t ∈ Icc 0 (needleRadius n q)) :
    t * |(chebNeedle n d q).eval t| ≤
      needleRadius n q / (needleDegree n q : ℝ)^2 := by
  have hB : 0 < needleRadius n q := by
    unfold needleRadius
    linarith [hbranch.1]
  have hk : 0 < needleDegree n q := by
    unfold needleDegree
    apply Nat.floor_pos.mpr
    linarith [hbranch.1]
  have hk2 : 0 < (needleDegree n q : ℝ)^2 := by positivity
  let p : Polynomial ℝ := 1 -
    (Chebyshev.T ℝ (needleDegree n q : ℤ)).comp
      (C 1 - C (2 / needleRadius n q) * X)
  have hp0 : p.coeff 0 = 0 := by
    simp [p, coeff_zero_eq_eval_zero, Chebyshev.T_eval_one]
  have hdiv : p.divX.eval t * t = p.eval t := by
    have h := congrArg (Polynomial.eval t) (divX_mul_X_add p)
    simpa [hp0] using h
  have hprod : (chebNeedle n d q).eval t * t =
      (needleRadius n q / (2 * (needleDegree n q : ℝ)^2)) *
        (1 - (Chebyshev.T ℝ (needleDegree n q : ℤ)).eval
          (1 - 2 * t / needleRadius n q)) := by
    simp only [chebNeedle, if_pos hbranch, eval_mul, eval_C]
    rw [mul_assoc, hdiv]
    simp only [p, eval_sub, eval_one, eval_comp, eval_mul, eval_C, eval_X]
    congr 3
    ring
  have hx : |1 - 2 * t / needleRadius n q| ≤ 1 := by
    apply abs_le.mpr
    have hratio : 0 ≤ 2 * t / needleRadius n q :=
      div_nonneg (mul_nonneg (by norm_num) ht.1) hB.le
    have hu : 2 * t / needleRadius n q ≤ 2 :=
      (div_le_iff₀ hB).2 (by linarith [ht.2])
    constructor <;> linarith
  have hT := Chebyshev.abs_eval_T_real_le_one (needleDegree n q : ℤ) hx
  have hab : |1 - (Chebyshev.T ℝ (needleDegree n q : ℤ)).eval
      (1 - 2 * t / needleRadius n q)| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hT).1, (abs_le.mp hT).2]
  calc
    _ = |(chebNeedle n d q).eval t * t| := by
      rw [abs_mul, abs_of_nonneg ht.1, mul_comm]
    _ = (needleRadius n q / (2 * (needleDegree n q : ℝ)^2)) *
        |1 - (Chebyshev.T ℝ (needleDegree n q : ℤ)).eval
          (1 - 2 * t / needleRadius n q)| := by
      rw [hprod, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (needleRadius n q / (2 * (needleDegree n q : ℝ)^2)) * 2 :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ = _ := by field_simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,j,hbranch,hlight), [the stated mathematical conclusion holds](goal). -/
-- @node: cellProb_mul_cellMean_abs_needle_le_of_light
lemma cellProb_mul_cellMean_abs_needle_le_of_light
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (j : Cell d)
    (hbranch : needleBranch n d q)
    (hlight : streamSize n * arrivedCell P j ≤ needleRadius n q) :
    cellProb P j * cellMean P j *
        |(chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      needleRadius n q /
        (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) := by
  have hm : 0 < streamSize n := by
    unfold streamSize
    have hn : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hP.n_pos)
    positivity
  have hN : 0 < streamEffectiveSize n q := by
    unfold streamEffectiveSize
    exact mul_pos hm hP.q_pos
  have ht : 0 ≤ streamSize n * arrivedCell P j :=
    mul_nonneg hm.le measureReal_nonneg
  have hi := streamEffectiveSize_mul_cellProb_le_arrivedStreamIntensity
    n d q P hP 2 j
  rw [coe_arrivedStreamIntensity] at hi
  have hneedle := cheb_needle_intensity_abs_le n d q
    (streamSize n * arrivedCell P j) hbranch ⟨ht, hlight⟩
  have hmu := cellMean_mem_Icc P j
  have hp : 0 ≤ cellProb P j := measureReal_nonneg
  have hmass : streamEffectiveSize n q * (cellProb P j * cellMean P j) ≤
      streamSize n * arrivedCell P j := by
    calc
      _ ≤ streamEffectiveSize n q * (cellProb P j * 1) := by gcongr; exact hmu.2
      _ ≤ _ := by simpa using hi
  have h := (mul_le_mul_of_nonneg_right hmass
    (abs_nonneg ((chebNeedle n d q).eval (streamSize n * arrivedCell P j)))).trans
      hneedle
  have hdiv : cellProb P j * cellMean P j *
      |(chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      (needleRadius n q / (needleDegree n q : ℝ)^2) / streamEffectiveSize n q :=
    (le_div_iff₀ hN).2 (by nlinarith [h])
  simpa only [div_div, mul_comm] using hdiv

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hbranch,pilot,hpilot), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_sum_light_pilot_needle_bias_le
lemma abs_sum_light_pilot_needle_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P)
    (hbranch : needleBranch n d q) (pilot : Cell d → ℝ)
    (hpilot : ∀ j, pilot j ∈ Icc (0 : ℝ) 1) :
    |2 * ∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ streamSize n * arrivedCell P j ≤ needleRadius n q),
      armSign j.1 * cellProb P j * cellMean P j * pilot j *
        (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      8 * d * needleRadius n q /
        (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) := by
  classical
  let c := needleRadius n q /
    (streamEffectiveSize n q * (needleDegree n q : ℝ)^2)
  have hc : 0 ≤ c := by
    dsimp [c, needleRadius, streamEffectiveSize, streamSize]
    have := hbranch.1
    have := hP.q_pos
    positivity
  have hj (j : Cell d)
      (hlight : streamSize n * arrivedCell P j ≤ needleRadius n q) :
      |armSign j.1 * cellProb P j * cellMean P j * pilot j *
        (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤ c := by
    have hsign : |armSign j.1| = 1 := by cases j.1 <;> simp [armSign]
    have hp : 0 ≤ cellProb P j := measureReal_nonneg
    have hmu := cellMean_mem_Icc P j
    have hpm : 0 ≤ cellProb P j * cellMean P j := mul_nonneg hp hmu.1
    rw [abs_mul, abs_mul, abs_mul, abs_mul, hsign, one_mul,
      abs_of_nonneg hp,
      abs_of_nonneg (cellMean_mem_Icc P j).1, abs_of_nonneg (hpilot j).1]
    calc
      _ ≤ cellProb P j * cellMean P j * 1 *
          |(chebNeedle n d q).eval (streamSize n * arrivedCell P j)| := by
        gcongr
        exact (hpilot j).2
      _ ≤ c := by
        simpa only [mul_one] using
          cellProb_mul_cellMean_abs_needle_le_of_light n d q P hP j hbranch hlight
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * ∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ streamSize n * arrivedCell P j ≤ needleRadius n q),
      |armSign j.1 * cellProb P j * cellMean P j * pilot j *
        (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ _j : Cell d, c := by
      rw [Finset.sum_filter]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hlight
      · exact hj j hlight
      · exact hc
    _ = _ := by simp [c]; ring

end CausalSmith.Stat.MarRareqLogfrontier
