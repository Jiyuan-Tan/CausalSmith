module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.FullFactorialMoment
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotBiasBounds

/-! Heavy-cell correction second moments, retaining the random membership
weights, as required by roadmap (24). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_selectedCorrection_eq_pilot_mul
lemma integral_sq_selectedCorrection_eq_pilot_mul
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q) :
    (∫ s, (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
    (∫ s, (poissonFactorialBranch n d q j s - poissonRatioBranch j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
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
    simp only [H, if_pos hb]
    apply Finset.measurable_sum
    intro v hv
    exact (measurable_weightedFactorial _ _
      (Set.Finite.measurableSet (Set.toFinite _))
      (Set.Finite.measurableSet (Set.toFinite _)) v).const_mul _
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
  have hDs (s : FiniteSample (ObsRecord d × Fin 3)) :
      D (unshuffle s 2) = poissonRatioBranch j s := by
    simp only [D, poissonRatioBranch, eventCount_unshuffle]
  have hHs (s : FiniteSample (ObsRecord d × Fin 3)) :
      H (unshuffle s 2) = poissonFactorialBranch n d q j s := by
    simp only [H, poissonFactorialBranch, weightedFactorial, eventCount_unshuffle]
  have hgate := integral_pilot_gated_estimationStatistic n d q P j
    (fun s ↦ (H s - D s) ^ 2) ((hH.sub hD).pow_const 2)
  simp only [hHs, hDs] at hgate
  rw [← hgate]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [poissonSelectedCellEstimate, hb, true_and]
  split_ifs <;> simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_selectedCorrection_le_of_heavy
lemma integral_sq_selectedCorrection_le_of_heavy
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (∫ s, (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      4 * Real.exp (-32 * logScale n q) := by
  have hH := (memLp_two_iff_integrable_sq
    (measurable_poissonFactorialBranch n d q j).aestronglyMeasurable).1
      (memLp_poissonFactorialBranch n d q P j)
  have hdiff := (memLp_two_iff_integrable_sq
    ((measurable_poissonFactorialBranch n d q j).sub
      (measurable_poissonRatioBranch j)).aestronglyMeasurable).1
        ((memLp_poissonFactorialBranch n d q P j).sub
          (memLp_poissonRatioBranch n d P j))
  have hmoment :
      (∫ s, (poissonFactorialBranch n d q j s - poissonRatioBranch j s) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      2 * ((∫ s, (poissonFactorialBranch n d q j s) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) + 1) := by
    calc
      _ ≤ ∫ s, 2 * ((poissonFactorialBranch n d q j s) ^ 2 + 1)
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2) := by
        apply integral_mono hdiff ((hH.add (integrable_const 1)).const_mul 2)
        intro s
        dsimp only [Pi.add_apply]
        have hD := poissonRatioBranch_mem_unitInterval j s
        have hDs : (poissonRatioBranch j s) ^ 2 ≤ 1 := by nlinarith [hD.1, hD.2]
        have hsq := add_sq_le (a := poissonFactorialBranch n d q j s)
          (b := -poissonRatioBranch j s)
        simp only [neg_sq, ← sub_eq_add_neg] at hsq
        exact hsq.trans (by linarith)
      _ = _ := by rw [integral_const_mul, integral_add hH (integrable_const 1)]; simp
  rw [integral_sq_selectedCorrection_eq_pilot_mul n d q P j hb]
  have hp := markedPoisson_pilot_light_probability_le_exp_of_heavy n d q P j hb hh
  have hprod := markedPoisson_pilot_light_mul_factorial_secondMoment_le n d q P j hb hh
  have h := mul_le_mul_of_nonneg_left hmoment
    (show 0 ≤ (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}
      from measureReal_nonneg)
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hn,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_memberWeight_mul_selectedCorrection_le_of_heavy
lemma integral_sq_memberWeight_mul_selectedCorrection_le_of_heavy
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) (hn : 0 < n)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (∫ s, (poissonMemberWeight n j s *
      (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      4 * Real.exp (-32 * logScale n q) *
        (∫ s, (poissonMemberWeight n j s) ^ 2
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  rw [integral_sq_poissonMemberWeight_mul_selectedCorrection n d q P j hn,
    integral_sq_poissonMemberWeight n d P j hn]
  have h := mul_le_mul_of_nonneg_left
    (integral_sq_selectedCorrection_le_of_heavy n d q P j hb hh)
    (show 0 ≤ (cellProb P j) ^ 2 + cellProb P j / streamSize n from
      add_nonneg (sq_nonneg _) (div_nonneg measureReal_nonneg (by
        unfold streamSize; positivity)))
  simpa only [mul_comm] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hn,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_heavy_integral_sq_memberWeight_mul_selectedCorrection_le
lemma sum_heavy_integral_sq_memberWeight_mul_selectedCorrection_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (hn : 0 < n)
    (hb : needleBranch n d q) :
    8 * (∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ needleRadius n q < streamSize n * arrivedCell P j),
      ∫ s, (poissonMemberWeight n j s *
        (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      32 * Real.exp (-32 * logScale n q) * (1 + 1 / streamSize n) := by
  classical
  calc
    _ ≤ 8 * ∑ j : Cell d, 4 * Real.exp (-32 * logScale n q) *
        (∫ s, (poissonMemberWeight n j s) ^ 2
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
      rw [Finset.sum_filter]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hh
      · exact integral_sq_memberWeight_mul_selectedCorrection_le_of_heavy n d q P j hn hb hh
      · exact mul_nonneg (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _)
    _ = 32 * Real.exp (-32 * logScale n q) *
        (∑ j : Cell d, ∫ s, (poissonMemberWeight n j s) ^ 2
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_integral_sq_poissonMemberWeight_le n d P hn) (by positivity)

end CausalSmith.Stat.MarRareqLogfrontier
