module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.FactorialMean

/-! Pilot independence and the exact selected-cell bias in roadmap (16). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

attribute [local instance] markedObsLaw_isProbabilityMeasure map_obs_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,F,hF), [the stated mathematical conclusion holds](goal). -/
-- @node: indepFun_pilotCount_estimationStatistic
lemma indepFun_pilotCount_estimationStatistic (n d : ℕ) (P : FullLaw d)
    (j : Cell d) (F : FiniteSample (ObsRecord d) → ℝ) (hF : Measurable F) :
    IndepFun (fun s ↦ eventCount s (streamEvent 1 j true false))
      (fun s ↦ F (unshuffle s 2))
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let C : FiniteSample (ObsRecord d) → ℕ := fun s ↦
    eventCount s (obsStreamEvent j true false)
  have hC : Measurable C :=
    measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _))
  have hcoords := (iIndepFun_pi (μ := fun _ : Fin 3 ↦
      finitePoissonSampleLaw (P.1.map obs) (((n : ℝ≥0) / 2) * (1 / 3)))
      (X := fun _ ↦ id) (fun _ ↦ measurable_id.aemeasurable)).indepFun
        (show (1 : Fin 3) ≠ 2 by decide)
  have hind := hcoords.comp hC hF
  rw [← map_unshuffle_markedObsLaw P ((n : ℝ≥0) / 2)] at hind
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro a b ha hb
  have h := hind a b ha hb
  simp only [id_eq] at h
  rw [Measure.map_apply measurable_unshuffle
      ((ha.preimage (hC.comp (measurable_pi_apply 1))).inter
        (hb.preimage (hF.comp (measurable_pi_apply 2)))),
    Measure.map_apply measurable_unshuffle (ha.preimage (hC.comp (measurable_pi_apply 1))),
    Measure.map_apply measurable_unshuffle (hb.preimage (hF.comp (measurable_pi_apply 2)))] at h
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def,
    C, eventCount_unshuffle] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,F,hF), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_pilot_gated_estimationStatistic
lemma integral_pilot_gated_estimationStatistic (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (j : Cell d) (F : FiniteSample (ObsRecord d) → ℝ)
    (hF : Measurable F) :
    (∫ s, (if (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4
      then F (unshuffle s 2) else 0)
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
    (∫ s, F (unshuffle s 2)
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let g : ℕ → ℝ := fun c ↦ if (c : ℝ) ≤ needleRadius n q / 4 then 1 else 0
  have hg : Measurable g := measurable_of_countable _
  have hi := (indepFun_pilotCount_estimationStatistic n d P j F hF).comp hg measurable_id
  have hcount := measurable_eventCount (streamEvent 1 j true false)
    (Set.Finite.measurableSet (Set.toFinite _))
  have hstat : Measurable (fun s : FiniteSample (ObsRecord d × Fin 3) ↦ F (unshuffle s 2)) :=
    hF.comp ((measurable_pi_apply (2 : Fin 3)).comp measurable_unshuffle)
  have h := hi.integral_fun_mul_eq_mul_integral
    (hg.comp hcount).aestronglyMeasurable hstat.aestronglyMeasurable
  simp only [Function.comp_def, id_eq, g, ite_mul, one_mul, zero_mul] at h
  rw [h]
  congr 1
  have hs : MeasurableSet {s : FiniteSample (ObsRecord d × Fin 3) |
      (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} :=
    ((measurable_of_countable (fun c : ℕ ↦ (c : ℝ))).comp hcount) measurableSet_Iic
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
    (integral_indicator_one (μ := finitePoissonSampleLaw (markedObsLaw P)
      ((n : ℝ≥0) / 2)) hs)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_poissonSelectedCellEstimate_eq_pilot_mixture
lemma integral_poissonSelectedCellEstimate_eq_pilot_mixture
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q) :
    (∫ s, poissonSelectedCellEstimate n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
    (∫ s, poissonRatioBranch j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) +
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
    ((∫ s, poissonFactorialBranch n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
     (∫ s, poissonRatioBranch j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))) := by
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
    (fun s ↦ H s - D s) (hH.sub hD)
  simp only [hHs, hDs] at hgate
  have hDint := (memLp_poissonRatioBranch n d P j).integrable (by norm_num)
  have hHint := (memLp_poissonFactorialBranch n d q P j).integrable (by norm_num)
  have hCint := (memLp_poissonSelectedCellEstimate_sub_ratio n d q P j).integrable
    (by norm_num)
  have hdecomp : (fun s ↦ poissonSelectedCellEstimate n d q j s) =
      (fun s ↦ poissonRatioBranch j s +
        (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) := by
    funext s
    ring
  rw [hdecomp, integral_add hDint hCint]
  have hcorr : (fun s ↦ poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s) =
      (fun s ↦ if (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4
        then poissonFactorialBranch n d q j s - poissonRatioBranch j s else 0) := by
    funext s
    simp only [poissonSelectedCellEstimate, hb, true_and]
    split_ifs <;> simp
  rw [hcorr, hgate, integral_sub hHint hDint]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoissonSelectedCellEstimate_bias
lemma markedPoissonSelectedCellEstimate_bias
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q) :
    (∫ s, poissonSelectedCellEstimate n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j =
    -cellMean P j *
      ((finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
        {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
          (chebNeedle n d q).eval (streamSize n * arrivedCell P j) +
       (1 - (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
        {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}) *
          Real.exp (-(streamSize n * arrivedCell P j))) := by
  rw [integral_poissonSelectedCellEstimate_eq_pilot_mixture n d q P j hb,
    integral_markedPoissonFactorialBranch_eq_needle, integral_markedPoissonRatioBranch]
  rw [neg_mul]
  ring

end CausalSmith.Stat.MarRareqLogfrontier
