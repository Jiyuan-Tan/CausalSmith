module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.MembershipMoments
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.StreamBridge
public import Mathlib.Probability.Independence.Integration

/-! Independent membership and estimation streams give the weighted ratio
variance identity and its aggregate bound in roadmap (21). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

attribute [local instance] markedObsLaw_isProbabilityMeasure map_obs_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,j), [the stated mathematical conclusion holds](goal). -/
-- @node: measurable_poissonMemberWeight
@[fun_prop] lemma measurable_poissonMemberWeight (n d : ℕ) (j : Cell d) :
    Measurable (poissonMemberWeight n j) := by
  unfold poissonMemberWeight
  exact ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))).div_const _

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonRatioBranch
lemma memLp_poissonRatioBranch (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    MemLp (poissonRatioBranch j) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_poissonRatioBranch j).aestronglyMeasurable).2
  exact integrable_poissonRatioBranch_sq n d P j

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: indepFun_poissonMemberWeight_ratioBranch
lemma indepFun_poissonMemberWeight_ratioBranch (n d : ℕ) (P : FullLaw d)
    (j : Cell d) :
    IndepFun (poissonMemberWeight n j) (poissonRatioBranch j)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let W : FiniteSample (ObsRecord d) → ℝ := fun s ↦
    eventCount s (obsStreamEvent j false false) / streamSize n
  let D : FiniteSample (ObsRecord d) → ℝ := fun s ↦
    if 0 < eventCount s (obsStreamEvent j true false) then
      eventCount s (obsStreamEvent j true true) /
        eventCount s (obsStreamEvent j true false) else 0
  have hcount (a o : Bool) : Measurable (fun s : FiniteSample (ObsRecord d) ↦
      (eventCount s (obsStreamEvent j a o) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
  have hW : Measurable W := (hcount false false).div_const _
  have hD : Measurable D := by
    apply Measurable.ite
    · exact (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
        measurableSet_Ioi
    · exact (hcount true true).div (hcount true false)
    · fun_prop
  have hcoords := (iIndepFun_pi (μ := fun _ : Fin 3 ↦
      finitePoissonSampleLaw (P.1.map obs) (((n : ℝ≥0) / 2) * (1 / 3)))
      (X := fun _ ↦ id) (fun _ ↦ measurable_id.aemeasurable)).indepFun
        (show (0 : Fin 3) ≠ 2 by decide)
  have hind := hcoords.comp hW hD
  rw [← map_unshuffle_markedObsLaw P ((n : ℝ≥0) / 2)] at hind
  have hWs (s : FiniteSample (ObsRecord d × Fin 3)) :
      W (unshuffle s 0) = poissonMemberWeight n j s := by
    simp only [W, poissonMemberWeight, eventCount_unshuffle]
  have hDs (s : FiniteSample (ObsRecord d × Fin 3)) :
      D (unshuffle s 2) = poissonRatioBranch j s := by
    simp only [D, poissonRatioBranch, eventCount_unshuffle]
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro a b ha hb
  have h := hind a b ha hb
  simp only [id_eq] at h
  rw [Measure.map_apply measurable_unshuffle
      ((ha.preimage (hW.comp (measurable_pi_apply 0))).inter
        (hb.preimage (hD.comp (measurable_pi_apply 2)))),
    Measure.map_apply measurable_unshuffle (ha.preimage (hW.comp (measurable_pi_apply 0))),
    Measure.map_apply measurable_unshuffle (hb.preimage (hD.comp (measurable_pi_apply 2)))] at h
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def, hWs, hDs] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonMemberWeight_mul_ratioBranch
lemma memLp_poissonMemberWeight_mul_ratioBranch (n d : ℕ) (P : FullLaw d)
    (j : Cell d) :
    MemLp (fun s ↦ poissonMemberWeight n j s * poissonRatioBranch j s) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  apply (memLp_poissonMemberWeight n d P j).of_le_mul
    ((measurable_poissonMemberWeight n d j).mul
      (measurable_poissonRatioBranch j)).aestronglyMeasurable (c := 1)
  filter_upwards [] with s
  simp only [Pi.mul_apply, norm_mul, one_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rcases poissonRatioBranch_mem_unitInterval j s with ⟨h0, h1⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: variance_poissonMemberWeight_mul_ratioBranch
lemma variance_poissonMemberWeight_mul_ratioBranch (n d : ℕ) (P : FullLaw d)
    (j : Cell d) (hn : 0 < n) :
    variance (fun s ↦ poissonMemberWeight n j s * poissonRatioBranch j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      (cellProb P j) ^ 2 * variance (poissonRatioBranch j)
        (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) +
      (cellProb P j / streamSize n) *
        (∫ s, (poissonRatioBranch j s) ^ 2
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hi := indepFun_poissonMemberWeight_ratioBranch n d P j
  have hmean := hi.integral_fun_mul_eq_mul_integral
    (measurable_poissonMemberWeight n d j).aestronglyMeasurable
    (measurable_poissonRatioBranch j).aestronglyMeasurable
  have hsecond := (hi.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
    ((measurable_poissonMemberWeight n d j).pow_const 2).aestronglyMeasurable
    ((measurable_poissonRatioBranch j).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def, id_eq] at hsecond
  rw [variance_eq_sub (memLp_poissonMemberWeight_mul_ratioBranch n d P j),
    variance_eq_sub (memLp_poissonRatioBranch n d P j)]
  simp only [Pi.pow_apply]
  simp only [mul_pow]
  rw [hmean, hsecond, integral_poissonMemberWeight n d P j hn,
    integral_sq_poissonMemberWeight n d P j hn]
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_variance_poissonMemberWeight_mul_ratioBranch_le
lemma sum_variance_poissonMemberWeight_mul_ratioBranch_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    (∑ j : Cell d, variance
      (fun s ↦ poissonMemberWeight n j s * poissonRatioBranch j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))) ≤
      4 / streamEffectiveSize n q + 1 / streamSize n := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hP.n_pos
  simp_rw [variance_poissonMemberWeight_mul_ratioBranch n d P _ hn]
  rw [Finset.sum_add_distrib]
  apply add_le_add (sum_cellProb_sq_mul_ratioVariance_le n d q P hP)
  simpa only [variance_poissonMemberWeight n d P _ hn] using
    sum_membershipVariance_mul_ratioSecondMoment_le n d P hn

end CausalSmith.Stat.MarRareqLogfrontier
