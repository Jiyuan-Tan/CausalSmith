module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreTransport

/-!
# Joint measurability of recurrence scores

The death product over distinct observed exit times is measurable jointly in
sample and time, even with ties. This supplies the measurable exposure-dependent
weights and concrete finite-configuration scores needed for product-law transport.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A finite product over distinct measurable values is measurable when every
factor evaluated at a generating value is measurable. Duplicates are retained
only once, matching the observed product-limit definition with tied exits. -/
-- @node: measurable_recurrence_prod_image
lemma measurable_recurrence_prod_image {E : Type*} [MeasurableSpace E] {n : ℕ}
    (s : Finset (Fin n)) (v : E → Fin n → ℝ) (F : E → ℝ → ℝ)
    (hv : ∀ i, Measurable (fun e => v e i))
    (hF : ∀ i, Measurable (fun e => F e (v e i))) :
    Measurable (fun e => ∏ u ∈ s.image (v e), F e u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : MeasurableSet {e | v e i ∈ s.image (v e)} := by
      simp only [Finset.mem_image]
      rw [show {e | ∃ j ∈ s, v e j = v e i} =
        ⋃ j : Fin n, {e | j ∈ s ∧ v e j = v e i} by ext e; simp]
      apply MeasurableSet.iUnion
      intro j
      by_cases hj : j ∈ s
      · simpa only [hj, true_and] using measurableSet_eq_fun (hv j) (hv i)
      · simp only [hj, false_and, ofPred_false]
        exact MeasurableSet.empty
    have heq : (fun e => ∏ u ∈ (insert i s).image (v e), F e u) =
        fun e => if v e i ∈ s.image (v e) then
          ∏ u ∈ s.image (v e), F e u
        else F e (v e i) * ∏ u ∈ s.image (v e), F e u := by
      funext e
      rw [Finset.image_insert]
      by_cases he : v e i ∈ s.image (v e) <;> simp [he]
    rw [heq]
    exact ih.ite hs ((hF i).mul ih)

/-- The observed risk count is jointly measurable in sample and time. -/
-- @node: measurable_recurrenceRiskSet_joint
@[fun_prop]
lemma measurable_recurrenceRiskSet_joint {n : ℕ} (a : Arm) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ => riskSet a p.1 p.2) := by
  classical
  have heq : (fun p : (Fin n → ObsHistory) × ℝ => riskSet a p.1 p.2) =
      fun p => ∑ i : Fin n,
        if (p.1 i).treatment = a ∧ p.2 ≤ (p.1 i).exit then (1 : ℕ) else 0 := by
    funext p
    simp [riskSet]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_le measurable_snd (by fun_prop))
  · exact measurable_const
  · exact measurable_const

/-- The totalized inverse risk is jointly measurable in sample and time. -/
-- @node: measurable_recurrenceInvRisk_joint
@[fun_prop]
lemma measurable_recurrenceInvRisk_joint {n : ℕ} (a : Arm) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ => invRisk a p.1 p.2) := by
  unfold invRisk
  apply Measurable.ite
    (measurableSet_eq_fun (measurable_recurrenceRiskSet_joint a) measurable_const)
  · exact measurable_const
  · fun_prop

/-- The aggregate observed death jump is jointly measurable in sample and time. -/
-- @node: measurable_recurrenceDeathJump_joint
@[fun_prop]
lemma measurable_recurrenceDeathJump_joint {n : ℕ} (a : Arm) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ => deathJump a p.1 p.2) := by
  unfold deathJump
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact (measurableSet_eq_fun
      (show Measurable (fun p : (Fin n → ObsHistory) × ℝ => (p.1 i).treatment) by fun_prop)
      measurable_const).inter
      ((measurableSet_eq_fun
        (show Measurable (fun p : (Fin n → ObsHistory) × ℝ => (p.1 i).deathInd) by fun_prop)
        measurable_const).inter
        (measurableSet_eq_fun
          (show Measurable (fun p : (Fin n → ObsHistory) × ℝ => (p.1 i).exit) by fun_prop)
          measurable_snd))
  · exact measurable_const
  · exact measurable_const

/-- The death Kaplan–Meier left limit is jointly measurable, with each distinct
exit time contributing its one aggregate decrement. -/
-- @node: measurable_recurrenceDeathKMLeft_joint
@[fun_prop]
lemma measurable_recurrenceDeathKMLeft_joint {n : ℕ} (a : Arm) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ => deathKMLeft a p.1 p.2) := by
  classical
  have heq : (fun p : (Fin n → ObsHistory) × ℝ => deathKMLeft a p.1 p.2) =
      fun p => ∏ u ∈ Finset.univ.image (fun i => (p.1 i).exit),
        if u < p.2 then 1 - invRisk a p.1 u * deathJump a p.1 u else 1 := by
    funext p
    simp only [deathKMLeft, exitTimes, Finset.prod_filter]
  rw [heq]
  apply measurable_recurrence_prod_image
  · intro i
    fun_prop
  · intro i
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_snd)
    · have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
          (p.1, (p.1 i).exit)) := by fun_prop
      exact measurable_const.sub
        (((measurable_recurrenceInvRisk_joint a).comp hm).mul
          ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
            ((measurable_recurrenceDeathJump_joint a).comp hm)))
    · exact measurable_const

/-- Subject point weights are jointly measurable in sample and time. -/
-- @node: measurable_recurrenceSubjectWeight_joint
@[fun_prop]
lemma measurable_recurrenceSubjectWeight_joint (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (i : Fin n) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      recurrenceSubjectWeight c h a p.1 i p.2) := by
  unfold recurrenceSubjectWeight
  apply Measurable.ite
  · exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_le measurable_snd (by fun_prop))
  · exact (((measurable_recurrenceContinuationWeight c h).comp measurable_snd).mul
      (measurable_recurrenceDeathKMLeft_joint a)).mul
      (measurable_recurrenceInvRisk_joint a)
  · exact measurable_const

/-- Exposure-only synthetic observations are measurable. -/
-- @node: measurable_recurrenceExposureHistory
@[fun_prop]
lemma measurable_recurrenceExposureHistory : Measurable recurrenceExposureHistory := by
  unfold recurrenceExposureHistory
  have hC : Measurable (fun e : Arm × (ℝ × ENNReal) =>
      if e.2.2 = ⊤ then (1 : ℝ) else min e.2.2.toReal 1) := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    · exact measurable_const
    · fun_prop
  have hd : Measurable (fun e : Arm × (ℝ × ENNReal) => decide (e.2.1 ≤
      (if e.2.2 = ⊤ then (1 : ℝ) else min e.2.2.toReal 1))) := by
    change Measurable (fun e : Arm × (ℝ × ENNReal) => if e.2.1 ≤
      (if e.2.2 = ⊤ then (1 : ℝ) else min e.2.2.toReal 1) then true else false)
    exact Measurable.ite (measurableSet_le (by fun_prop) hC) measurable_const measurable_const
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _
    (MeasurableSpace.comap ObsHistory.toCoordinates inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (measurable_fst.prodMk ((measurable_snd.fst.min hC).prodMk
    (hd.prodMk (measurable_const (a := RecurConfig.empty))))).comap_le

/-- A measurable score depending on exposure has a jointly measurable finite
configuration sum; a padded stream makes the random configuration size explicit. -/
-- @node: measurable_recurrence_param_point_sum
lemma measurable_recurrence_param_point_sum {E : Type*} [MeasurableSpace E]
    (f : E → (ℝ × ℝ) → ℝ)
    (hf : Measurable (fun p : E × (ℝ × ℝ) => f p.1 p.2)) :
    Measurable (fun p : E × RecurConfig => ∑ k : Fin p.2.1, f p.1 (p.2.2 k)) := by
  classical
  have hsum : Measurable (fun p : ℕ × (E × (ℕ → ℝ × ℝ)) =>
      ∑ k : Fin p.1, f p.2.1 (p.2.2 k)) := by
    apply measurable_from_prod_countable_right
    intro m
    change Measurable (fun y : E × (ℕ → ℝ × ℝ) =>
      ∑ k : Fin m, f y.1 (y.2 k))
    apply Finset.measurable_sum
    intro k _
    exact hf.comp (measurable_fst.prodMk
      ((measurable_pi_apply (k : ℕ)).comp measurable_snd))
  have hp := (finiteSamplePaddedStream_measurable ((0 : ℝ), (0 : ℝ))).comp
    (measurable_snd : Measurable (Prod.snd : E × RecurConfig → RecurConfig))
  have hm := hsum.comp (hp.fst.prodMk (measurable_fst.prodMk hp.snd))
  convert hm using 1
  funext p
  apply Finset.sum_congr rfl
  intro k _
  simp [finiteSamplePaddedStream, FiniteSample.count, FiniteSample.points, k.isLt]

/-- Integrated powers of recurrence weights are measurable in the observed
sample. A measurable version of the intensity suffices, since all integration
stays within the model's intensity domain. -/
-- @node: measurable_recurrenceWeightIntegral
@[fun_prop]
lemma measurable_recurrenceWeightIntegral (c : ClassConstants) (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) {n : ℕ} (i : Fin n)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (k : ℕ) :
    Measurable (fun s : Fin n → ObsHistory =>
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ k * P.lam a t) := by
  let hm := (hP a).1
  let g := hm.mk (P.lam a)
  have hg : Measurable g := hm.measurable_mk
  have hj : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      recurrenceSubjectWeight c h a p.1 i p.2 ^ k * g p.2) :=
    ((measurable_recurrenceSubjectWeight_joint c h a i).pow_const k).mul
      (hg.comp measurable_snd)
  have hi : Measurable (fun s : Fin n → ObsHistory =>
      ∫ t in Ioc (0 : ℝ) (1 - h), recurrenceSubjectWeight c h a s i t ^ k * g t) :=
    hj.stronglyMeasurable.integral_prod_right.measurable
  have heq : (fun s : Fin n → ObsHistory =>
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ k * P.lam a t) =
      fun s => ∫ t in Ioc (0 : ℝ) (1 - h),
        recurrenceSubjectWeight c h a s i t ^ k * g t := by
    funext s
    rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ 1 - h)]
    apply integral_congr_ae
    have ha := ae_restrict_of_ae_restrict_of_subset
      (show Ioc (0 : ℝ) (1 - h) ⊆ Ioc 0 1 from
        Ioc_subset_Ioc le_rfl (by linarith)) hm.ae_eq_mk
    filter_upwards [ha] with t ht
    rw [ht]
  rw [heq]
  exact hi

/-- The concrete score is jointly measurable in the exposure and recurrence
arrays. No compensation or moment premise is needed for this regularity. -/
-- @node: measurable_recurrenceConcreteExposureScore
@[fun_prop]
lemma measurable_recurrenceConcreteExposureScore (c : ClassConstants) (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) (n : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      recurrenceConcreteExposureScore c P a n h p.1 p.2) := by
  classical
  have hs : Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
      fun j => recurrenceExposureHistory (e j)) := by fun_prop
  unfold recurrenceConcreteExposureScore
  apply Finset.measurable_sum
  intro i _
  apply Measurable.sub
  · have hw : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (ℝ × ℝ) =>
        if p.2.1 ≤ 1 - h then recurrenceSubjectWeight c h a
          (fun j => recurrenceExposureHistory (p.1 j)) i p.2.1 else 0) := by
      apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      · exact (measurable_recurrenceSubjectWeight_joint c h a i).comp
          ((hs.comp measurable_fst).prodMk (by fun_prop))
      · exact measurable_const
    exact (measurable_recurrence_param_point_sum (E := Fin n → Arm × (ℝ × ENNReal))
      (fun e x => if x.1 ≤ 1 - h then recurrenceSubjectWeight c h a
        (fun j => recurrenceExposureHistory (e j)) i x.1 else 0) hw).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · simpa only [pow_one, Function.comp_def] using
      (measurable_recurrenceWeightIntegral c P hP a i hh hh1 1).comp
        (hs.comp measurable_fst)

/-- The unprojected recurrence estimator is measurable in the observed sample. -/
-- @node: measurable_recurrenceMuTildeAt
@[fun_prop]
lemma measurable_recurrenceMuTildeAt (c : ClassConstants) (h : ℝ)
    (a : Arm) (n : ℕ) : Measurable (muTildeAt c h a (n := n)) := by
  classical
  unfold muTildeAt
  apply Finset.measurable_sum
  intro i _
  have hm : Measurable (fun p : (Fin n → ObsHistory) × RecurConfig =>
      ∑ k : Fin p.2.1, if (p.2.2 k).1 ≤ 1 - h then
        continuationWeight (holderOrder c) h (p.2.2 k).1 *
          deathKMLeft a p.1 (p.2.2 k).1 * invRisk a p.1 (p.2.2 k).1 else 0) := by
    apply measurable_recurrence_param_point_sum (E := Fin n → ObsHistory)
      (fun s x => if x.1 ≤ 1 - h then continuationWeight (holderOrder c) h x.1 *
        deathKMLeft a s x.1 * invRisk a s x.1 else 0)
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    · have hx : Measurable (fun p : (Fin n → ObsHistory) × (ℝ × ℝ) =>
          (p.1, p.2.1)) := by fun_prop
      exact (((measurable_recurrenceContinuationWeight c h).comp (by fun_prop)).mul
        ((measurable_recurrenceDeathKMLeft_joint a).comp hx)).mul
          ((measurable_recurrenceInvRisk_joint a).comp hx)
    · exact measurable_const
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · have heq : (fun s : Fin n → ObsHistory =>
        (((s i).recur.times.filter (fun t => t ≤ 1 - h)).map
          (fun t => continuationWeight (holderOrder c) h t * deathKMLeft a s t *
            invRisk a s t)).sum) =
        fun s => ∑ k : Fin (s i).recur.1, if ((s i).recur.2 k).1 ≤ 1 - h then
          continuationWeight (holderOrder c) h ((s i).recur.2 k).1 *
            deathKMLeft a s ((s i).recur.2 k).1 * invRisk a s ((s i).recur.2 k).1
          else 0 := by
      funext s
      exact recurrence_times_filtered_sum _ _ _
    rw [heq]
    exact hm.comp (measurable_id.prodMk (by fun_prop))
  · exact measurable_const

/-- The recurrence error is measurable under the paper assumptions. -/
-- @node: measurable_recurrenceError
@[fun_prop]
lemma measurable_recurrenceError (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) :
    Measurable (fun s : Fin n → ObsHistory => recurrenceError c P a s h) := by
  have heq : (fun s : Fin n → ObsHistory => recurrenceError c P a s h) =
      fun s => muTildeAt c h a s - ∑ i : Fin n,
        ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t * P.lam a t := by
    funext s
    exact recurrenceError_eq_subject_compensators c P hP a s hh hh1
  rw [heq]
  apply (measurable_recurrenceMuTildeAt c h a n).sub
  apply Finset.measurable_sum
  intro i _
  simpa only [pow_one] using
    measurable_recurrenceWeightIntegral c P hP.poissonRecurrence a i hh.le hh1 1

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
