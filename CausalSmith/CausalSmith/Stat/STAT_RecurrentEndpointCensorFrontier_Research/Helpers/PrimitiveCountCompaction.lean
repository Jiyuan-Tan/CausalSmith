module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedInteriorObservableEquality

/-! # Primitive recurrence count and compaction -/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Compacting a finite sample at `x` preserves exactly the original points
whose times are at most both `x` and the later query threshold. -/
lemma countLE_stopAt_eq_sum (s : RecurConfig) (x t : ℝ) :
    (s.stopAt x).countLE t =
      ∑ i : Fin s.1, if (s.2 i).1 ≤ x ∧ (s.2 i).1 ≤ t then 1 else 0 := by
  classical
  rw [RecurConfig.stopAt_eq_restrictAt]
  unfold RecurConfig.restrictAt RecurConfig.countLE RecurConfig.paddedCountLE
  simp only [finiteSamplePaddedStream, FiniteMeasurablePartition.restrictCell,
    FiniteSample.count, FiniteSample.points]
  simp
  let u := (timeCutPartition x).cellIndices true s
  let v : Finset (Fin s.1) := Finset.univ.filter
    (fun i => (s.2 i).1 ≤ x ∧ (s.2 i).1 ≤ t)
  change (Finset.univ.filter (fun k : Fin u.card =>
    (s.2 ((u.orderIsoOfFin rfl k).1)).1 ≤ t)).card = v.card
  apply Finset.card_bij (fun k _ => (u.orderIsoOfFin rfl k).1)
  · intro k hk
    change (u.orderIsoOfFin rfl k).1 ∈ Finset.univ.filter
      (fun i : Fin s.1 => (s.2 i).1 ≤ x ∧ (s.2 i).1 ≤ t)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hu : (u.orderIsoOfFin rfl k).1 ∈ u := (u.orderIsoOfFin rfl k).2
    have hux : (s.2 ((u.orderIsoOfFin rfl k).1)).1 ≤ x := by
      simpa [u, FiniteMeasurablePartition.cellIndices, timeCutPartition,
        FiniteSample.points] using hu
    exact ⟨hux, (Finset.mem_filter.mp hk).2⟩
  · intro k1 _ k2 _ heq
    exact (u.orderIsoOfFin rfl).injective (Subtype.ext heq)
  · intro i hi
    change i ∈ Finset.univ.filter
      (fun i : Fin s.1 => (s.2 i).1 ≤ x ∧ (s.2 i).1 ≤ t) at hi
    have hip := (Finset.mem_filter.mp hi).2
    have hiu : i ∈ u := by
      simpa [u, FiniteMeasurablePartition.cellIndices, timeCutPartition,
        FiniteSample.points] using hip.1
    let k : Fin u.card := (u.orderIsoOfFin rfl).symm ⟨i, hiu⟩
    refine ⟨k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa [k] using hip.2⟩
    · simp [k]

/-- Away from recurrence points on stopping boundaries, the compacted paper
count is the strict primitive retained-point sum used by the promoted model. -/
lemma potentialStoppedRecurrenceCount_eq_strict_sum_of_no_boundary
    (z : LatentSubject) (a : Arm) (t : ℝ)
    (hb : ∀ i : Fin (z.recur a).1,
      ((z.recur a).2 i).1 ≠ z.death a ∧
      ((z.recur a).2 i).1 ≠ censorHorizon z a ∧
      ((z.recur a).2 i).1 ≠ 1) :
    potentialStoppedRecurrenceCountFromRest a t (latentRest z) =
      ∑ i : Fin (z.recur a).1,
        if ((z.recur a).2 i).1 < z.death a ∧
          ((z.recur a).2 i).1 < censorHorizon z a ∧
          ((z.recur a).2 i).1 < 1 ∧ ((z.recur a).2 i).1 ≤ t
        then (1 : ℝ≥0∞) else 0 := by
  rw [potentialStoppedRecurrenceCountFromRest_latentRest]
  rw [countLE_stopAt_eq_sum]
  norm_cast
  apply Finset.sum_congr rfl
  intro i _
  have hc : censorHorizon z a ≤ 1 := by
    unfold censorHorizon
    split_ifs <;> simp
  by_cases hkeep : ((z.recur a).2 i).1 ≤
      min (z.death a) (censorHorizon z a) ∧ ((z.recur a).2 i).1 ≤ t
  · have hdle := hkeep.1.trans (min_le_left _ _)
    have hcle := hkeep.1.trans (min_le_right _ _)
    have hd : ((z.recur a).2 i).1 < z.death a :=
      lt_of_le_of_ne hdle (hb i).1
    have hci : ((z.recur a).2 i).1 < censorHorizon z a :=
      lt_of_le_of_ne hcle (hb i).2.1
    have h1 : ((z.recur a).2 i).1 < 1 := hci.trans_le hc
    simp [hkeep, hd, hci, h1]
  · have hstrict : ¬(((z.recur a).2 i).1 < z.death a ∧
        ((z.recur a).2 i).1 < censorHorizon z a ∧
        ((z.recur a).2 i).1 < 1 ∧ ((z.recur a).2 i).1 ≤ t) := by
      intro h
      exact hkeep ⟨le_min h.1.le h.2.1.le, h.2.2.2⟩
    rw [if_neg hkeep, if_neg hstrict]

lemma promotedArmModel_primitiveRecurrenceCountSet_Iic
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (t : ℝ) (z : LatentSubject) :
    (promotedArmModel P hP a).primitiveRecurrenceCountSet () (Set.Iic t)
        ((), z.recur a, z.death a, censorHorizon z a) =
      ∑ i : Fin (z.recur a).1,
        if ((z.recur a).2 i).1 < z.death a ∧
          ((z.recur a).2 i).1 < censorHorizon z a ∧
          ((z.recur a).2 i).1 < 1 ∧ ((z.recur a).2 i).1 ≤ t
        then (1 : ℝ≥0∞) else 0 := by
  unfold Causalean.Stat.RecurrentEvent.Model.primitiveRecurrenceCountSet
    Causalean.Stat.RecurrentEvent.Model.stopTime
  simp only [promotedArmModel_horizon, promotedArmModel_time, Set.mem_Iic,
    true_and, lt_min_iff]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply propext
  tauto

/-- The strict retained-point count as a function of a recurrence sample and
the pair of death and censor times. -/
@[no_expose]
noncomputable def strictPrimitiveRecurrenceCountIic (t : ℝ)
    (q : RecurConfig × (ℝ × ℝ)) : ℝ≥0∞ :=
  ∑ i : Fin q.1.1,
    if (q.1.2 i).1 < q.2.1 ∧ (q.1.2 i).1 < q.2.2 ∧
      (q.1.2 i).1 < 1 ∧ (q.1.2 i).1 ≤ t
    then 1 else 0

set_option maxHeartbeats 800000 in
@[fun_prop]
lemma measurable_strictPrimitiveRecurrenceCountIic (t : ℝ) :
    Measurable (strictPrimitiveRecurrenceCountIic t) := by
  let F := strictPrimitiveRecurrenceCountIic t
  have he (n : ℕ) : MeasurableEmbedding
      (fixedSizeEmbed (X := ℝ × ℝ) n) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    · exact measurable_fixedSizeEmbed n
    · intro s hs
      change @MeasurableSet _
        (⨅ m, (inferInstance : MeasurableSpace (Fin m → ℝ × ℝ)).map (Sigma.mk m))
        (fixedSizeEmbed n '' s)
      rw [MeasurableSpace.measurableSet_iInf]
      intro m
      change MeasurableSet (fixedSizeEmbed m ⁻¹' (fixedSizeEmbed n '' s))
      by_cases h : m = n
      · subst m
        rw [Set.preimage_image_eq s (fun x y h ↦
          eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
        exact hs
      · convert MeasurableSet.empty using 1
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨y, _, heq⟩
        exact h (congrArg Sigma.fst heq).symm
  intro s hs
  have hpre : F ⁻¹' s = ⋃ n : ℕ,
      (Prod.map (fixedSizeEmbed (X := ℝ × ℝ) n) id) ''
        {q : (Fin n → ℝ × ℝ) × (ℝ × ℝ) | F (⟨n, q.1⟩, q.2) ∈ s} := by
    ext ⟨⟨n, x⟩, r⟩
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨n, ⟨(x, r), h, rfl⟩⟩
    · rintro h
      obtain ⟨m, ⟨y, r⟩, hy, hz⟩ := Set.mem_iUnion.mp h
      cases hz
      exact hy
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  apply ((he n).prodMap MeasurableEmbedding.id).measurableSet_image.mpr
  apply hs.preimage
  change Measurable (fun q : (Fin n → ℝ × ℝ) × (ℝ × ℝ) ↦
    ∑ i : Fin n,
      if (q.1 i).1 < q.2.1 ∧ (q.1 i).1 < q.2.2 ∧
        (q.1 i).1 < 1 ∧ (q.1 i).1 ≤ t
      then (1 : ℝ≥0∞) else 0)
  apply Finset.measurable_sum Finset.univ
  intro i _
  have htime : Measurable
      (fun q : (Fin n → ℝ × ℝ) × (ℝ × ℝ) ↦ (q.1 i).1) := by
    fun_prop
  have hone : Measurable
      (fun _ : (Fin n → ℝ × ℝ) × (ℝ × ℝ) ↦ (1 : ℝ)) := measurable_const
  have htconst : Measurable
      (fun _ : (Fin n → ℝ × ℝ) × (ℝ × ℝ) ↦ t) := measurable_const
  exact Measurable.ite
    ((measurableSet_lt htime (measurable_fst.comp measurable_snd)).inter
      ((measurableSet_lt htime (measurable_snd.comp measurable_snd)).inter
        ((measurableSet_lt htime hone).inter
          (measurableSet_le htime htconst))))
    measurable_const measurable_const

/-- The promoted primitive recurrence count on a lower ray is globally
measurable, including across the variable finite-sample size. -/
lemma measurable_promotedArmModel_primitiveRecurrenceCountSet_Iic
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (t : ℝ) :
    Measurable (fun ω ↦
      (promotedArmModel P hP a).primitiveRecurrenceCountSet () (Set.Iic t) ω) := by
  have heq : (fun ω ↦
      (promotedArmModel P hP a).primitiveRecurrenceCountSet () (Set.Iic t) ω) =
      fun ω ↦ strictPrimitiveRecurrenceCountIic t (ω.2.1, ω.2.2) := by
    funext ω
    rcases ω with ⟨u, s, d, k⟩
    unfold Causalean.Stat.RecurrentEvent.Model.primitiveRecurrenceCountSet
      Causalean.Stat.RecurrentEvent.Model.stopTime
      strictPrimitiveRecurrenceCountIic
    simp only [promotedArmModel_horizon, promotedArmModel_time, Set.mem_Iic,
      true_and, lt_min_iff]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply propext
    tauto
  rw [heq]
  exact (measurable_strictPrimitiveRecurrenceCountIic t).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))

/-- A promoted arm's recurrence-event CDF is the latent integral of the
paper compacted stopped count.  Boundary nullity removes the sole strict
versus non-strict discrepancy. -/
lemma ModelClass.promotedArmModel_recurrenceEventMeasure_Iic
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (t : ℝ) :
    (promotedArmModel P hP a).recurrenceEventMeasure () (Set.Iic t) =
      ∫⁻ z, potentialStoppedRecurrenceCountFromRest a t (latentRest z)
        ∂P.latent := by
  let M := promotedArmModel P hP a
  rw [M.recurrence_event_measure_primitive () (Set.Iic t) measurableSet_Iic]
  rw [← hP.map_latentToPromotedArmOutcome_eq_primitiveLaw a]
  rw [lintegral_map
    (measurable_promotedArmModel_primitiveRecurrenceCountSet_Iic hP a t)
    (show Measurable (fun z : LatentSubject ↦
        ((), z.recur a, z.death a, censorHorizon z a)) by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hP.ae_no_recurrence_at_stopping_boundaries a] with z hb
  rw [promotedArmModel_primitiveRecurrenceCountSet_Iic hP a t z]
  exact (potentialStoppedRecurrenceCount_eq_strict_sum_of_no_boundary
    z a t hb).symm

/-- The paper cumulative recurrence observable is assignment mass times the
promoted arm recurrence-event CDF. -/
lemma ModelClass.observedArmRecurrenceCumulative_eq_promoted_Iic
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (t : ℝ) :
    observedArmRecurrenceCumulative P a t = ENNReal.ofReal (P.p a) *
      (promotedArmModel P hP a).recurrenceEventMeasure () (Set.Iic t) := by
  rw [hP.observedArmRecurrenceCumulative_factor a t,
    hP.promotedArmModel_recurrenceEventMeasure_Iic a t]

/-- Equal paper observed laws identify every lower-ray mass of each promoted
arm recurrence-event measure. -/
lemma promotedArmModel_recurrenceEventMeasure_Iic_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm) (t : ℝ) :
    (promotedArmModel P hP a).recurrenceEventMeasure () (Set.Iic t) =
      (promotedArmModel Q hQ a).recurrenceEventMeasure () (Set.Iic t) := by
  have hp := hP.assignmentProbability_eq_of_observedLaw_eq hQ hobs a
  have hm := observedArmRecurrenceCumulative_congr hobs a t
  rw [hP.observedArmRecurrenceCumulative_eq_promoted_Iic a t,
    hQ.observedArmRecurrenceCumulative_eq_promoted_Iic a t, ← hp] at hm
  have hzero : ENNReal.ofReal (P.p a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le c.pMin_pos (hP.treatmentOverlap a))).ne'
  have htop : ENNReal.ofReal (P.p a) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj hzero htop).mp
  simpa [mul_comm] using hm


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
