module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationObservables
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedConditionalObservedLaw

/-! # Observable transport through armwise compaction -/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

abbrev LatentRest :=
  (Arm → RecurConfig) × (Arm → ℝ) × (Arm → ENNReal)

@[no_expose]
def latentRest (z : LatentSubject) : LatentRest :=
  (z.recur, z.death, z.censor)

@[fun_prop] lemma measurable_latentRest : Measurable latentRest := by
  unfold latentRest
  fun_prop

/-- Restricting to one assigned arm and then observing any measurable
functional of the potential-outcome block multiplies its unconditional law
by the assignment probability. -/
lemma ModelClass.map_restrict_treatment_comp_latentRest
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) {Y : Type*} [MeasurableSpace Y]
    (g : LatentRest → Y) (hg : Measurable g) :
    Measure.map (g ∘ latentRest)
        (P.latent.restrict {z : LatentSubject | z.treatment = a}) =
      ENNReal.ofReal (P.p a) • Measure.map (g ∘ latentRest) P.latent := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  apply Measure.ext
  intro s hs
  have haSet : MeasurableSet ({a} : Set Arm) := measurableSet_singleton a
  have hrestSet : MeasurableSet (g ⁻¹' s) := hs.preimage hg
  rw [Measure.map_apply (hg.comp measurable_latentRest) hs,
    Measure.restrict_apply (hs.preimage (hg.comp measurable_latentRest)),
    Measure.smul_apply, Measure.map_apply (hg.comp measurable_latentRest) hs]
  rw [Set.inter_comm]
  change P.latent
      ((fun z : LatentSubject ↦ z.treatment) ⁻¹' ({a} : Set Arm) ∩
        latentRest ⁻¹' (g ⁻¹' s)) = _
  unfold latentRest
  rw [hP.randomAssignment.measure_inter_preimage_eq_mul
    ({a} : Set Arm) (g ⁻¹' s) haSet hrestSet]
  congr 1
  rw [← hP.assignmentLaw a]
  exact (ENNReal.ofReal_toReal (measure_ne_top P.latent _)).symm

/-- Integral form of arm randomization for any nonnegative measurable
potential-outcome functional. -/
lemma ModelClass.lintegral_treatment_indicator_factor
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (g : LatentRest → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, (if z.treatment = a then g (latentRest z) else 0) ∂P.latent) =
      ENNReal.ofReal (P.p a) * ∫⁻ z, g (latentRest z) ∂P.latent := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let w : Arm → ℝ≥0∞ := fun b ↦ if b = a then 1 else 0
  have hw : Measurable w := measurable_of_finite w
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hw.comp measurable_latentSubject_treatment)
    (hg.comp measurable_latentRest)
    (hP.randomAssignment.comp hw hg)
  have hwint : (∫⁻ z, w z.treatment ∂P.latent) =
      ENNReal.ofReal (P.p a) := by
    have hevent : (fun z : LatentSubject ↦ w z.treatment) =
        {z | z.treatment = a}.indicator 1 := by
      funext z
      simp [w, Set.indicator]
    rw [hevent, lintegral_indicator_one]
    · rw [← hP.assignmentLaw a]
      exact (ENNReal.ofReal_toReal (measure_ne_top P.latent _)).symm
    · exact measurableSet_eq_fun measurable_latentSubject_treatment measurable_const
  calc
    (∫⁻ z, (if z.treatment = a then g (latentRest z) else 0) ∂P.latent) =
        ∫⁻ z, w z.treatment * g (latentRest z) ∂P.latent := by
      apply lintegral_congr
      intro z
      by_cases h : z.treatment = a <;> simp [w, h]
    _ = (∫⁻ z, w z.treatment ∂P.latent) *
        ∫⁻ z, g (latentRest z) ∂P.latent := hfactor
    _ = _ := by rw [hwint]

/-- The observed arm mass recovers the paper assignment probability. -/
lemma ModelClass.observedLaw_arm_mass
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    observedLaw P {o : ObsHistory | o.treatment = a} =
      ENNReal.ofReal (P.p a) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  rw [observedLaw, Measure.map_apply measurable_observe
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const)]
  change P.latent {z : LatentSubject | z.treatment = a} = _
  rw [← hP.assignmentLaw a]
  exact (ENNReal.ofReal_toReal (measure_ne_top P.latent _)).symm

/-- Equal paper observed laws identify each assignment probability. -/
lemma ModelClass.assignmentProbability_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm) :
    P.p a = Q.p a := by
  have hmass : ENNReal.ofReal (P.p a) = ENNReal.ofReal (Q.p a) := by
    rw [← hP.observedLaw_arm_mass a, ← hQ.observedLaw_arm_mass a, hobs]
  exact (ENNReal.ofReal_eq_ofReal_iff
    (le_trans c.pMin_pos.le (hP.treatmentOverlap a))
    (le_trans c.pMin_pos.le (hQ.treatmentOverlap a))).mp hmass

@[no_expose]
noncomputable def potentialExitFromRest (a : Arm) (r : LatentRest) : ℝ :=
  min (r.2.1 a) (censorHorizonValue (r.2.2 a))

@[fun_prop] lemma measurable_potentialExitFromRest (a : Arm) :
    Measurable (potentialExitFromRest a) := by
  unfold potentialExitFromRest
  fun_prop

@[no_expose]
noncomputable def potentialStoppedRecurrenceCountFromRest
    (a : Arm) (t : ℝ) (r : LatentRest) : ℝ≥0∞ :=
  (((r.1 a).stopAt
    (min (r.2.1 a) (censorHorizonValue (r.2.2 a)))).countLE t : ℕ)

lemma potentialStoppedRecurrenceCountFromRest_latentRest
    (z : LatentSubject) (a : Arm) (t : ℝ) :
    potentialStoppedRecurrenceCountFromRest a t (latentRest z) =
      (((z.recur a).stopAt
        (min (z.death a) (censorHorizon z a))).countLE t : ℕ) := by
  rfl

set_option maxHeartbeats 800000 in
lemma measurable_potentialStoppedRecurrenceCountFromRest
    (a : Arm) (t : ℝ) :
    Measurable (potentialStoppedRecurrenceCountFromRest a t) := by
  unfold potentialStoppedRecurrenceCountFromRest
  have hexit : Measurable (fun r : LatentRest ↦
      min (r.2.1 a) (censorHorizonValue (r.2.2 a))) := by fun_prop
  have hrecur : Measurable (fun r : LatentRest ↦ r.1 a) := by fun_prop
  have hstop : Measurable (fun r : LatentRest ↦
      (r.1 a).stopAt (min (r.2.1 a) (censorHorizonValue (r.2.2 a)))) :=
    RecurConfig.measurable_stopAt.comp (hexit.prodMk hrecur)
  have hcount : Measurable (fun r : LatentRest ↦
      ((r.1 a).stopAt
        (min (r.2.1 a) (censorHorizonValue (r.2.2 a)))).countLE t) :=
    RecurConfig.measurable_countLE.comp (measurable_const.prodMk hstop)
  exact (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp hcount

/-- The paper cumulative recurrence observable is the assignment-scaled
potential compacted count integral. -/
lemma ModelClass.observedArmRecurrenceCumulative_factor
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (t : ℝ) :
    observedArmRecurrenceCumulative P a t = ENNReal.ofReal (P.p a) *
      ∫⁻ z, potentialStoppedRecurrenceCountFromRest a t (latentRest z)
        ∂P.latent := by
  rw [observedArmRecurrenceCumulative_eq_latent]
  have hfac := hP.lintegral_treatment_indicator_factor a
    (potentialStoppedRecurrenceCountFromRest a t)
    (measurable_potentialStoppedRecurrenceCountFromRest a t)
  convert hfac using 1
  apply lintegral_congr
  intro z
  unfold latentStoppedArmRecurrenceCount
    potentialStoppedRecurrenceCountFromRest latentRest
  simp only [censorHorizon_eq_value]

/-- Compaction preserves the risk observable: the paper arm-specific mass is
the assignment probability times the promoted Unit-arm risk probability. -/
lemma ModelClass.observedArmAtRiskMass_eq_promoted
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) (t : ℝ) :
    observedArmAtRiskMass P a t =
      ENNReal.ofReal (P.p a) *
        (promotedArmModel P hP a).riskProbability () t := by
  let M := promotedArmModel P hP a
  let e : LatentRest → ℝ := potentialExitFromRest a
  have he : Measurable e := measurable_potentialExitFromRest a
  have hmap := hP.map_restrict_treatment_comp_latentRest a e he
  have heval := congrArg (fun μ : Measure ℝ ↦ μ (Set.Ici t)) hmap
  rw [Measure.map_apply (he.comp measurable_latentRest) measurableSet_Ici,
    Measure.smul_apply,
    Measure.map_apply (he.comp measurable_latentRest) measurableSet_Ici] at heval
  rw [Measure.restrict_apply
    (measurableSet_Ici.preimage (he.comp measurable_latentRest))] at heval
  rw [observedArmAtRiskMass_eq_latent]
  calc
    P.latent (latentArmAtRisk a t) =
        P.latent ((e ∘ latentRest) ⁻¹' Set.Ici t ∩
          {z : LatentSubject | z.treatment = a}) := by
      congr 1
      ext z
      simp [latentArmAtRisk, e, potentialExitFromRest, latentRest,
        censorHorizon_eq_value, and_comm]
    _ = ENNReal.ofReal (P.p a) *
        P.latent ((e ∘ latentRest) ⁻¹' Set.Ici t) := heval
    _ = ENNReal.ofReal (P.p a) * M.riskProbability () t := by
      congr 1
      rw [Causalean.Stat.RecurrentEvent.Model.riskProbability,
        hP.promotedArmModel_observedLaw_eq_map_latent a,
        Measure.map_apply]
      · congr 1
        ext z
        have hc : censorHorizonValue (z.censor a) ≤ 1 := by
          unfold censorHorizonValue
          split_ifs <;> simp
        simp [Causalean.Stat.RecurrentEvent.Model.observe,
          Causalean.Stat.RecurrentEvent.Model.stopTime, e,
          potentialExitFromRest, latentRest, censorHorizon_eq_value,
          min_assoc, min_left_comm, min_comm, hc]
        exact fun _ htc ↦ htc.trans hc
      · apply M.measurable_observe.comp
        exact measurable_const.prodMk
          ((measurable_latentSubject_recur a).prodMk
            ((measurable_latentSubject_death a).prodMk
              (measurable_censorHorizon.comp
                (measurable_id.prodMk measurable_const))))
      · measurability

/-- Equality of paper observed laws identifies the promoted armwise risk
probability despite the raw recurrence-stream representation mismatch. -/
lemma promotedArmModel_riskProbability_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm) (t : ℝ) :
    (promotedArmModel P hP a).riskProbability () t =
      (promotedArmModel Q hQ a).riskProbability () t := by
  have hp := hP.assignmentProbability_eq_of_observedLaw_eq hQ hobs a
  have hm := observedArmAtRiskMass_congr hobs a t
  rw [hP.observedArmAtRiskMass_eq_promoted a t,
    hQ.observedArmAtRiskMass_eq_promoted a t, ← hp] at hm
  have hzero : ENNReal.ofReal (P.p a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le c.pMin_pos (hP.treatmentOverlap a))).ne'
  have htop : ENNReal.ofReal (P.p a) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj hzero htop).mp
  simpa [mul_comm] using hm

/-- Equality of paper observed laws identifies the complete promoted
armwise risk-set measures. -/
lemma promotedArmModel_riskSetMeasure_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm) :
    (promotedArmModel P hP a).riskSetMeasure () =
      (promotedArmModel Q hQ a).riskSetMeasure () := by
  let M := promotedArmModel P hP a
  let N := promotedArmModel Q hQ a
  unfold Causalean.Stat.RecurrentEvent.Model.riskSetMeasure
  simp only [promotedArmModel_horizon]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  rw [← M.risk_factorization () t (by simpa [M] using ht'),
    ← N.risk_factorization () t (by simpa [N] using ht')]
  exact promotedArmModel_riskProbability_eq_of_observedLaw_eq hP hQ hobs a t


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
