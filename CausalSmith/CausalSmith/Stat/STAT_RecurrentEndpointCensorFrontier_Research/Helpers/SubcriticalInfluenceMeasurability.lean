module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

/-!
# An almost-everywhere measurable subcritical influence representative

The model controls intensities and hazards on the study horizon.  This file
extends the two compensator densities by zero off that horizon, producing a
globally measurable representative that agrees with the paper influence on
the almost-sure support of observed exit times.
-/

@[expose] public section

open MeasureTheory Set Filter
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The recurrence compensator density, extended by zero off the study horizon. -/
noncomputable def subcriticalRecurrenceDensity (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 1).indicator (fun u => P.lam a u / retention P a u) t

/-- The death compensator density, extended by zero off the study horizon. -/
noncomputable def subcriticalDeathDensity (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 1).indicator (fun u =>
    remainingTarget c P a 0 u * P.hazard a u /
      (survival P a u * retention P a u)) t

/-- An unfiltered finite event sum is its finite indexed point sum. -/
lemma recurrence_times_sum (s : RecurConfig) (f : ℝ → ℝ) :
    (s.times.map f).sum = ∑ k : Fin s.1, f (s.2 k).1 := by
  simp [RecurConfig.times, FiniteSample.count, FiniteSample.points,
    List.map_ofFn, List.sum_ofFn]

/-- The inverse-retention point sum of an observed recurrence configuration is measurable. -/
lemma measurable_subcriticalRecurrencePointSum (P : SubjectLaw) (a : Arm) :
    Measurable (fun o : ObsHistory =>
      Multiset.sum (o.recur.times.map (fun t => (retention P a t)⁻¹))) := by
  have hm : Measurable (fun q : Unit × RecurConfig =>
      ∑ k : Fin q.2.1, (retention P a (q.2.2 k).1)⁻¹) := by
    apply measurable_recurrence_param_point_sum
      (fun (_ : Unit) (x : ℝ × ℝ) => (retention P a x.1)⁻¹)
    exact ((measurable_retention P a).comp (by fun_prop)).inv
  have heq : (fun o : ObsHistory =>
      Multiset.sum (o.recur.times.map (fun t => (retention P a t)⁻¹))) =
      fun o => ∑ k : Fin o.recur.1, (retention P a (o.recur.2 k).1)⁻¹ := by
    funext o
    exact recurrence_times_sum _ _
  rw [heq]
  exact hm.comp
    ((show Measurable (fun _ : ObsHistory => ()) from measurable_const).prodMk
      measurable_obsHistory_recur)

/-- Both zero-extended compensator densities are integrable in the subcritical regime. -/
lemma integrable_subcriticalInfluenceDensities (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm) :
    Integrable (subcriticalRecurrenceDensity P a) ∧
      Integrable (subcriticalDeathDensity c P a) := by
  have hinv := inv_retention_intervalIntegrable_subcritical c P hP hk a
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hinv
  have hlam := (hP.recurrenceHolder a).1.continuousOn
  obtain ⟨BL, hBL⟩ := isCompact_Icc.exists_bound_of_continuousOn hlam
  have hrOn : IntegrableOn (fun t => P.lam a t * (retention P a t)⁻¹)
      (Icc (0 : ℝ) 1) := hinv.bdd_mul
        (hlam.aestronglyMeasurable measurableSet_Icc)
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hBL t ht)
  let q : ℝ → ℝ := fun t => remainingTarget c P a 0 t * P.hazard a t /
    survival P a t
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) :=
    ((continuousOn_remainingTarget_zero c P hP a).mul
      (hP.deathHolder a).1.continuousOn).div
      (modelClass_survival_continuousOn c P hP a) (fun t _ => (Real.exp_pos _).ne')
  obtain ⟨BD, hBD⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hdOn : IntegrableOn (fun t => q t * (retention P a t)⁻¹)
      (Icc (0 : ℝ) 1) := hinv.bdd_mul
        (hq.aestronglyMeasurable measurableSet_Icc)
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hBD t ht)
  constructor
  · have hi := hrOn.integrable_indicator measurableSet_Icc
    have heq : subcriticalRecurrenceDensity P a =
        (Icc (0 : ℝ) 1).indicator (fun t => P.lam a t * (retention P a t)⁻¹) := by
      funext t
      by_cases ht : t ∈ Icc (0 : ℝ) 1 <;>
        simp [subcriticalRecurrenceDensity, Set.indicator, ht, div_eq_mul_inv]
    rw [heq]
    exact hi
  · have hi := hdOn.integrable_indicator measurableSet_Icc
    have heq : (Icc (0 : ℝ) 1).indicator (fun u =>
        remainingTarget c P a 0 u * P.hazard a u /
          (survival P a u * retention P a u)) =
        (Icc (0 : ℝ) 1).indicator (fun u => q u * (retention P a u)⁻¹) := by
      funext u
      by_cases hu : u ∈ Icc (0 : ℝ) 1
      · simp only [Set.indicator_of_mem hu]
        dsimp [q]
        ring
      · simp [Set.indicator, Set.piecewise, hu]
    change Integrable ((Icc (0 : ℝ) 1).indicator (fun u =>
      remainingTarget c P a 0 u * P.hazard a u /
        (survival P a u * retention P a u)))
    rw [heq]
    exact hi

/-- A globally measurable representative of the paper's subcritical influence. -/
noncomputable def measurableSubcriticalInfluence (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (o : ObsHistory) : ℝ :=
  (if o.treatment = a then
    Multiset.sum (o.recur.times.map (fun t => (retention P a t)⁻¹)) -
      ∫ t in (0 : ℝ)..o.exit, subcriticalRecurrenceDensity P a t
    else 0) / P.p a -
  (if o.treatment = a then
    (if o.deathInd then
      deathTargetWeight c P a 0 o.exit * (retention P a o.exit)⁻¹ else 0) -
      ∫ t in (0 : ℝ)..o.exit, subcriticalDeathDensity c P a t
    else 0) / P.p a

/-- The zero-extended representative is globally measurable. -/
lemma measurable_measurableSubcriticalInfluence (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm) :
    Measurable (measurableSubcriticalInfluence c P a) := by
  have hi := integrable_subcriticalInfluenceDensities c P hP hk a
  have hrPrim : Measurable (fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, subcriticalRecurrenceDensity P a t) :=
    (hi.1.continuous_primitive 0).measurable
  have hdPrim : Measurable (fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, subcriticalDeathDensity c P a t) :=
    (hi.2.continuous_primitive 0).measurable
  unfold measurableSubcriticalInfluence
  have hr : Measurable (fun o : ObsHistory =>
      (if o.treatment = a then
        Multiset.sum (o.recur.times.map (fun t => (retention P a t)⁻¹)) -
          ∫ t in (0 : ℝ)..o.exit, subcriticalRecurrenceDensity P a t else 0) /
        P.p a) := (Measurable.ite
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const)
    ((measurable_subcriticalRecurrencePointSum P a).sub
      (hrPrim.comp measurable_obsHistory_exit)) measurable_const).div_const _
  have hd : Measurable (fun o : ObsHistory =>
      (if o.treatment = a then
        (if o.deathInd then deathTargetWeight c P a 0 o.exit *
          (retention P a o.exit)⁻¹ else 0) -
          ∫ t in (0 : ℝ)..o.exit, subcriticalDeathDensity c P a t else 0) /
        P.p a) := (Measurable.ite
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const) ?_
    measurable_const).div_const _
  · exact hr.sub hd
  apply (Measurable.ite
    (measurableSet_eq_fun measurable_obsHistory_deathInd measurable_const)
    (((measurable_deathTargetWeight c P hP a (by norm_num) (by norm_num)).comp
      measurable_obsHistory_exit).mul
      ((measurable_retention P a).inv.comp measurable_obsHistory_exit))
    measurable_const).sub
  exact hdPrim.comp measurable_obsHistory_exit

/-- Observed exits lie in the study horizon almost surely. -/
lemma observed_exit_mem_Icc_ae (P : SubjectLaw) (hDeath : DeathHazard P) :
    ∀ᵐ o ∂observedLaw P, o.exit ∈ Icc (0 : ℝ) 1 := by
  have hlo : ∀ᵐ o ∂observedLaw P, 0 ≤ o.exit := by
    rw [observedLaw]
    apply (ae_map_iff measurable_observe.aemeasurable
      (measurableSet_le measurable_const measurable_obsHistory_exit)).mpr
    have hDeathNonneg (a : Arm) : ∀ᵐ z ∂P.latent, 0 ≤ z.death a := by
      letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
      have htail : P.latent.real {z | (0 : ℝ) ≤ z.death a} = 1 := by
        simpa [survival] using hDeath.2.2.2.1 a 0 (by norm_num)
      have hmeas : MeasurableSet {z : LatentSubject | (0 : ℝ) ≤ z.death a} :=
        measurableSet_le measurable_const (measurable_latentSubject_death a)
      have hcomp := measureReal_compl (μ := P.latent) hmeas
      have huniv : P.latent.real Set.univ = 1 := by simp [Measure.real, P.prob]
      rw [htail, huniv] at hcomp
      apply ae_iff.mpr
      have hzero : P.latent.real {z | ¬(0 : ℝ) ≤ z.death a} = 0 := by
        simpa [compl_setOf] using hcomp
      simpa only [not_not] using ((measureReal_eq_zero_iff).mp hzero)
    filter_upwards [hDeathNonneg false, hDeathNonneg true] with z h0 h1
    have hd : 0 ≤ z.death z.treatment := by cases z.treatment <;> assumption
    have hc : 0 ≤ censorHorizon z z.treatment := by
      unfold censorHorizon
      split_ifs <;> positivity
    simpa only [observe] using le_min hd hc
  have hhi : ∀ᵐ o ∂observedLaw P, o.exit ≤ 1 := by
    rw [observedLaw]
    apply (ae_map_iff measurable_observe.aemeasurable
      (measurableSet_le measurable_obsHistory_exit measurable_const)).mpr
    apply Filter.Eventually.of_forall
    intro z
    have hc : censorHorizon z z.treatment ≤ 1 := by
      unfold censorHorizon
      split_ifs <;> simp
    simpa only [observe] using
      (min_le_right (z.death z.treatment) (censorHorizon z z.treatment)).trans hc
  filter_upwards [hlo, hhi] with o ho hlo
  exact ⟨ho, hlo⟩

/-- On the study horizon, the measurable representative equals the paper influence. -/
lemma measurableSubcriticalInfluence_eq (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (o : ObsHistory) (ho : o.exit ∈ Icc (0 : ℝ) 1) :
    measurableSubcriticalInfluence c P a o = subcriticalInfluence c P a o := by
  have hr : (∫ t in (0 : ℝ)..o.exit, subcriticalRecurrenceDensity P a t) =
      ∫ t in (0 : ℝ)..o.exit, P.lam a t / retention P a t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ho.1] at ht
    simp [subcriticalRecurrenceDensity, Set.indicator,
      show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, ht.2.trans ho.2⟩]
  have hd : (∫ t in (0 : ℝ)..o.exit, subcriticalDeathDensity c P a t) =
      ∫ t in (0 : ℝ)..o.exit,
        remainingTarget c P a 0 t * P.hazard a t /
          (survival P a t * retention P a t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ho.1] at ht
    simp [subcriticalDeathDensity, Set.indicator,
      show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, ht.2.trans ho.2⟩]
  have hw : deathTargetWeight c P a 0 o.exit =
      remainingTarget c P a 0 o.exit / survival P a o.exit := by
    simp [deathTargetWeight, ho]
  unfold measurableSubcriticalInfluence subcriticalInfluence
  rw [hr, hd, hw]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The paper influence equals its measurable representative almost surely. -/
lemma subcriticalInfluence_ae_eq_measurableRepresentative (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) :
    subcriticalInfluence c P a =ᵐ[observedLaw P]
      measurableSubcriticalInfluence c P a := by
  filter_upwards [observed_exit_mem_Icc_ae P hP.deathHazard] with o ho
  exact (measurableSubcriticalInfluence_eq c P hP a o ho).symm

/-- The original paper influence is almost-everywhere measurable under the observed law. -/
lemma aemeasurable_subcriticalInfluence (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm) :
    AEMeasurable (subcriticalInfluence c P a) (observedLaw P) := by
  exact (measurable_measurableSubcriticalInfluence c P hP hk a).aemeasurable.congr
    (subcriticalInfluence_ae_eq_measurableRepresentative c P hP a).symm

/-- The representative equality transfers simultaneously to every coordinate of an iid sample. -/
lemma sample_subcriticalInfluence_ae_eq_measurableRepresentative (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (fun s : Fin n → ObsHistory => fun i => subcriticalInfluence c P a (s i)) =ᵐ[sampleLaw P n]
      fun s => fun i => measurableSubcriticalInfluence c P a (s i) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw
    infer_instance
  have hall : ∀ᵐ s ∂sampleLaw P n, ∀ i,
      subcriticalInfluence c P a (s i) = measurableSubcriticalInfluence c P a (s i) := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval
      (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving.ae_eq
      (subcriticalInfluence_ae_eq_measurableRepresentative c P hP a)
  filter_upwards [hall] with s hs
  funext i
  exact hs i

/-- Finite iid sums may be replaced by sums of the measurable representative almost surely. -/
lemma sum_subcriticalInfluence_ae_eq_measurableRepresentative (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (fun s : Fin n → ObsHistory => ∑ i, subcriticalInfluence c P a (s i)) =ᵐ[sampleLaw P n]
      fun s => ∑ i, measurableSubcriticalInfluence c P a (s i) := by
  filter_upwards [sample_subcriticalInfluence_ae_eq_measurableRepresentative c P hP a n]
    with s hs
  exact Finset.sum_congr rfl (fun i _ => congrFun hs i)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
