module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionVariance
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceMeasurability

/-!
# Measurable influence for the positive-retention benchmark

Roadmap (25): the compensator densities are integrable with only measurable
hazards and horizon retention. Their continuous primitives and the bounded
measurable death multiplier give an observable influence representative.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Positive horizon retention makes both full-horizon influence compensators
integrable without endpoint smoothness. -/
-- @node: positiveRetention_integrable_influenceDensities
lemma positiveRetention_integrable_influenceDensities (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Integrable (subcriticalRecurrenceDensity P a) ∧
      Integrable (subcriticalDeathDensity c P a) := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  have hl : Integrable (P.lam a) ν :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (poissonRecurrence_intervalIntegrable P hPoisson a)
  have hd : Integrable (P.hazard a) ν :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hDeath.1 a)
  have hinv : AEStronglyMeasurable (fun t => (retention P a t)⁻¹) ν := by
    first | fun_prop | exact (measurable_retention P a).inv.aestronglyMeasurable
  have hinvBound : ∀ᵐ t ∂ν, ‖(retention P a t)⁻¹‖ ≤ c.Ghor⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
      (c.Ghor_pos.le.trans (hHorizon a t ht)))]
    exact positiveRetention_inv_retention_le c P hHorizon a ht
  have hw : AEStronglyMeasurable (deathTargetWeight c P a 0) ν := by
    first | fun_prop | exact (positiveRetention_measurable_deathTargetWeight c P
      hPoisson hDeath hDeathBounds a (by norm_num) (by norm_num)).aestronglyMeasurable
  have hwBound : ∀ᵐ t ∂ν, ‖deathTargetWeight c P a 0 t‖ ≤
      c.lambdaMax * Real.exp c.dMax := by
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using
      positiveRetention_deathTargetWeight_zero_abs_le c P hRecurBounds hDeathBounds a t
  have hrOn : IntegrableOn (fun t => (retention P a t)⁻¹ * P.lam a t)
      (Icc (0 : ℝ) 1) := hl.bdd_mul hinv hinvBound
  have heOn : IntegrableOn (fun t => (retention P a t)⁻¹ *
      (deathTargetWeight c P a 0 t * P.hazard a t)) (Icc (0 : ℝ) 1) :=
    (hd.bdd_mul hw hwBound).bdd_mul hinv hinvBound
  have hr := hrOn.integrable_indicator measurableSet_Icc
  have he := heOn.integrable_indicator measurableSet_Icc
  constructor
  · apply hr.congr
    filter_upwards [] with t
    by_cases ht : t ∈ Icc (0 : ℝ) 1 <;>
      simp [subcriticalRecurrenceDensity, Set.indicator, ht, div_eq_mul_inv, mul_comm]
  · apply he.congr
    filter_upwards [] with t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp only [subcriticalDeathDensity, Set.indicator_of_mem ht]
      rw [deathTargetWeight, if_pos (by simpa using ht)]
      ring
    · simp [subcriticalDeathDensity, Set.indicator, ht]

/-- The observable representative has measurable event sums and continuous
compensator primitives under the benchmark assumptions. -/
-- @node: positiveRetention_measurable_influenceRepresentative
@[fun_prop] lemma positiveRetention_measurable_influenceRepresentative (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Measurable (measurableSubcriticalInfluence c P a) := by
  have hi := positiveRetention_integrable_influenceDensities c P hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon a
  have hrPrim : Measurable (fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, subcriticalRecurrenceDensity P a t) :=
    (hi.1.continuous_primitive 0).measurable
  have hdPrim : Measurable (fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, subcriticalDeathDensity c P a t) :=
    (hi.2.continuous_primitive 0).measurable
  have hw := positiveRetention_measurable_deathTargetWeight c P hPoisson hDeath
    hDeathBounds a (h := 0) (by norm_num) (by norm_num)
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
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const)
    ((Measurable.ite
      (measurableSet_eq_fun measurable_obsHistory_deathInd measurable_const)
      ((hw.comp measurable_obsHistory_exit).mul
        ((measurable_retention P a).inv.comp measurable_obsHistory_exit))
      measurable_const).sub (hdPrim.comp measurable_obsHistory_exit))
    measurable_const).div_const _
  exact hr.sub hd

/-- The representative equals the paper influence whenever the exit lies
in the study horizon; this identity requires no model regularity. -/
-- @node: positiveRetention_influenceRepresentative_eq
lemma positiveRetention_influenceRepresentative_eq (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (o : ObsHistory) (ho : o.exit ∈ Icc (0 : ℝ) 1) :
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

/-- The paper influence and its benchmark representative agree almost surely. -/
-- @node: positiveRetention_influence_ae_eq_representative
lemma positiveRetention_influence_ae_eq_representative (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (a : Arm) :
    subcriticalInfluence c P a =ᵐ[observedLaw P]
      measurableSubcriticalInfluence c P a := by
  filter_upwards [observed_exit_mem_Icc_ae P hDeath] with o ho
  exact (positiveRetention_influenceRepresentative_eq c P a o ho).symm

/-- The actual individual influence is almost everywhere measurable under
positive horizon retention, without a Holder or endpoint-tail assumption. -/
-- @node: positiveRetention_aemeasurable_influence
@[fun_prop] lemma positiveRetention_aemeasurable_influence (c : ClassConstants) (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    AEMeasurable (subcriticalInfluence c P a) (observedLaw P) := by
  exact (positiveRetention_measurable_influenceRepresentative c P hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon a).aemeasurable.congr
      (positiveRetention_influence_ae_eq_representative c P hDeath a).symm

/-- The representative identity holds simultaneously for every iid sample
coordinate, so finite influence sums can use the measurable version. -/
-- @node: positiveRetention_sample_influence_ae_eq_representative
lemma positiveRetention_sample_influence_ae_eq_representative (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (a : Arm) (n : ℕ) :
    (fun s : Fin n → ObsHistory => fun i => subcriticalInfluence c P a (s i))
      =ᵐ[sampleLaw P n]
    fun s => fun i => measurableSubcriticalInfluence c P a (s i) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hall : ∀ᵐ s ∂sampleLaw P n, ∀ i,
      subcriticalInfluence c P a (s i) = measurableSubcriticalInfluence c P a (s i) := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval
      (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving.ae_eq
      (positiveRetention_influence_ae_eq_representative c P hDeath a)
  filter_upwards [hall] with s hs
  funext i
  exact hs i

/-- The finite iid influence sum agrees almost surely with its measurable
representative under the benchmark death model. -/
-- @node: positiveRetention_sum_influence_ae_eq_representative
lemma positiveRetention_sum_influence_ae_eq_representative (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (a : Arm) (n : ℕ) :
    (fun s : Fin n → ObsHistory => ∑ i, subcriticalInfluence c P a (s i))
      =ᵐ[sampleLaw P n]
    fun s => ∑ i, measurableSubcriticalInfluence c P a (s i) := by
  filter_upwards [positiveRetention_sample_influence_ae_eq_representative c P hDeath a n]
    with s hs
  exact Finset.sum_congr rfl (fun i _ => congrFun hs i)

/-- The actual influence contrast used by the benchmark CLT is almost
everywhere measurable under the observed subject law. -/
-- @node: positiveRetention_aemeasurable_influenceContrast
@[fun_prop] lemma positiveRetention_aemeasurable_influenceContrast (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) :
    AEMeasurable (fun o => subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) (observedLaw P) := by
  have h1 := positiveRetention_aemeasurable_influence c P hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon true
  have h0 := positiveRetention_aemeasurable_influence c P hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon false
  fun_prop

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
