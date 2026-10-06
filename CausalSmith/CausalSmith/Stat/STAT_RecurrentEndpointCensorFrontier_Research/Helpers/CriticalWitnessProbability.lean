module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceWitness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PrimitiveCountCompaction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureProductLaw
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.StoppedKL

/-!
# Subject-level early recurrence probabilities

Roadmap (31) factors an early recurrence from assigned-arm observation through
its cutoff. The canonical stopped Poisson law supplies the exact empty-count
probability, including a zero intensity measure.
-/

public section

open MeasureTheory Set ProbabilityTheory Filter
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The number of events retained at a deterministic cutoff has the Poisson
law with mean equal to the intensity mass before that cutoff. -/
-- @node: canonicalRecurrenceLawOf_map_stopped_count
lemma canonicalRecurrenceLawOf_map_stopped_count (ν : Measure ℝ)
    [IsFiniteMeasure ν] (τ : ℝ) :
    (canonicalRecurrenceLawOf ν).map (fun s => (s.stopAt τ).1) =
      poissonMeasure (finiteMeasureMass (ν.restrict (Iic τ))) := by
  rw [show (fun s : RecurConfig => (s.stopAt τ).1) =
      FiniteSample.count ∘ RecurConfig.stopAt τ from rfl,
    ← Measure.map_map (measurable_finiteSample_count) (by fun_prop),
    canonicalRecurrenceLawOf_map_stopAt_restrict τ ν (Measure.dirac 0),
    finiteMeasureMarkedPoissonLaw_map_count]
  simp

/-- The exact probability of no recurrence before a fixed cutoff is the
exponential of minus the corresponding intensity mass. -/
-- @node: canonicalRecurrenceLawOf_stopped_count_zero_probability
lemma canonicalRecurrenceLawOf_stopped_count_zero_probability (ν : Measure ℝ)
    [IsFiniteMeasure ν] (τ : ℝ) :
    (canonicalRecurrenceLawOf ν).real {s | (s.stopAt τ).1 = 0} =
      Real.exp (-(ν.real (Iic τ))) := by
  have hm : Measurable (fun s : RecurConfig => (s.stopAt τ).1) := by
    exact measurable_finiteSample_count.comp (by fun_prop)
  have h := canonicalRecurrenceLawOf_map_stopped_count ν τ
  have he := congrArg (fun μ : Measure ℕ => μ.real {0}) h
  rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton 0)] at he
  change (canonicalRecurrenceLawOf ν).real {s | (s.stopAt τ).1 = 0} = _ at he
  rw [poissonMeasure_real_singleton] at he
  simpa [finiteMeasureMass, Measure.real, Measure.restrict_apply MeasurableSet.univ, ENNReal.toReal] using he

/-- Under the paper's recurrence model, the latent probability of at least
one recurrence before the cutoff is one minus the empty Poisson probability. -/
-- @node: latent_early_recurrence_probability
lemma latent_early_recurrence_probability (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (a : Arm) (τ : ℝ) :
    P.latent.real {z | 0 < ((z.recur a).stopAt τ).1} =
      1 - Real.exp (-(recurrenceIntensity P a).real (Iic τ)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  obtain ⟨hν, hmap⟩ := (hPoisson a).2.2
  letI := hν
  have hm : MeasurableSet {s : RecurConfig | (s.stopAt τ).1 = 0} := by
    apply measurableSet_eq_fun _ measurable_const
    exact measurable_finiteSample_count.comp (by fun_prop)
  have hz : P.latent.real {z | ((z.recur a).stopAt τ).1 = 0} =
      Real.exp (-(recurrenceIntensity P a).real (Iic τ)) := by
    have he := canonicalRecurrenceLawOf_stopped_count_zero_probability
      (recurrenceIntensity P a) τ
    rw [← show P.latent.map (fun z : LatentSubject => z.recur a) =
      canonicalRecurrenceLawOf (recurrenceIntensity P a) from hmap] at he
    rw [measureReal_def, Measure.map_apply (by fun_prop) hm] at he
    exact he
  have hc : {z : LatentSubject | 0 < ((z.recur a).stopAt τ).1} =
      {z | ((z.recur a).stopAt τ).1 = 0}ᶜ := by
    ext z
    exact Nat.pos_iff_ne_zero
  have hmz : MeasurableSet {z : LatentSubject | ((z.recur a).stopAt τ).1 = 0} :=
    hm.preimage (measurable_latentSubject_recur a)
  rw [hc, probReal_compl_eq_one_sub hmz, hz]

/-- Assignment and observation through the cutoff factor from recurrence,
so the subject witness in roadmap (31) has an exact product probability. -/
-- @node: latent_assigned_early_recurrence_probability
lemma latent_assigned_early_recurrence_probability (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    P.latent.real {z | z.treatment = a ∧
      τ ≤ min (z.death a) (censorHorizon z a) ∧
      0 < ((z.recur a).stopAt τ).1} =
      (P.p a * survival P a τ * retention P a τ) *
        (1 - Real.exp (-(recurrenceIntensity P a).real (Iic τ))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E : Set (Arm × (ℝ × ENNReal)) :=
    {e | e.1 = a ∧ τ ≤ min e.2.1 (censorHorizonValue e.2.2)}
  let B : Set RecurConfig := {s | 0 < (s.stopAt τ).1}
  have hE : MeasurableSet E := by
    exact (measurableSet_eq_fun (measurable_fst : Measurable (fun e : Arm × (ℝ × ENNReal) => e.1)) measurable_const).inter
      (measurableSet_le measurable_const
        (show Measurable (fun e : Arm × (ℝ × ENNReal) =>
          min e.2.1 (censorHorizonValue e.2.2)) by fun_prop))
  have hB : MeasurableSet B := by
    exact (measurable_finiteSample_count.comp
      (show Measurable (fun s : RecurConfig => s.stopAt τ) by fun_prop)) measurableSet_Ioi
  have hi := arm_exposure_indep_recurrence P hP.randomAssignment
    hP.recurrenceDeathIndependence hP.independentCensoring a
  have hf := hi.measure_inter_preimage_eq_mul E B hE hB
  have heq : {z : LatentSubject | z.treatment = a ∧
      τ ≤ min (z.death a) (censorHorizon z a) ∧
      0 < ((z.recur a).stopAt τ).1} =
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))) ⁻¹' E ∩
      (fun z : LatentSubject => z.recur a) ⁻¹' B := by
    ext z
    simp [E, B, censorHorizon_eq_value, and_assoc]
  rw [heq, measureReal_def, hf, ENNReal.toReal_mul]
  have hrisk : P.latent.real
      ((fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))) ⁻¹' E) =
      P.p a * survival P a τ * retention P a τ := by
    have hm : MeasurableSet {o : ObsHistory | o.treatment = a ∧ τ ≤ o.exit} := by
      exact (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
        (measurableSet_le measurable_const measurable_obsHistory_exit)
    have hp := observed_arm_risk_probability P hP a hτ
    rw [observedLaw, measureReal_def, Measure.map_apply measurable_observe hm] at hp
    have hs :
        ((fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))) ⁻¹' E) =
        observe ⁻¹' {o : ObsHistory | o.treatment = a ∧ τ ≤ o.exit} := by
      ext z
      by_cases ha : z.treatment = a <;> simp [E, observe, ha, censorHorizon_eq_value]
    rw [hs, measureReal_def]
    exact hp
  change P.latent.real _ * P.latent.real {z | 0 < ((z.recur a).stopAt τ).1} = _
  rw [hrisk, latent_early_recurrence_probability P hP.poissonRecurrence a τ]

/-- The recurrence lower envelope bounds the mean count through an early
cutoff; finiteness justifies passing the intensity inequality to real mass. -/
-- @node: recurrenceIntensity_early_mass_lower
lemma recurrenceIntensity_early_mass_lower (c : ClassConstants) (P : SubjectLaw)
    (hRecur : RecurrenceBounds c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    c.lambdaMin * τ ≤ (recurrenceIntensity P a).real (Iic τ) := by
  have hd : (volume.restrict (Ioc (0 : ℝ) 1)).withDensity
      (fun _ => ENNReal.ofReal c.lambdaMin) ≤ recurrenceIntensity P a := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ENNReal.ofReal_le_ofReal (hRecur a t ⟨ht.1.le, ht.2⟩).1
  have hmass := hd (Iic τ)
  rw [withDensity_const, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic] at hmass
  have hs : Iic τ ∩ Ioc (0 : ℝ) 1 = Ioc 0 τ := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, h2.trans hτ.2⟩
  rw [hs, Real.volume_Ioc] at hmass
  have hr := ENNReal.toReal_mono (measure_ne_top (recurrenceIntensity P a) (Iic τ)) hmass
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal c.lambdaMin_pos.le,
    ENNReal.toReal_ofReal hτ.1, Measure.real] using hr

/-- The genuine uniform positive lower probability for the latent witness
in roadmap (31), derived from randomization, recurrence and retention. -/
-- @node: latent_assigned_early_recurrence_probability_lower
lemma latent_assigned_early_recurrence_probability_lower (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 - c.x0) :
    (c.pMin * Real.exp (-c.dMax) * c.Gint) *
      (1 - Real.exp (-(c.lambdaMin * τ))) ≤
    P.latent.real {z | z.treatment = a ∧
      τ ≤ min (z.death a) (censorHorizon z a) ∧
      0 < ((z.recur a).stopAt τ).1} := by
  have hτ : τ ∈ Icc (0 : ℝ) 1 :=
    ⟨hτ0.le, hτ1.trans (by linarith [c.x0_pos])⟩
  rw [latent_assigned_early_recurrence_probability c P hP a hτ]
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI := hν
  have hmass := recurrenceIntensity_early_mass_lower c P hP.recurrenceBounds a hτ
  have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a hτ).1
  have hg := hP.interiorRetention a τ ⟨hτ0.le, hτ1⟩
  have hp := hP.treatmentOverlap a
  have he : 0 ≤ 1 - Real.exp (-(c.lambdaMin * τ)) := by
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg c.lambdaMin_pos.le hτ0.le)
  have hdiff : 1 - Real.exp (-(c.lambdaMin * τ)) ≤
      1 - Real.exp (-(recurrenceIntensity P a).real (Iic τ)) := by
    exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hmass)) 1
  have hprod : c.pMin * Real.exp (-c.dMax) * c.Gint ≤
      P.p a * survival P a τ * retention P a τ := by
    exact mul_le_mul (mul_le_mul hp hs (Real.exp_pos _).le
      (c.pMin_pos.le.trans hp)) hg c.Gint_pos.le
      (mul_nonneg (c.pMin_pos.le.trans hp) ((Real.exp_pos _).le.trans hs))
  exact mul_le_mul hprod hdiff he
    (mul_nonneg (mul_nonneg (c.pMin_pos.le.trans hp)
      ((Real.exp_pos _).le.trans hs)) (c.Gint_pos.le.trans hg))

/-- Stopping retains precisely the events counted below its cutoff. -/
-- @node: stopped_count_eq_countLE
lemma stopped_count_eq_countLE (s : RecurConfig) (τ : ℝ) :
    (s.stopAt τ).1 = s.countLE τ := by
  classical
  rw [RecurConfig.stopAt_eq_restrictAt]
  simp [RecurConfig.restrictAt, RecurConfig.countLE, RecurConfig.paddedCountLE,
    finiteSamplePaddedStream, FiniteMeasurablePartition.restrictCell,
    FiniteMeasurablePartition.cellIndices, timeCutPartition, FiniteSample.points,
    FiniteSample.count]
  rfl

/-- A positive early count has an actual represented recurrence time. -/
-- @node: countLE_pos_iff_recurrence_witness
lemma countLE_pos_iff_recurrence_witness (s : RecurConfig) (τ : ℝ) :
    0 < s.countLE τ ↔ ∃ k : Fin s.1, (s.2 k).1 ≤ τ := by
  classical
  simp [RecurConfig.countLE, RecurConfig.paddedCountLE, finiteSamplePaddedStream,
    FiniteSample.points, FiniteSample.count, Finset.card_pos]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩

/-- Observation through a cutoff preserves the latent count at that cutoff. -/
-- @node: observe_countLE_eq_of_still_observed
lemma observe_countLE_eq_of_still_observed (z : LatentSubject) (a : Arm)
    (ha : z.treatment = a) {τ : ℝ}
    (hτ : τ ≤ min (z.death a) (censorHorizon z a)) :
    (observe z).recur.countLE τ = ((z.recur a).stopAt τ).1 := by
  change ((z.recur z.treatment).stopAt
    (min (z.death z.treatment) (censorHorizon z z.treatment))).countLE τ = _
  rw [ha, stopped_count_eq_countLE, countLE_stopAt_eq_sum]
  simp only [RecurConfig.countLE, RecurConfig.paddedCountLE, finiteSamplePaddedStream,
    FiniteSample.points, FiniteSample.count]
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : ((z.recur a).2 k).1 ≤ τ
  · simp [ht, ht.trans hτ]
  · simp [ht]

/-- The observable early recurrence witness has the same exact probability
as the latent witness, with no added measurability assumption. -/
-- @node: observed_early_recurrence_probability
lemma observed_early_recurrence_probability (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    (observedLaw P).real {o | o.treatment = a ∧ τ ≤ o.exit ∧
      0 < o.recur.countLE τ} =
      (P.p a * survival P a τ * retention P a τ) *
        (1 - Real.exp (-(recurrenceIntensity P a).real (Iic τ))) := by
  have hm : MeasurableSet {o : ObsHistory | o.treatment = a ∧ τ ≤ o.exit ∧
      0 < o.recur.countLE τ} := by
    apply (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
    apply (measurableSet_le measurable_const measurable_obsHistory_exit).inter
    exact (RecurConfig.measurable_countLE.comp
      (measurable_const.prodMk measurable_obsHistory_recur))
      measurableSet_Ioi
  have hs : observe ⁻¹' {o : ObsHistory | o.treatment = a ∧ τ ≤ o.exit ∧
      0 < o.recur.countLE τ} =
      {z | z.treatment = a ∧ τ ≤ min (z.death a) (censorHorizon z a) ∧
        0 < ((z.recur a).stopAt τ).1} := by
    ext z
    change (z.treatment = a ∧ τ ≤ (observe z).exit ∧
      0 < (observe z).recur.countLE τ) ↔
      (z.treatment = a ∧ τ ≤ min (z.death a) (censorHorizon z a) ∧
        0 < ((z.recur a).stopAt τ).1)
    by_cases ha : z.treatment = a
    · have he : (observe z).exit = min (z.death a) (censorHorizon z a) := by
        simp [observe, ha]
      rw [he]
      by_cases ht : τ ≤ min (z.death a) (censorHorizon z a)
      · rw [observe_countLE_eq_of_still_observed z a ha ht]
      · simp only [ht, false_and, and_false]
    · simp [ha]
  rw [observedLaw, measureReal_def, Measure.map_apply measurable_observe hm, hs]
  exact latent_assigned_early_recurrence_probability c P hP a hτ

/-- Roadmap (31) for the actual observable witness event. -/
-- @node: observed_early_recurrence_probability_lower
lemma observed_early_recurrence_probability_lower (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 - c.x0) :
    (c.pMin * Real.exp (-c.dMax) * c.Gint) *
      (1 - Real.exp (-(c.lambdaMin * τ))) ≤
    (observedLaw P).real {o | o.treatment = a ∧ τ ≤ o.exit ∧
      0 < o.recur.countLE τ} := by
  have hτ : τ ∈ Icc (0 : ℝ) 1 :=
    ⟨hτ0.le, hτ1.trans (by linarith [c.x0_pos])⟩
  rw [observed_early_recurrence_probability c P hP a hτ,
    ← latent_assigned_early_recurrence_probability c P hP a hτ]
  exact latent_assigned_early_recurrence_probability_lower c P hP a hτ0 hτ1

/-- Early observable witnesses in the two arms give a uniform geometric
fallback bound once the continuation band lies beyond their fixed cutoff. -/
-- @node: nonFallback_compl_probability_le_early_geometric
lemma nonFallback_compl_probability_le_early_geometric (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 - c.x0) {n : ℕ} (hn : 0 < n)
    (hband : τ < 1 - 2 * bandwidth c n) :
    (sampleLaw P n).real {s | ¬ nonFallback c s} ≤
      2 * (1 - (c.pMin * Real.exp (-c.dMax) * c.Gint) *
        (1 - Real.exp (-(c.lambdaMin * τ)))) ^ n := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let B : Arm → Set ObsHistory := fun a =>
    {o | o.treatment = a ∧ τ ≤ o.exit ∧ 0 < o.recur.countLE τ}
  have hm (a : Arm) : MeasurableSet (B a) := by
    exact (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      ((measurableSet_le measurable_const measurable_obsHistory_exit).inter
        ((RecurConfig.measurable_countLE.comp
          (measurable_const.prodMk measurable_obsHistory_recur)) measurableSet_Ioi))
  have hw : ∀ a o, o ∈ B a → o.treatment = a ∧
      ∃ k : Fin o.recur.1, (o.recur.2 k).1 ≤ o.exit ∧
        (o.recur.2 k).1 < 1 - 2 * bandwidth c n := by
    intro a o ho
    obtain ⟨k, hk⟩ := (countLE_pos_iff_recurrence_witness o.recur τ).mp ho.2.2
    exact ⟨ho.1, k, hk.trans ho.2.1, hk.trans_lt hband⟩
  have hb := nonFallback_compl_probability_le_no_early_witness c P hn B hm hw
  have hpow (a : Arm) : (1 - (observedLaw P).real (B a)) ^ n ≤
      (1 - (c.pMin * Real.exp (-c.dMax) * c.Gint) *
        (1 - Real.exp (-(c.lambdaMin * τ)))) ^ n := by
    apply pow_le_pow_left₀
    · exact sub_nonneg.mpr ((measureReal_mono (Set.subset_univ (B a))).trans
        (by simp))
    · exact sub_le_sub_left
        (observed_early_recurrence_probability_lower c P hP a hτ0 hτ1) 1
  calc
    _ ≤ (1 - (observedLaw P).real (B false)) ^ n +
      (1 - (observedLaw P).real (B true)) ^ n := hb
    _ ≤ _ := by simpa [two_mul] using add_le_add (hpow false) (hpow true)

/-- A fixed cutoff of one quarter lies before the continuation band for every
positive sample size, so the geometric fallback bound needs no asymptotic cap. -/
-- @node: nonFallback_compl_uniform_geometric_bound
lemma nonFallback_compl_uniform_geometric_bound (c : ClassConstants) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ n : ℕ, 0 < n →
      ∀ P : SubjectLaw, ModelClass c P →
        (sampleLaw P n).real {s | ¬ nonFallback c s} ≤ 2 * (1 - δ) ^ n := by
  let δ := (c.pMin * Real.exp (-c.dMax) * c.Gint) *
    (1 - Real.exp (-(c.lambdaMin * (1 / 4))))
  have hdpos : 0 < c.dMax := c.dMin_pos.trans c.dMin_lt
  have he : 0 < 1 - Real.exp (-(c.lambdaMin * (1 / 4))) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith [c.lambdaMin_pos]
  have hp0 := c.pMin_pos
  have hg0 := c.Gint_pos
  have hg1 := c.Gint_le
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ ≤ 1 / 2 := by
    have hexp : Real.exp (-c.dMax) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hdpos.le
    have hdiff : 1 - Real.exp (-(c.lambdaMin * (1 / 4))) ≤ 1 := by
      linarith [Real.exp_pos (-(c.lambdaMin * (1 / 4)))]
    calc
      δ ≤ (c.pMin * 1 * 1) * 1 := by
        dsimp [δ]
        gcongr <;> first | assumption | positivity
      _ ≤ 1 / 2 := by simpa using c.pMin_le
  refine ⟨δ, hδ, by linarith, ?_⟩
  intro n hn P hP
  apply nonFallback_compl_probability_le_early_geometric c P hP (by norm_num)
    (by linarith [c.x0_le]) hn
  have hh := (bandwidth_pos_and_le_cap c hn).2
  linarith [c.x0_le]

/-- Roadmap (32): a positive fixed subject probability makes the actual
fallback probability exponentially small, uniformly over the full model. -/
-- @node: nonFallback_compl_uniform_exponential_bound
lemma nonFallback_compl_uniform_exponential_bound (c : ClassConstants) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 0 < n →
      ∀ P : SubjectLaw, ModelClass c P →
        (sampleLaw P n).real {s | ¬ nonFallback c s} ≤
          2 * Real.exp (-δ * n) := by
  obtain ⟨δ, hδ, hδ1, hb⟩ := nonFallback_compl_uniform_geometric_bound c
  refine ⟨δ, hδ, ?_⟩
  intro n hn P hP
  calc
    _ ≤ 2 * (1 - δ) ^ n := hb n hn P hP
    _ ≤ 2 * (Real.exp (-δ)) ^ n := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg δ) n) (by norm_num)
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- The exponential fallback bound gives the finite-sample probability rate
needed by the expected critical interval length assembly. -/
-- @node: nonFallback_compl_uniform_log_rate_bound
lemma nonFallback_compl_uniform_log_rate_bound (c : ClassConstants) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ P : SubjectLaw, ModelClass c P →
        (sampleLaw P n).real {s | ¬ nonFallback c s} ≤
          C * Real.sqrt (Real.log n / n) := by
  obtain ⟨δ, hδ, hb⟩ := nonFallback_compl_uniform_exponential_bound c
  refine ⟨2 / δ, by positivity, ?_⟩
  intro n hn P hP
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : Real.exp (-δ * n) ≤ (δ * n)⁻¹ := by
    rw [show -δ * (n : ℝ) = -(δ * n) by ring, Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos _) (mul_pos hδ hnR)).mpr
    linarith [Real.add_one_le_exp (δ * n)]
  have hsqrt : (n : ℝ)⁻¹ ≤ Real.sqrt (Real.log n / n) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    have hl := one_le_log_sampleSize hn
    have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnR).mpr hn1
    have hi0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
    calc
      ((n : ℝ)⁻¹) ^ 2 ≤ (n : ℝ)⁻¹ := by nlinarith
      _ ≤ Real.log n / n := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hl hi0
  calc
    _ ≤ 2 * Real.exp (-δ * n) := hb n hn0 P hP
    _ ≤ 2 * (δ * n)⁻¹ := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = (2 / δ) * (n : ℝ)⁻¹ := by rw [mul_inv_rev, div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Geometric witness control makes fallback vanish along arbitrary triangular
model sequences, independently of optional-variation consistency. -/
-- @node: nonFallback_compl_triangular_tendsto_of_early_witness
lemma nonFallback_compl_triangular_tendsto_of_early_witness
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s | ¬ nonFallback c s})
      atTop (nhds 0) := by
  obtain ⟨δ, hδ, hδ1, hb⟩ := nonFallback_compl_uniform_geometric_bound c
  have hp : Tendsto (fun n : ℕ => 2 * (1 - δ) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ 1 - δ by linarith) (show 1 - δ < 1 by linarith)).const_mul (2 : ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hp
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hb n (by omega) (Pseq n) (hP n)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
