module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceAssembly
public import Causalean.Stat.CLT.Lindeberg

/-!
# Actual benchmark influence moments

Roadmap (25)--(30): exposure orthogonality and the full-horizon isometries
give exact arm and contrast moments for the actual paper influence. A
finite-second-moment Lindeberg argument then proves its iid Gaussian limit.
Oracle replacement for the ordinary estimator remains a separate obligation.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The full-horizon canonical death oracle is orthogonal to the recurrence
oracle on the actual observed sample. All quadratic moment conditions are
supplied by subcritical overlap and the proved death oracle isometry. -/
-- @node: positiveRetention_recurrence_deathOracle_orthogonal
lemma positiveRetention_recurrence_deathOracle_orthogonal
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    let J := fun s : Fin n → ObsHistory =>
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s)
    Integrable (fun s => J s * observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s) (sampleLaw P n) ∧
    (∫ s, J s * observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s ∂sampleLaw P n) = 0 := by
  let D := aggregateIntegral (referenceDeathHazard P a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
  let F := fun s : Fin n → ObsHistory => D (observedDeathSample a s)
  let g := fun e : Fin n → Arm × (ℝ × ENNReal) =>
    F (fun i => recurrenceExposureHistory (e i))
  have hDeq : D = aggregateIntegral
      (DeathCP.positiveRetention_referenceHazard P hDeath a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 := by
    funext x
    exact (DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a _ x).symm
  have hD : Measurable D := by
    rw [hDeq]
    exact measurable_deathAggregateIntegral_deterministic _ _
      (DeathCP.positiveRetention_referenceHazard_measurable P hDeath a)
      (positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath hDeathBounds a) 1
  have hF : Measurable F := hD.comp (measurable_pi_lambda _ (fun i =>
    (measurable_observedDeathPair a).comp (measurable_pi_apply i)))
  have hg : Measurable g := hF.comp (measurable_pi_lambda _ (fun i =>
    measurable_recurrenceExposureHistory.comp (measurable_pi_apply i)))
  have hfactor : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      F (fun i => observe (z i)) =
        g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply congrArg D
    funext i
    exact observedDeathPair_eq_exposureHistory a (z i)
  have hg2 := integrable_sq_exposure_coefficient_of_observed P a n g hg F hF
    (positiveRetention_observedDeathOracle_full_moments c P hRandom hAssignment hOverlap hPoisson hDeath hCensor hRecurBounds hDeathBounds hHorizon a n).2.2.1 hfactor
  exact positiveRetention_recurrenceOracle_orthogonal_of_exposure
    c P hRandom hRD hCensor hPoisson hHorizon a n g hg hg2 F hF hfactor

/-- The assembled full-horizon arm oracle is centered and has exactly the
sum of the recurrence and death variance contributions. Orthogonality, rather
than independence, removes its cross term. -/
-- @node: positiveRetention_armOracle_full_moments
lemma positiveRetention_armOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    let R := observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
    let D := fun s : Fin n → ObsHistory =>
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s)
    Integrable (fun s => R s / P.p a - D s) (sampleLaw P n) ∧
    (∫ s, R s / P.p a - D s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => (R s / P.p a - D s) ^ 2) (sampleLaw P n) ∧
    (∫ s, (R s / P.p a - D s) ^ 2 ∂sampleLaw P n) =
      ((n : ℝ) / P.p a) *
        ((∫ t in (0 : ℝ)..1, survival P a t * P.lam a t / retention P a t) +
          ∫ t in (0 : ℝ)..1, remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)) := by
  let R := observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
  let D := fun s : Fin n → ObsHistory =>
    aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
        (observedDeathSample a s)
  have hr := positiveRetention_recurrenceOracle_full_moments c P hRandom hRD hCensor hPoisson hHorizon a n
  have hd := positiveRetention_observedDeathOracle_full_moments c P hRandom hAssignment hOverlap hPoisson hDeath hCensor hRecurBounds hDeathBounds hHorizon a n
  have hx := positiveRetention_recurrence_deathOracle_orthogonal c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a hn
  have hR : MemLp R 2 (sampleLaw P n) :=
    (memLp_two_iff_integrable_sq hr.1.aestronglyMeasurable).2 hr.2.2.1
  have hD : MemLp D 2 (sampleLaw P n) :=
    (memLp_two_iff_integrable_sq hd.1.aestronglyMeasurable).2 hd.2.2.1
  have hi := (hr.1.div_const (P.p a)).sub hd.1
  refine ⟨hi, ?_, ?_, ?_⟩
  · rw [integral_sub (hr.1.div_const _) hd.1, integral_div, hr.2.1, hd.2.1]
    simp
  · exact (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).1
      (by
        simpa only [div_eq_mul_inv, mul_comm] using
          (hR.const_mul (P.p a)⁻¹).sub hD)
  · calc
      _ = ∫ s, R s ^ 2 / P.p a ^ 2 + D s ^ 2 -
          (2 / P.p a) * (D s * R s) ∂sampleLaw P n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by ring)
      _ = (∫ s, R s ^ 2 ∂sampleLaw P n) / P.p a ^ 2 +
          (∫ s, D s ^ 2 ∂sampleLaw P n) := by
        rw [integral_sub (f := fun s => R s ^ 2 / P.p a ^ 2 + D s ^ 2)
          (g := fun s => (2 / P.p a) * (D s * R s))
          ((hr.2.2.1.div_const _).add hd.2.2.1) (hx.1.const_mul _),
          integral_add (f := fun s => R s ^ 2 / P.p a ^ 2)
            (g := fun s => D s ^ 2) (hr.2.2.1.div_const _) hd.2.2.1,
          integral_div, integral_const_mul, hx.2]
        ring
      _ = _ := by
        rw [positiveRetention_recurrenceOracle_full_secondMoment c P hRandom hAssignment hDeath hRD hCensor hPoisson hHorizon a hn,
          hd.2.2.2]
        have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hOverlap a)).ne'
        field_simp
        <;> ring



/-- The finite full-horizon arm oracle is exactly the sum of the paper's
influences on observed latent paths. -/
-- @node: positiveRetention_armOracle_eq_influence_sum
lemma positiveRetention_armOracle_eq_influence_sum
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (z : Fin n → LatentSubject)
    (ho : ∀ i, (observe (z i)).exit ∈ Icc (0 : ℝ) 1) :
    observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
        (fun i => observe (z i)) / P.p a -
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
        (observedDeathSample a (fun i => observe (z i))) =
      ∑ i, subcriticalInfluence c P a (observe (z i)) := by
  classical
  unfold observedRecurrenceScore aggregateIntegral
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [subcriticalDeathOracle_subject_eq c P a _ i (ho i),
    observedRecurrence_compensator_eq_interval P hPoisson a _ (ho i),
    observedRecurrence_full_point_sum]
  unfold subcriticalInfluence
  by_cases ha : (observe (z i)).treatment = a <;> simp [ha]

/-- The oracle-to-influence identity holds almost surely under the actual iid law. -/
-- @node: positiveRetention_armOracle_ae_eq_influence_sum
lemma positiveRetention_armOracle_ae_eq_influence_sum
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ) :
    (fun s : Fin n → ObsHistory =>
      observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s / P.p a -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      fun s => ∑ i, subcriticalInfluence c P a (s i) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsFiniteMeasure (recurrenceIntensity P a) :=
    (hPoisson a).2.2.1
  let F := fun s : Fin n → ObsHistory =>
    observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s / P.p a -
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
        (observedDeathSample a s)
  let G := fun s : Fin n → ObsHistory => ∑ i, measurableSubcriticalInfluence c P a (s i)
  have hF : Measurable F := by
    apply Measurable.sub
    · exact (measurable_observedRecurrenceScore P a n 1 _
        (measurable_retention P a).inv).div_const _
    · have heq : aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 =
          aggregateIntegral (DeathCP.positiveRetention_referenceHazard P hDeath a)
            (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 := by
        funext x
        exact (DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a _ x).symm
      rw [heq]
      exact (measurable_deathAggregateIntegral_deterministic _ _
        (DeathCP.positiveRetention_referenceHazard_measurable P hDeath a)
        (positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath hDeathBounds a) 1).comp
          (measurable_pi_lambda _ (fun i =>
            (measurable_observedDeathPair a).comp (measurable_pi_apply i)))
  have hG : Measurable G := by
    apply Finset.measurable_sum
    intro i _
    exact (positiveRetention_measurable_influenceRepresentative c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a).comp
      (measurable_pi_apply i)
  have hFG : F =ᵐ[sampleLaw P n] G := by
    rw [recurrence_sampleLaw_eq_latent_map]
    apply (ae_map_iff (show Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) by fun_prop).aemeasurable
      (measurableSet_eq_fun hF hG)).2
    have he : ∀ᵐ z ∂P.latent, (observe z).exit ∈ Icc (0 : ℝ) 1 := by
      exact (ae_map_iff measurable_observe.aemeasurable
        (measurableSet_Icc.preimage measurable_obsHistory_exit)).1
          (observed_exit_mem_Icc_ae P hDeath)
    have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
        ∀ i, (observe (z i)).exit ∈ Icc (0 : ℝ) 1 := by
      rw [Filter.eventually_all]
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => P.latent) i).quasiMeasurePreserving.ae he
    filter_upwards [hall] with z hz
    change F (fun i => observe (z i)) = G (fun i => observe (z i))
    dsimp [F, G]
    rw [positiveRetention_armOracle_eq_influence_sum c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a z hz]
    apply Finset.sum_congr rfl
    intro i _
    exact (positiveRetention_influenceRepresentative_eq c P a _ (hz i)).symm
  exact hFG.trans (positiveRetention_sum_influence_ae_eq_representative c P hDeath a n).symm


/-- Both oracle variance terms have finite horizon integrals under the benchmark
assumptions, including merely measurable recurrence and death hazards. -/
-- @node: positiveRetention_variance_terms_intervalIntegrable
lemma positiveRetention_variance_terms_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    IntervalIntegrable (fun t =>
      survival P a t * P.lam a t / retention P a t) volume 0 1 ∧
    IntervalIntegrable (fun t => (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t)) volume 0 1 := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  have htarget : Integrable (fun t => survival P a t * P.lam a t) ν := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa [continuationWeight] using weightedTarget_intervalIntegrable c P hPoisson
      hDeath hDeathBounds a (h := 0) (by norm_num) (by norm_num) (by norm_num)
  have hinv : AEStronglyMeasurable (fun t => (retention P a t)⁻¹) ν := by
    exact (measurable_retention P a).inv.aestronglyMeasurable
  have hinvBound : ∀ᵐ t ∂ν, ‖(retention P a t)⁻¹‖ ≤ c.Ghor⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (c.Ghor_pos.le.trans (hHorizon a t ht)))]
    exact positiveRetention_inv_retention_le c P hHorizon a ht
  have hrec := htarget.bdd_mul hinv hinvBound
  have henergy : Integrable (fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t) ν :=
    positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn c P hPoisson
      hDeath hRecurBounds hDeathBounds a
  have hs : AEStronglyMeasurable (survival P a) ν :=
    (positiveRetention_survival_continuousOn P hDeath a).aestronglyMeasurable measurableSet_Icc
  have hsBound : ∀ᵐ t ∂ν, ‖survival P a t‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa [Real.norm_eq_abs, abs_of_pos (show 0 < survival P a t from Real.exp_pos _)]
      using (survival_bounds_of_deathBounds c P hDeathBounds a ht).2
  have hd := (henergy.bdd_mul hs hsBound).bdd_mul hinv hinvBound
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hrec.congr (Filter.Eventually.of_forall (fun t => by
      dsimp only
      ring))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply hd.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hs0 : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  have hg0 : retention P a t ≠ 0 := (c.Ghor_pos.trans_le (hHorizon a t ht)).ne'
  rw [deathTargetWeight, if_pos (by simpa using ht)]
  field_simp


/-- The actual armwise influence sum is centered and square integrable,
with exactly n times its paper variance contribution. -/
-- @node: positiveRetention_subcriticalInfluence_sum_moments
lemma positiveRetention_subcriticalInfluence_sum_moments
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    let Z := fun s : Fin n → ObsHistory => ∑ i, subcriticalInfluence c P a (s i)
    Integrable Z (sampleLaw P n) ∧
    (∫ s, Z s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => Z s ^ 2) (sampleLaw P n) ∧
    (∫ s, Z s ^ 2 ∂sampleLaw P n) =
      ((n : ℝ) / P.p a) * ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t) := by
  have hm := positiveRetention_armOracle_full_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a hn
  have he := positiveRetention_armOracle_ae_eq_influence_sum c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a n
  have he2 := he.fun_comp (fun x : ℝ => x ^ 2)
  dsimp only [Function.comp_def] at he2
  dsimp only
  refine ⟨hm.1.congr he, (integral_congr_ae he.symm).trans hm.2.1,
    hm.2.2.1.congr he2, ?_⟩
  rw [integral_congr_ae he2.symm, hm.2.2.2,
    intervalIntegral.integral_add
      (positiveRetention_variance_terms_intervalIntegrable c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a).1
      (positiveRetention_variance_terms_intervalIntegrable c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a).2]

/-- Each one-subject influence is centered and has its exact full-horizon
variance, derived from the oracle moments at sample size one. -/
-- @node: positiveRetention_subcriticalInfluence_arm_moments
lemma positiveRetention_subcriticalInfluence_arm_moments
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Integrable (subcriticalInfluence c P a) (observedLaw P) ∧
    (∫ o, subcriticalInfluence c P a o ∂observedLaw P) = 0 ∧
    Integrable (fun o => subcriticalInfluence c P a o ^ 2) (observedLaw P) ∧
    (∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P) =
      (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hm := positiveRetention_subcriticalInfluence_sum_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a (n := 1) (by norm_num)
  simp only [Fin.sum_univ_one, Nat.cast_one, one_div] at hm
  have hz := (positiveRetention_aemeasurable_influence c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a).aestronglyMeasurable
  have hz2 := hz.pow 2
  have hp := measurePreserving_eval (fun _ : Fin 1 => observedLaw P) 0
  refine ⟨(hp.integrable_comp hz).1 hm.1, ?_,
    (hp.integrable_comp hz2).1 hm.2.2.1, ?_⟩
  · exact (integral_comp_eval (μ := fun _ : Fin 1 => observedLaw P)
      (i := 0) hz).symm.trans hm.2.1
  · exact (integral_comp_eval (μ := fun _ : Fin 1 => observedLaw P)
      (i := 0) hz2).symm.trans hm.2.2.2

/-- Disjoint arm support and the exact arm moments give the contrast variance
in roadmap (25), without an independence assertion between arm scores. -/
-- @node: positiveRetention_subcriticalInfluence_contrast_moments
lemma positiveRetention_subcriticalInfluence_contrast_moments
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) :
    Integrable (fun o => subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) (observedLaw P) ∧
    (∫ o, subcriticalInfluence c P true o -
      subcriticalInfluence c P false o ∂observedLaw P) = 0 ∧
    Integrable (fun o => (subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) ^ 2) (observedLaw P) ∧
    (∫ o, (subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) ^ 2 ∂observedLaw P) = subcriticalVariance c P := by
  have h1 := positiveRetention_subcriticalInfluence_arm_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon true
  have h0 := positiveRetention_subcriticalInfluence_arm_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon false
  have he : (fun o => (subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) ^ 2) =
      fun o => subcriticalInfluence c P true o ^ 2 + subcriticalInfluence c P false o ^ 2 := by
    funext o
    exact subcriticalInfluence_contrast_sq c P o
  refine ⟨h1.1.sub h0.1, ?_, ?_, ?_⟩
  · rw [integral_sub h1.1 h0.1, h1.2.1, h0.2.1, sub_self]
  · rw [he]
    exact h1.2.2.1.add h0.2.2.1
  · rw [he, integral_add h1.2.2.1 h0.2.2.1, h1.2.2.2, h0.2.2.2]
    simp [subcriticalVariance, add_comm]

/-- The scalar contrast law uses the actual paper influence. -/
-- @node: positiveRetention_subcriticalContrastLaw
noncomputable def positiveRetention_subcriticalContrastLaw (c : ClassConstants) (P : SubjectLaw) : Measure ℝ :=
  (observedLaw P).map (fun o => subcriticalInfluence c P true o -
    subcriticalInfluence c P false o)

/-- The observed contrast is almost everywhere measurable. -/
-- @node: positiveRetention_aemeasurable_subcriticalContrast
@[fun_prop] lemma positiveRetention_aemeasurable_subcriticalContrast (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) :
    AEMeasurable (fun o => subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) (observedLaw P) := by
  exact (positiveRetention_aemeasurable_influence c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon true).sub
    (positiveRetention_aemeasurable_influence c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon false)

/-- The pushforward contrast law has zero mean and the exact paper variance. -/
-- @node: positiveRetention_subcriticalContrastLaw_moments
lemma positiveRetention_subcriticalContrastLaw_moments (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) :
    MemLp id 2 (positiveRetention_subcriticalContrastLaw c P) ∧
    (∫ x, x ∂positiveRetention_subcriticalContrastLaw c P) = 0 ∧
    (∫ x, x ^ 2 ∂positiveRetention_subcriticalContrastLaw c P) = subcriticalVariance c P := by
  have hm := positiveRetention_subcriticalInfluence_contrast_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon
  have ha := positiveRetention_aemeasurable_subcriticalContrast c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon
  have hs : Integrable (fun x : ℝ => x ^ 2) (positiveRetention_subcriticalContrastLaw c P) :=
    (integrable_map_measure (by fun_prop) ha).2 hm.2.2.1
  refine ⟨(memLp_two_iff_integrable_sq (by fun_prop)).2 hs, ?_, ?_⟩
  · rw [positiveRetention_subcriticalContrastLaw, integral_map ha (by fun_prop)]
    exact hm.2.1
  · rw [positiveRetention_subcriticalContrastLaw, integral_map ha (by fun_prop)]
    exact hm.2.2.2

/-- Finite contrast variance gives the square-root-scale Lindeberg tail,
with no boundedness or third-moment assumption. -/
-- @node: positiveRetention_subcriticalContrastLaw_lindeberg
lemma positiveRetention_subcriticalContrastLaw_lindeberg (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ∫ x in {x : ℝ | ε * Real.sqrt n ≤ |x|},
      x ^ 2 ∂positiveRetention_subcriticalContrastLaw c P) atTop (nhds 0) := by
  let Q := positiveRetention_subcriticalContrastLaw c P
  have hi : Integrable (fun x : ℝ => x ^ 2) Q :=
    (memLp_two_iff_integrable_sq (by fun_prop)).1
      (positiveRetention_subcriticalContrastLaw_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon).1
  have ht : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := Q) (f := fun _ : ℝ => (0 : ℝ))
    (F := fun n : ℕ => {x : ℝ | ε * Real.sqrt n ≤ |x|}.indicator (fun x => x ^ 2))
    (fun x : ℝ => x ^ 2)
    (Eventually.of_forall (fun n : ℕ =>
      ((measurable_id.pow_const 2).indicator
        (measurableSet_le measurable_const measurable_id.abs)).aestronglyMeasurable))
    (Eventually.of_forall (fun n : ℕ => by
      filter_upwards [] with x
      by_cases hx : ε * Real.sqrt n ≤ |x|
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx, sq_nonneg])) hi (by
      filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [ht.eventually_gt_atTop |x|] with n hn
      simp [Set.indicator, not_le.mpr hn])
  change Tendsto (fun n : ℕ => ∫ x,
    {x : ℝ | ε * Real.sqrt n ≤ |x|}.indicator (fun x => x ^ 2) x ∂Q)
    atTop (nhds (∫ x : ℝ, (0 : ℝ) ∂Q)) at h
  have he (n : ℕ) : (∫ x,
      {x : ℝ | ε * Real.sqrt n ≤ |x|}.indicator (fun x => x ^ 2) x ∂Q) =
      ∫ x in {x : ℝ | ε * Real.sqrt n ≤ |x|}, x ^ 2 ∂Q :=
    integral_indicator (measurableSet_le measurable_const measurable_id.abs)
  simp_rw [he] at h
  simpa only [integral_zero] using h

/-- The actual finite-sample influence-sum law is the iid scalar row law. -/
-- @node: positiveRetention_subcriticalInfluence_normalizedSumLaw_eq
lemma positiveRetention_subcriticalInfluence_normalizedSumLaw_eq (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (n : ℕ) :
    (sampleLaw P n).map (fun s => (∑ i : Fin n,
      (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
        Real.sqrt n) =
    (Measure.pi (fun _ : Fin n => positiveRetention_subcriticalContrastLaw c P)).map
      (fun y => (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have ha := positiveRetention_aemeasurable_subcriticalContrast c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon
  let Z := fun o => subcriticalInfluence c P true o - subcriticalInfluence c P false o
  letI : IsProbabilityMeasure (positiveRetention_subcriticalContrastLaw c P) :=
    Measure.isProbabilityMeasure_map ha
  have hp := Measure.pi_map_pi (fun _ : Fin n => ha)
  unfold positiveRetention_subcriticalContrastLaw
  have hv : AEMeasurable (fun s : Fin n → ObsHistory => fun i =>
      subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))
      (Measure.pi (fun _ : Fin n => observedLaw P)) :=
    aemeasurable_pi_lambda _ (fun i =>
      ha.comp_quasiMeasurePreserving
        (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving)
  have hr := AEMeasurable.map_map_of_aemeasurable
    (g := fun y : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y)
    ((Causalean.Stat.measurable_iidRowSum n).const_mul _).aemeasurable hv
  rw [← hp, hr]
  congr 1
  funext s
  simp [Function.comp_def, Causalean.Stat.iidRowSum, div_eq_mul_inv, mul_comm]

/-- The normalized actual influence contrast converges to the centered
Gaussian with the exact positive subcritical variance, as in roadmap (30). -/
-- @node: positiveRetention_subcriticalInfluence_normalizedSum_gaussian
lemma positiveRetention_subcriticalInfluence_normalizedSum_gaussian (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) :
    ConvergesInLaw (fun n : ℕ => (sampleLaw P n).map (fun s =>
      (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
        subcriticalInfluence c P false (s i))) / Real.sqrt n))
      (gaussianReal 0 (Real.toNNReal (subcriticalVariance c P))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (positiveRetention_subcriticalContrastLaw c P) :=
    Measure.isProbabilityMeasure_map (positiveRetention_aemeasurable_subcriticalContrast c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon)
  have hm := positiveRetention_subcriticalContrastLaw_moments c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon
  have hvar := (positiveRetention_variance_pos c P hOverlap hPoisson hDeath hRecurBounds hDeathBounds hHorizon).le
  have hclt := Causalean.Stat.iidRowNormalizedSumLaw_tendsto_gaussian
    (fun _ => positiveRetention_subcriticalContrastLaw c P) (Real.toNNReal (subcriticalVariance c P))
    (fun _ => hm.1) (fun _ => hm.2.1)
    (by simpa only [hm.2.2, Real.coe_toNNReal _ hvar] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => subcriticalVariance c P)
        atTop (nhds (subcriticalVariance c P))))
    (fun ε hε => positiveRetention_subcriticalContrastLaw_lindeberg c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon ε hε)
  intro f hf hb
  obtain ⟨M, hM⟩ := hb
  let F : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨f, hf⟩, ⟨2 * M, fun x y => by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hM x, hM y])⟩⟩
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hclt) F
  simpa [Causalean.Stat.iidRowNormalizedSumLaw, F,
    ← positiveRetention_subcriticalInfluence_normalizedSumLaw_eq c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon] using ht

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
