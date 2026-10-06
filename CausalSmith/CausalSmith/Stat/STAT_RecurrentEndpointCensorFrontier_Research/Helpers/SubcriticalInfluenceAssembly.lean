module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceMeasurability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleOrthogonality

/-!
# Pathwise assembly of the subcritical influence

Roadmap (23)--(25): identify the full-horizon canonical oracle with the
finite sum of the paper influences before transporting its proved moments.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A stopped recurrence score has the paper's interval compensator. -/
-- @node: observedRecurrence_compensator_eq_interval
lemma observedRecurrence_compensator_eq_interval (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) (o : ObsHistory)
    (ho : o.exit ∈ Icc (0 : ℝ) 1) :
    (∫ t, observedRecurrenceTimeWeight a 1 (fun t => (retention P a t)⁻¹) o t
      ∂recurrenceIntensity P a) =
      if o.treatment = a then ∫ t in (0 : ℝ)..o.exit,
        P.lam a t / retention P a t else 0 := by
  by_cases ha : o.treatment = a
  · rw [if_pos ha]
    have heq : observedRecurrenceTimeWeight a 1 (fun t => (retention P a t)⁻¹) o =
        fun t => if t ≤ o.exit then (retention P a t)⁻¹ else 0 := by
      funext t
      by_cases ht : t ≤ o.exit
      · simp [observedRecurrenceTimeWeight, ha, ht, ht.trans ho.2]
      · simp [observedRecurrenceTimeWeight, ha, ht]
    rw [heq, recurrenceIntensity_integral_truncated P hP a _ ho.1 ho.2]
    apply intervalIntegral.integral_congr
    intro t _
    simp [div_eq_mul_inv, mul_comm]
  · simp [observedRecurrenceTimeWeight, ha]

/-- The canonical subject death oracle is the paper's assignment-scaled death score. -/
-- @node: subcriticalDeathOracle_subject_eq
lemma subcriticalDeathOracle_subject_eq (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n)
    (ho : (s i).exit ∈ Icc (0 : ℝ) 1) :
    subjectIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) i 1
      (observedDeathSample a s) =
    (if (s i).treatment = a then
      (if (s i).deathInd then remainingTarget c P a 0 (s i).exit /
        (survival P a (s i).exit * retention P a (s i).exit) else 0) -
      ∫ t in (0 : ℝ)..(s i).exit,
        remainingTarget c P a 0 t * P.hazard a t /
          (survival P a t * retention P a t) else 0) / P.p a := by
  classical
  have hint : (∫ t in Icc (0 : ℝ) 1,
      subcriticalDeathOracleWeight c P a t * referenceDeathHazard P a t *
        riskIndicator i t (observedDeathSample a s)) =
      if (s i).treatment = a then
        (∫ t in (0 : ℝ)..(s i).exit,
          remainingTarget c P a 0 t * P.hazard a t /
            (survival P a t * retention P a t)) / P.p a else 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    by_cases ha : (s i).treatment = a
    · rw [if_pos ha]
      rw [← intervalIntegral.integral_div]
      rw [← intervalIntegral.integral_indicator ho]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      dsimp only
      rw [referenceDeathHazard_eq P a ht]
      have hw : deathTargetWeight c P a 0 t = remainingTarget c P a 0 t / survival P a t := by
        simp [deathTargetWeight, ht]
      by_cases he : t ≤ (s i).exit
      · have he1 : t ≤ (s i).exit + 1 := by linarith
        cases hd : (s i).deathInd <;> simp [riskIndicator, observedDeathSample, observedDeathPair, ha, hd,
          ht.1, he, he1, subcriticalDeathOracleWeight, hw, Set.indicator]
        <;> ring
      · cases hd : (s i).deathInd <;> simp [riskIndicator, observedDeathSample, observedDeathPair, ha, hd,
          he, subcriticalDeathOracleWeight, Set.indicator]
    · rw [if_neg ha]
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hn : ¬ t ≤ (0 : ℝ) := not_le_of_gt ht.1
      simp [riskIndicator, observedDeathSample, observedDeathPair, ha, hn]
  unfold subjectIntegral
  rw [hint]
  by_cases ha : (s i).treatment = a
  · have hw : deathTargetWeight c P a 0 (s i).exit =
        remainingTarget c P a 0 (s i).exit / survival P a (s i).exit := by
      simp [deathTargetWeight, ho]
    cases hd : (s i).deathInd <;>
      simp [observedDeathSample, observedDeathPair, ha, hd, ho.2,
        subcriticalDeathOracleWeight, hw, show ¬ (1 : ℝ) < 0 by norm_num]
    <;> ring
  · simp [observedDeathSample, observedDeathPair, ha]

/-- Every retained recurrence point is at or before its stopping time. -/
-- @node: stoppedRecurrence_point_le
lemma stoppedRecurrence_point_le (r : RecurConfig) (x : ℝ)
    (j : Fin (r.stopAt x).1) : ((r.stopAt x).2 j).1 ≤ x := by
  classical
  revert j
  rw [RecurConfig.stopAt_eq_restrictAt]
  unfold RecurConfig.restrictAt
  intro j
  let u := (timeCutPartition x).cellIndices true r
  change (r.2 ((u.orderIsoOfFin rfl j).1)).1 ≤ x
  have h := (u.orderIsoOfFin rfl j).2
  simpa [u, FiniteMeasurablePartition.cellIndices, timeCutPartition,
    FiniteSample.points] using h

/-- The horizon filter is inactive on an observed stopped configuration. -/
-- @node: observedRecurrence_full_point_sum
lemma observedRecurrence_full_point_sum (z : LatentSubject) (f : ℝ → ℝ) :
    ((((observe z).recur.times.filter (fun t => t ≤ 1)).map f).sum) =
      ((observe z).recur.times.map f).sum := by
  classical
  rw [recurrence_times_filtered_sum, recurrence_times_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hx : (observe z).exit ≤ 1 := by
    have hc : censorHorizon z z.treatment ≤ 1 := by
      unfold censorHorizon
      split_ifs <;> simp
    exact (min_le_right _ _).trans hc
  have hj : ((observe z).recur.2 j).1 ≤ (observe z).exit :=
    stoppedRecurrence_point_le _ _ j
  exact if_pos (hj.trans hx)

/-- The finite full-horizon arm oracle is exactly the sum of the paper's
influences on observed latent paths. -/
-- @node: observedSubcriticalArmOracle_eq_influence_sum
lemma observedSubcriticalArmOracle_eq_influence_sum
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
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
    observedRecurrence_compensator_eq_interval P hP.poissonRecurrence a _ (ho i),
    observedRecurrence_full_point_sum]
  unfold subcriticalInfluence
  by_cases ha : (observe (z i)).treatment = a <;> simp [ha]

/-- The oracle-to-influence identity holds almost surely under the actual iid law. -/
-- @node: observedSubcriticalArmOracle_ae_eq_influence_sum
lemma observedSubcriticalArmOracle_ae_eq_influence_sum
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
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
    (hP.poissonRecurrence a).2.2.1
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
    · exact (measurable_deathAggregateIntegral_deterministic _ _
        (measurable_referenceDeathHazard hP a)
        (measurable_subcriticalDeathOracleWeight c P hP a) 1).comp
          (measurable_pi_lambda _ (fun i =>
            (measurable_observedDeathPair a).comp (measurable_pi_apply i)))
  have hG : Measurable G := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_measurableSubcriticalInfluence c P hP hk a).comp
      (measurable_pi_apply i)
  have hFG : F =ᵐ[sampleLaw P n] G := by
    rw [recurrence_sampleLaw_eq_latent_map]
    apply (ae_map_iff (show Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) by fun_prop).aemeasurable
      (measurableSet_eq_fun hF hG)).2
    have he : ∀ᵐ z ∂P.latent, (observe z).exit ∈ Icc (0 : ℝ) 1 := by
      exact (ae_map_iff measurable_observe.aemeasurable
        (measurableSet_Icc.preimage measurable_obsHistory_exit)).1
          (observed_exit_mem_Icc_ae P hP.deathHazard)
    have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
        ∀ i, (observe (z i)).exit ∈ Icc (0 : ℝ) 1 := by
      rw [Filter.eventually_all]
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => P.latent) i).quasiMeasurePreserving.ae he
    filter_upwards [hall] with z hz
    change F (fun i => observe (z i)) = G (fun i => observe (z i))
    dsimp [F, G]
    rw [observedSubcriticalArmOracle_eq_influence_sum c P hP a z hz]
    apply Finset.sum_congr rfl
    intro i _
    exact (measurableSubcriticalInfluence_eq c P hP a _ (hz i)).symm
  exact hFG.trans (sum_subcriticalInfluence_ae_eq_measurableRepresentative c P hP a n).symm

/-- The actual armwise influence sum is centered and square integrable,
with exactly n times its paper variance contribution. -/
-- @node: subcriticalInfluence_sum_moments
lemma subcriticalInfluence_sum_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    let Z := fun s : Fin n → ObsHistory => ∑ i, subcriticalInfluence c P a (s i)
    Integrable Z (sampleLaw P n) ∧
    (∫ s, Z s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => Z s ^ 2) (sampleLaw P n) ∧
    (∫ s, Z s ^ 2 ∂sampleLaw P n) =
      ((n : ℝ) / P.p a) * ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t) := by
  have hm := observedSubcriticalArmOracle_full_moments c P hP hk a hn
  have he := observedSubcriticalArmOracle_ae_eq_influence_sum c P hP hk a n
  have he2 := he.fun_comp (fun x : ℝ => x ^ 2)
  dsimp only [Function.comp_def] at he2
  dsimp only
  refine ⟨hm.1.congr he, (integral_congr_ae he.symm).trans hm.2.1,
    hm.2.2.1.congr he2, ?_⟩
  rw [integral_congr_ae he2.symm, hm.2.2.2,
    intervalIntegral.integral_add
      (subcritical_recurrence_energy_intervalIntegrable c P hP hk a)
      (subcritical_death_energy_intervalIntegrable c P hP hk a)]

/-- Each one-subject influence is centered and has its exact full-horizon
variance, derived from the oracle moments at sample size one. -/
-- @node: subcriticalInfluence_arm_moments
lemma subcriticalInfluence_arm_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
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
  have hm := subcriticalInfluence_sum_moments c P hP hk a (n := 1) (by norm_num)
  simp only [Fin.sum_univ_one, Nat.cast_one, one_div] at hm
  have hz := (aemeasurable_subcriticalInfluence c P hP hk a).aestronglyMeasurable
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
-- @node: subcriticalInfluence_contrast_moments
lemma subcriticalInfluence_contrast_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) :
    Integrable (fun o => subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) (observedLaw P) ∧
    (∫ o, subcriticalInfluence c P true o -
      subcriticalInfluence c P false o ∂observedLaw P) = 0 ∧
    Integrable (fun o => (subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) ^ 2) (observedLaw P) ∧
    (∫ o, (subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) ^ 2 ∂observedLaw P) = subcriticalVariance c P := by
  have h1 := subcriticalInfluence_arm_moments c P hP hk true
  have h0 := subcriticalInfluence_arm_moments c P hP hk false
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

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
