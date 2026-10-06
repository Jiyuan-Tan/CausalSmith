module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionLocalization

/-!
# Full-horizon observable KM consistency under positive retention

Roadmap (19)--(22): identify the actual KM endpoint error with its dependent
oracle action on nonempty risk sets, then use the transported second moment
and terminal-risk localization. Bounded integrable hazards suffice.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The observed oracle compensator agrees with the source-hazard risk-set expression. -/
-- @node: positiveRetention_kmOracleIntegrand_observed_compensator
lemma positiveRetention_kmOracleIntegrand_observed_compensator
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {T t : ℝ} (ht0 : 0 < t)
    (htT : t ≤ T) (hT1 : T ≤ 1)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    kmOracleIntegrand P a T t (observedDeathSample a s) *
        referenceDeathHazard P a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
            (observedDeathSample a s)) =
      survival P a T * (deathKMLeft a s t / survival P a t *
        (if riskSet a s t = 0 then 0 else P.hazard a t)) := by
  rw [referenceDeathHazard_eq P a ⟨ht0.le, htT.trans hT1⟩]
  rw [kmOracleIntegrand, kmOracleWeight, if_pos ⟨ht0.le, htT⟩]
  rw [pairDeathKMLeft_observedDeathSample_eq_deathKMLeft a s hDeathPos hNoTies]
  rw [observedDeathSample_inverseRisk a s ht0]
  have hrisk : (∑ i : Fin n,
      Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
        (observedDeathSample a s)) = (riskSet a s t : ℝ) := by
    calc
      _ = (Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t
          (observedDeathSample a s) : ℝ) := by
        simp [Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskSet]
      _ = _ := by rw [observedDeathSample_riskSet a s ht0]
  rw [hrisk]
  have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  rw [show survival P a T / survival P a t * deathKMLeft a s t *
      invRisk a s t * P.hazard a t * (riskSet a s t : ℝ) =
      survival P a T * (deathKMLeft a s t / survival P a t) *
        ((riskSet a s t : ℝ) * invRisk a s t) * P.hazard a t by ring,
    riskSet_mul_invRisk]
  split_ifs <;> field_simp <;> ring

/-- Each observed death contributes the source oracle jump with its survival multiplier. -/
-- @node: positiveRetention_kmOracleIntegrand_observed_event
lemma positiveRetention_kmOracleIntegrand_observed_event
    (P : SubjectLaw) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {T : ℝ} (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd →
      0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit)
    (i : Fin n) :
    (if (observedDeathSample a s i).2 ≤ T ∧
        (observedDeathSample a s i).2 < (observedDeathSample a s i).1 then
      kmOracleIntegrand P a T (observedDeathSample a s i).2
        (observedDeathSample a s) else 0) =
    survival P a T *
      (if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ T then
        deathKMLeft a s (s i).exit / survival P a (s i).exit *
          invRisk a s (s i).exit else 0) := by
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd
    · by_cases he : (s i).exit ≤ T
      · have heq : (observedDeathSample a s i).2 = (s i).exit := by
          simp [observedDeathSample, observedDeathPair, ha, hd]
        have hlt : (observedDeathSample a s i).2 <
            (observedDeathSample a s i).1 := by
          simp [observedDeathSample, observedDeathPair, ha, hd]
        rw [if_pos ⟨heq.trans_le he, hlt⟩, if_pos ⟨ha, hd, he⟩, heq]
        rw [kmOracleIntegrand, kmOracleWeight,
          if_pos ⟨(hDeathPos i ha hd).le, he⟩]
        rw [pairDeathKMLeft_observedDeathSample_eq_deathKMLeft
          a s hDeathPos hNoTies]
        rw [observedDeathSample_inverseRisk a s (hDeathPos i ha hd)]
        ring
      · have heq : (observedDeathSample a s i).2 = (s i).exit := by
          simp [observedDeathSample, observedDeathPair, ha, hd]
        rw [if_neg (by simp [heq, he]), if_neg (by simp [ha, hd, he])]
        ring
    · simp [observedDeathSample, observedDeathPair, ha, hd]
  · simp [observedDeathSample, observedDeathPair, ha]

/-- On a regular observed path the canonical aggregate oracle integral is
survival at `T` times the paper oracle action. -/
-- @node: positiveRetention_aggregateIntegral_observedDeathSample_eq_oracleAction
lemma positiveRetention_aggregateIntegral_observedDeathSample_eq_oracleAction
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
      (observedDeathSample a s) = survival P a T * deathKMOracleAction P a s T := by
  classical
  let x := observedDeathSample a s
  have hterm (i : Fin n) : IntegrableOn (fun t =>
      kmOracleIntegrand P a T t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
      (Set.Icc 0 T) := by
    have hm : Measurable (fun t =>
        kmOracleIntegrand P a T t x *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
      have hrisk : Measurable (fun t : ℝ =>
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        apply Measurable.ite
        · exact (measurableSet_le measurable_const measurable_id).inter
            ((measurableSet_le measurable_id measurable_const).inter
              (measurableSet_le measurable_id measurable_const))
        · exact measurable_const
        · exact measurable_const
      exact ((positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1).comp
        (measurable_id.prodMk measurable_const)).mul hrisk
    have hhazI : IntervalIntegrable (P.hazard a) volume 0 T :=
      (hDeath.1 a).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
        exact Set.Icc_subset_Icc le_rfl hT1)
    have hhaz : IntegrableOn (P.hazard a) (Set.Icc 0 T) := by
      rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hT0] at hhazI
    have hprod : IntegrableOn (fun t =>
        (kmOracleIntegrand P a T t x *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) *
          P.hazard a t) (Set.Icc 0 T) := by
      apply hhaz.bdd_mul hm.aestronglyMeasurable (c := Real.exp c.dMax)
      filter_upwards [] with t
      have hri : Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∈
          Set.Icc (0 : ℝ) 1 := by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num
      have hH : |kmOracleIntegrand P a T t x| ≤ Real.exp c.dMax := by
        rw [kmOracleIntegrand, abs_mul, abs_mul]
        have hkm := pairDeathKMLeft_mem_Icc t x
        have hinv := pairInverseRisk_mem_Icc t x
        rw [abs_of_nonneg hkm.1, abs_of_nonneg hinv.1]
        calc
          _ ≤ |kmOracleWeight P a T t| * 1 *
              Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkm.2 (abs_nonneg _)) hinv.1
          _ ≤ |kmOracleWeight P a T t| * 1 * 1 :=
            mul_le_mul_of_nonneg_left hinv.2
              (mul_nonneg (abs_nonneg _) zero_le_one)
          _ ≤ Real.exp c.dMax := by
            simpa using positiveRetention_kmOracleWeight_abs_le_exp c P hDeath hDeathBounds a hT0 hT1 (t := t)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hri.1]
      exact (mul_le_mul_of_nonneg_right hH hri.1).trans
        (mul_le_of_le_one_right (Real.exp_pos _).le hri.2)
    apply hprod.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans hT1⟩]
    ring
  have hcomp : (∫ t in Set.Icc 0 T, ∑ i : Fin n,
      kmOracleIntegrand P a T t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∂volume) =
      survival P a T * ∫ t in (0 : ℝ)..T,
        deathKMLeft a s t / survival P a t *
          (if riskSet a s t = 0 then 0 else P.hazard a t) := by
    rw [intervalIntegral.integral_of_le hT0, ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ((volume.restrict (Set.Icc 0 T)).ae_ne (0 : ℝ))] with t ht htne
    rw [← Finset.mul_sum]
    exact positiveRetention_kmOracleIntegrand_observed_compensator c P hDeath hDeathBounds a s
      (lt_of_le_of_ne ht.1 (Ne.symm htne)) ht.2 hT1 hDeathPos hNoTies
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
    Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral
    deathKMOracleAction
  rw [Finset.sum_sub_distrib,
    ← integral_finsetSum Finset.univ (fun i _ => hterm i), hcomp]
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact positiveRetention_kmOracleIntegrand_observed_event P a s hDeathPos hNoTies i


/-- On every regular observed path, the squared Kaplan--Meier endpoint error
is bounded by the squared oracle action plus the empty-risk indicator. -/
-- @node: positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk
lemma positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) (hExit0 : ∀ i, 0 ≤ (s i).exit)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    (deathKM a s T - survival P a T) ^ 2 ≤
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2 +
      if riskSet a s T = 0 then 1 else 0 := by
  by_cases hRisk : riskSet a s T = 0
  · rw [if_pos hRisk]
    rcases deathKM_mem_Icc a s T with ⟨hkm0, hkm1⟩
    rcases survival_bounds_of_deathBounds c P hDeathBounds a
      ⟨hT0, hT1⟩ with ⟨hs0, hs1⟩
    have hs_nonneg : 0 ≤ survival P a T :=
      le_trans (Real.exp_pos _).le hs0
    have herr_lower : -1 ≤ deathKM a s T - survival P a T := by linarith
    have herr_upper : deathKM a s T - survival P a T ≤ 1 := by linarith
    have herr_sq : (deathKM a s T - survival P a T) ^ 2 ≤ 1 := by
      nlinarith
    nlinarith [sq_nonneg (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
      (observedDeathSample a s))]
  · rw [if_neg hRisk]
    rw [deathKM_sub_survival_eq_neg_oracleAction P hDeath a s
      hT0 hT1 hExit0 hRisk,
      positiveRetention_aggregateIntegral_observedDeathSample_eq_oracleAction
        c P hDeath hDeathBounds a s hT0 hT1 hDeathPos hNoTies]
    ring_nf
    exact le_rfl

/-- The pathwise oracle inequality holds almost surely under the observed iid
law. -/
-- @node: positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk_ae
lemma positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk_ae
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∀ᵐ s ∂sampleLaw P n,
      (deathKM a s T - survival P a T) ^ 2 ≤
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
          (observedDeathSample a s)) ^ 2 +
        if riskSet a s T = 0 then 1 else 0 := by
  filter_upwards [sample_exit_nonneg P hDeath n,
    sample_arm_death_exit_pos_ae P hDeath a n,
    sample_death_exit_no_tie P hDeath n] with s hExit hPos hTies
  exact positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk
    c P hDeath hDeathBounds a s hT0 hT1 hExit hPos (by
      intro i j hij hi hdi hj hdj
      exact hTies i j hij a hi hdi)


/-- Averaging the pathwise oracle inequality leaves only the canonical oracle
energy and the exact empty-risk probability. -/
-- @node: positiveRetention_deathKM_terminal_secondMoment_le_oracleAggregate_add_emptyRisk
lemma positiveRetention_deathKM_terminal_secondMoment_le_oracleAggregate_add_emptyRisk
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm)
    (n : ℕ) :
    (∫ s : Fin n → ObsHistory,
      (deathKM a s 1 - survival P a 1) ^ 2 ∂sampleLaw P n) ≤
      (∫ s : Fin n → ObsHistory,
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (kmOracleIntegrand P a 1) 1
          (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) +
      (sampleLaw P n).real {s | riskSet a s 1 = 0} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E : Set (Fin n → ObsHistory) := {s | riskSet a s 1 = 0}
  let J : (Fin n → ObsHistory) → ℝ := fun s =>
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a 1) 1
      (observedDeathSample a s)
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun
      ((measurable_recurrenceRiskSet_joint a).comp
        (measurable_id.prodMk measurable_const)) measurable_const
  have hJ : Integrable (fun s => J s ^ 2) (sampleLaw P n) := by
    have hi := positiveRetention_observedDeathSample_oracleAggregate_sq_integrable
        c P hDeath hDeathBounds hRandom hCensor a n (T := 1) (by norm_num) (by norm_num)
    simpa only [J, positiveRetention_referenceHazard_aggregateIntegral_eq] using hi
  have hR : Integrable (fun s => J s ^ 2 + E.indicator (fun _ => 1) s)
      (sampleLaw P n) := hJ.add ((integrable_const 1).indicator hE)
  calc
    _ ≤ ∫ s, J s ^ 2 + E.indicator (fun _ => 1) s ∂sampleLaw P n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        hR (by
          filter_upwards [positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk_ae
            c P hDeath hDeathBounds a n (T := 1) (by norm_num) (by norm_num)] with s hs
          by_cases hz : riskSet a s 1 = 0
          · simpa [J, E, hz] using hs
          · simpa [J, E, hz] using hs)
    _ = (∫ s, J s ^ 2 ∂sampleLaw P n) +
        ∫ s, E.indicator (fun _ => 1) s ∂sampleLaw P n := integral_add hJ
          ((integrable_const 1).indicator hE)
    _ = _ := by
      rw [integral_indicator_const 1 hE]
      simp [J, E]


/-- The death Kaplan–Meier estimate is jointly measurable, with each distinct
exit time contributing its one aggregate decrement. -/
-- @node: positiveRetention_measurable_deathKM_joint
@[fun_prop] lemma positiveRetention_measurable_deathKM_joint {n : ℕ} (a : Arm) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ => deathKM a p.1 p.2) := by
  classical
  have heq : (fun p : (Fin n → ObsHistory) × ℝ => deathKM a p.1 p.2) =
      fun p => ∏ u ∈ Finset.univ.image (fun i => (p.1 i).exit),
        if u ≤ p.2 then 1 - invRisk a p.1 u * deathJump a p.1 u else 1 := by
    funext p
    simp only [deathKM, exitTimes, Finset.prod_filter]
  rw [heq]
  apply measurable_recurrence_prod_image
  · intro i
    fun_prop
  · intro i
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_snd)
    · have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
          (p.1, (p.1 i).exit)) := by fun_prop
      exact measurable_const.sub
        (((measurable_recurrenceInvRisk_joint a).comp hm).mul
          ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
            ((measurable_recurrenceDeathJump_joint a).comp hm)))
    · exact measurable_const

/-- The observed KM endpoint error has an integrable square under the death envelope. -/
-- @node: positiveRetention_deathKM_error_sq_integrable
lemma positiveRetention_deathKM_error_sq_integrable (c : ClassConstants)
    (P : SubjectLaw) (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ)
    {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    Integrable (fun s : Fin n → ObsHistory =>
      (deathKM a s T - survival P a T) ^ 2) (sampleLaw P n) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      (deathKM a s T - survival P a T) ^ 2) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hk := deathKM_mem_Icc a s T
  have hs := survival_bounds_of_deathBounds c P hDeathBounds a hT
  nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]

/-- The observable KM endpoint is consistent in second mean at the full horizon,
by dependent oracle energy and the actual empty-risk probability. -/
-- @node: positiveRetention_deathKM_terminal_secondMoment_tendsto_zero
lemma positiveRetention_deathKM_terminal_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (deathKM a s 1 - survival P a 1) ^ 2 ∂sampleLaw P n)
      atTop (nhds 0) := by
  let C : ℝ := 2 * (Real.exp c.dMax) ^ 2 * c.dMax /
    (c.pMin * Real.exp (-c.dMax) * c.Ghor)
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Pi.inv_apply] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C
  have hempty := positiveRetention_terminal_emptyRisk_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
  apply squeeze_zero' (Eventually.of_forall (fun _ =>
    integral_nonneg (fun _ => sq_nonneg _))) _
    (by simpa only [add_zero] using hlim.add hempty)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := positiveRetention_observedKMOracle_secondMoment_le_inv_sampleSize
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
    (n := n) (by omega)
  simp only [positiveRetention_referenceHazard_aggregateIntegral_eq] at hb
  exact (positiveRetention_deathKM_terminal_secondMoment_le_oracleAggregate_add_emptyRisk
    c P hDeath hDeathBounds hRandom hCensor a n).trans (add_le_add hb le_rfl)

/-- The actual full-horizon KM endpoint converges in probability by its second moment. -/
-- @node: positiveRetention_deathKM_terminal_probability_tendsto_zero
lemma positiveRetention_deathKM_terminal_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |deathKM a s 1 - survival P a 1|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [zero_div] using
      (positiveRetention_deathKM_terminal_secondMoment_tendsto_zero c P hRandom
        hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).div_const (ε ^ 2))
  intro n
  exact positiveRetention_probability_le_secondMoment (sampleLaw P n) _
    (positiveRetention_deathKM_error_sq_integrable c P hDeathBounds a n (by norm_num)) hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
