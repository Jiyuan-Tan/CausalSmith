module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleSecondMoment
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

/-!
# Observed-sample transport for the fixed-horizon death KM oracle action
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier
namespace DeathCP

private lemma kmOracleIntegrand_observed_compensator
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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

private lemma kmOracleIntegrand_observed_event
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
lemma aggregateIntegral_observedDeathSample_eq_oracleAction
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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
        kmOracleIntegrand P a T t x * referenceDeathHazard P a t *
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
      exact ((kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1).comp
        (measurable_id.prodMk measurable_const)).mul
        (measurable_referenceDeathHazard hP a) |>.mul hrisk
    have hhazI : IntervalIntegrable (P.hazard a) volume 0 T :=
      (hP.deathHazard.1 a).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
        exact Set.Icc_subset_Icc le_rfl hT1)
    have hhaz : IntegrableOn (P.hazard a) (Set.Icc 0 T) := by
      rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hT0] at hhazI
    apply (hhaz.const_mul (Real.exp c.dMax)).mono'
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans hT1⟩]
    have hri : Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∈
        Set.Icc (0 : ℝ) 1 := by
      unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
      split_ifs <;> norm_num
    have hhaz0 : 0 ≤ P.hazard a t := c.dMin_pos.le.trans
      (hP.deathBounds a t ⟨ht.1, ht.2.trans hT1⟩).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hhaz0,
      abs_of_nonneg hri.1]
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
          simpa using kmOracleWeight_abs_le_exp c P hP a hT0 hT1 (t := t)
    calc
      |kmOracleIntegrand P a T t x| * P.hazard a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ≤
        Real.exp c.dMax * P.hazard a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hH hhaz0) hri.1
      _ ≤ Real.exp c.dMax * P.hazard a t * 1 :=
        mul_le_mul_of_nonneg_left hri.2
          (mul_nonneg (Real.exp_pos _).le hhaz0)
      _ = Real.exp c.dMax * P.hazard a t := by ring
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
    exact kmOracleIntegrand_observed_compensator c P hP a s
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
  exact kmOracleIntegrand_observed_event P a s hDeathPos hNoTies i

/-- Squared fixed-horizon aggregate oracle actions transport exactly from the
observed iid sample to the canonical reference product sample. -/
lemma observedDeathSample_oracleAggregate_secondMoment_eq_reference
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ s : Fin n → ObsHistory,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) =
    ∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ :=
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
  have hJ : Measurable J :=
    measurable_kmOracle_aggregateIntegral c P hP a hT0 hT1
  have hreg := referenceSample_regular_ae c P hP a n
  have hobsMeas : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  calc
    _ = ∫ y : Sample n, (J y) ^ 2
        ∂(sampleLaw P n).map (observedDeathSample a) := by
      symm
      exact integral_map hobsMeas.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable
    _ = ∫ y : Sample n, (J y) ^ 2
        ∂μ.map referenceStoppedSyntheticSample := by
      rw [observedDeathSample_map_eq_reference P hP.deathHazard
        hP.randomAssignment hP.independentCensoring a]
    _ = ∫ x : Sample n, (J (referenceStoppedSyntheticSample x)) ^ 2 ∂μ := by
      exact integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable
    _ = ∫ x : Sample n, (J x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hreg] with x hx
      exact congrArg (fun z : ℝ => z ^ 2)
        (aggregateIntegral_referenceStoppedSyntheticSample
          (referenceDeathHazard P a) (kmOracleIntegrand P a T)
          (kmOracleIntegrand_leftPredictable P a T) x hx.1 hx.2.1 hx.2.2
          hT0 hT1)

/-- The observed aggregate oracle action inherits the canonical strict
fixed-horizon `1/n` second-moment bound. -/
lemma observedDeathSample_oracleAggregate_secondMoment_le_fixedRate
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (∫ s : Fin n → ObsHistory,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) ≤
      (2 / ((n : ℝ) *
        (c.pMin * retention P a T * Real.exp (-c.dMax)))) *
        ∫ t in Set.Icc 0 T,
          (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t ∂volume := by
  rw [observedDeathSample_oracleAggregate_secondMoment_eq_reference
    c P hP a n hT0 hT1.le]
  exact kmOracle_aggregate_secondMoment_le_fixedRate c P hP a hn hT0 hT1

/-- The observed fixed-horizon aggregate oracle action has an integrable
square under the actual iid sample law. -/
lemma observedDeathSample_oracleAggregate_sq_integrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory =>
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2) (sampleLaw P n) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ :=
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
  have hJ : Measurable J :=
    measurable_kmOracle_aggregateIntegral c P hP a hT0 hT1
  have hi : Integrable (fun x : Sample n => J x ^ 2) μ :=
    deathAggregateIntegral_sq_integrable _ _ _
      (armDeathFailureLaw_nonnegativeTimeLaw P a)
      (referenceDeathLaw_hasCensorHazard hP a) _
      (kmOracleIntegrand_leftPredictable P a T)
      (kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1) T hT0
      (kmOracleIntegrand_quadraticEnergyFinite c P hP a hT0 hT1)
      (kmOracle_predictableEnergy_integrable c P hP a hT0 hT1)
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  apply (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
    hs.aemeasurable).1
  rw [observedDeathSample_map_eq_reference P hP.deathHazard
    hP.randomAssignment hP.independentCensoring a]
  apply (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
    measurable_referenceStoppedSyntheticSample.aemeasurable).2
  apply hi.congr
  filter_upwards [referenceSample_regular_ae c P hP a n] with x hx
  exact congrArg (fun z : ℝ => z ^ 2)
    (aggregateIntegral_referenceStoppedSyntheticSample
      (referenceDeathHazard P a) (kmOracleIntegrand P a T)
      (kmOracleIntegrand_leftPredictable P a T) x hx.1 hx.2.1 hx.2.2
      hT0 hT1).symm

/-- On every regular observed path, the squared Kaplan--Meier endpoint error
is bounded by the squared oracle action plus the empty-risk indicator. -/
lemma deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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
    rcases survival_bounds_of_deathBounds c P hP.deathBounds a
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
    rw [deathKM_sub_survival_eq_neg_oracleAction P hP.deathHazard a s
      hT0 hT1 hExit0 hRisk,
      aggregateIntegral_observedDeathSample_eq_oracleAction
        c P hP a s hT0 hT1 hDeathPos hNoTies]
    ring_nf
    exact le_rfl

/-- The pathwise oracle inequality holds almost surely under the observed iid
law. -/
lemma deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∀ᵐ s ∂sampleLaw P n,
      (deathKM a s T - survival P a T) ^ 2 ≤
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
          (observedDeathSample a s)) ^ 2 +
        if riskSet a s T = 0 then 1 else 0 := by
  filter_upwards [sample_exit_nonneg P hP.deathHazard n,
    sample_arm_death_exit_pos_ae P hP.deathHazard a n,
    sample_death_exit_no_tie P hP.deathHazard n] with s hExit hDeath hTies
  exact deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk
    c P hP a s hT0 hT1 hExit hDeath (by
      intro i j hij hi hdi hj hdj
      exact hTies i j hij a hi hdi)

/-- Averaging the pathwise oracle inequality leaves only the canonical oracle
energy and the exact empty-risk probability. -/
lemma deathKM_secondMoment_le_oracleAggregate_add_emptyRisk
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ s : Fin n → ObsHistory,
      (deathKM a s T - survival P a T) ^ 2 ∂sampleLaw P n) ≤
      (∫ s : Fin n → ObsHistory,
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
          (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) +
      (sampleLaw P n).real {s | riskSet a s T = 0} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E : Set (Fin n → ObsHistory) := {s | riskSet a s T = 0}
  let J : (Fin n → ObsHistory) → ℝ := fun s =>
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
      (observedDeathSample a s)
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun
      ((measurable_recurrenceRiskSet_joint a).comp
        (measurable_id.prodMk measurable_const)) measurable_const
  have hJ : Integrable (fun s => J s ^ 2) (sampleLaw P n) :=
    observedDeathSample_oracleAggregate_sq_integrable c P hP a n hT0 hT1
  have hR : Integrable (fun s => J s ^ 2 + E.indicator (fun _ => 1) s)
      (sampleLaw P n) := hJ.add ((integrable_const 1).indicator hE)
  calc
    _ ≤ ∫ s, J s ^ 2 + E.indicator (fun _ => 1) s ∂sampleLaw P n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        hR (by
          filter_upwards [deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk_ae
            c P hP a n hT0 hT1] with s hs
          by_cases hz : riskSet a s T = 0
          · simpa [J, E, hz] using hs
          · simpa [J, E, hz] using hs)
    _ = (∫ s, J s ^ 2 ∂sampleLaw P n) +
        ∫ s, E.indicator (fun _ => 1) s ∂sampleLaw P n := integral_add hJ
          ((integrable_const 1).indicator hE)
    _ = _ := by
      rw [integral_indicator_const 1 hE]
      simp [J, E]

/-- At every strict fixed horizon, the Kaplan--Meier endpoint has an explicit
`1/n` mean-square envelope. The first term is the stopped martingale energy;
the second is the empty-risk contribution. -/
lemma deathKM_secondMoment_le_fixedRate
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (∫ s : Fin n → ObsHistory,
      (deathKM a s T - survival P a T) ^ 2 ∂sampleLaw P n) ≤
      (2 / ((n : ℝ) *
        (c.pMin * retention P a T * Real.exp (-c.dMax)))) *
        ∫ t in Set.Icc 0 T,
          (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t ∂volume +
      1 / ((n : ℝ) *
        (c.pMin * retention P a T * Real.exp (-c.dMax))) := by
  let q0 : ℝ := c.pMin * retention P a T * Real.exp (-c.dMax)
  let q : ℝ := P.p a * survival P a T * retention P a T
  have hr : 0 < retention P a T :=
    retention_pos_of_modelClass c P hP a T hT0 hT1
  have hq0 : 0 < q0 := by
    dsimp [q0]
    exact mul_pos (mul_pos c.pMin_pos hr) (Real.exp_pos _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0n : 0 < (n : ℝ) * q0 := mul_pos hnR hq0
  have hq : q0 ≤ q := by
    have hp : c.pMin ≤ P.p a := hP.treatmentOverlap a
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a
      ⟨hT0, hT1.le⟩).1
    have hbase : c.pMin * Real.exp (-c.dMax) ≤
        P.p a * survival P a T :=
      mul_le_mul hp hs (Real.exp_pos _).le
        (c.pMin_pos.le.trans hp)
    dsimp [q0, q]
    calc
      c.pMin * retention P a T * Real.exp (-c.dMax) =
          (c.pMin * Real.exp (-c.dMax)) * retention P a T := by ring
      _ ≤ (P.p a * survival P a T) * retention P a T :=
        mul_le_mul_of_nonneg_right hbase hr.le
      _ = P.p a * survival P a T * retention P a T := rfl
  have hEmpty : (sampleLaw P n).real {s | riskSet a s T = 0} ≤
      1 / ((n : ℝ) * q0) := by
    calc
      _ ≤ Real.exp (-((n : ℝ) * q)) := by
        simpa [q, Nat.cast_ofNat] using
          (riskSet_zero_probability_le_exp P hP a n ⟨hT0, hT1.le⟩)
      _ ≤ Real.exp (-((n : ℝ) * q0)) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_left hq hnR.le)
      _ ≤ 1 / ((n : ℝ) * q0) := by
        rw [Real.exp_neg]
        simpa [one_div] using
          (one_div_le_one_div_of_le hq0n
            (le_trans (by linarith : (n : ℝ) * q0 ≤ 1 + (n : ℝ) * q0)
              (by simpa [add_comm] using Real.add_one_le_exp ((n : ℝ) * q0))))
  calc
    _ ≤ (∫ s : Fin n → ObsHistory,
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
          (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) +
        (sampleLaw P n).real {s | riskSet a s T = 0} :=
      deathKM_secondMoment_le_oracleAggregate_add_emptyRisk
        c P hP a n hT0 hT1.le
    _ ≤ _ := add_le_add
      (observedDeathSample_oracleAggregate_secondMoment_le_fixedRate
        c P hP a hn hT0 hT1) hEmpty

end DeathCP
end CausalSmith.Stat.RecurrentEndpointCensorFrontier
