module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathRegularity

/-!
# Observed death-integral transport for the positive-retention benchmark

Roadmap (6) and (9): identify the death error with the canonical compensated
integral under the benchmark hazard assumptions. Local hazard integrability
suffices; no endpoint Hölder continuity or global measurable hazard is assumed.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

-- @node: positiveRetention_deathCPIntegrand_observed_compensator
lemma positiveRetention_deathCPIntegrand_observed_compensator (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h t : ℝ} (hh : 0 ≤ h) (ht0 : 0 < t)
    (htU : t ≤ 1 - h)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    deathCPIntegrand c P a h t (observedDeathSample a s) *
        referenceDeathHazard P a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
            (observedDeathSample a s)) =
      remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
        (if riskSet a s t = 0 then 0 else P.hazard a t) := by
  have ht1 : t ≤ 1 := by linarith
  rw [referenceDeathHazard_eq P a ⟨ht0.le, ht1⟩]
  rw [deathCPIntegrand, deathTargetWeight, if_pos ⟨ht0.le, htU⟩]
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
  convert deathCompensator_integrand c P a s h t using 1 <;> ring

-- @node: positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError
lemma positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
      (observedDeathSample a s) = deathError c P a s h := by
  classical
  let U : ℝ := 1 - h
  let x := observedDeathSample a s
  have hU0 : 0 ≤ U := by dsimp [U]; linarith
  have hc := (positiveRetention_continuousOn_deathTargetWeight c P hPoisson
    hDeath hDeathBounds a hh hh1).abs
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by exact ⟨0, by constructor <;> linarith⟩) hc
  let C := |deathTargetWeight c P a h t|
  have hC0 : 0 ≤ C := abs_nonneg _
  have hC : ∀ u ∈ Set.Icc (0 : ℝ) (1 - h), |deathTargetWeight c P a h u| ≤ C :=
    fun u hu => hmax hu
  have hhazI : IntervalIntegrable (P.hazard a) volume 0 U :=
    (hDeath.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hU0]
      exact Set.Icc_subset_Icc le_rfl (by dsimp [U]; linarith))
  have hhaz : IntegrableOn (P.hazard a) (Set.Icc 0 U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at hhazI
  have hterm (i : Fin n) : IntegrableOn (fun t =>
      deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
      (Set.Icc 0 U) := by
    let f : ℝ → ℝ := fun t => deathCPIntegrand c P a h t x *
      Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x
    have hm : Measurable f := by
      have hrisk : Measurable (fun t : ℝ =>
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        apply Measurable.ite
        · exact (measurableSet_le measurable_const measurable_id).inter
            ((measurableSet_le measurable_id measurable_const).inter
              (measurableSet_le measurable_id measurable_const))
        · exact measurable_const
        · exact measurable_const
      exact ((positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson
        hDeath hDeathBounds a hh hh1).comp
        (measurable_id.prodMk measurable_const)).mul hrisk
    have hprod : IntegrableOn (fun t => f t * P.hazard a t) (Set.Icc 0 U) := by
      apply hhaz.bdd_mul hm.aestronglyMeasurable (c := C)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hri : |Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x| ≤ 1 := by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num
      rw [Real.norm_eq_abs, show f t = deathCPIntegrand c P a h t x *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x from rfl, abs_mul]
      calc
        _ ≤ |deathCPIntegrand c P a h t x| * 1 :=
          mul_le_mul_of_nonneg_left hri (abs_nonneg _)
        _ ≤ C := by
          simpa using (deathCPIntegrand_abs_le c P a h t x).trans (hC t ht)
    apply hprod.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans (by dsimp [U] at ht ⊢; linarith)⟩]
    dsimp [f]
    ring
  have hsumInt : IntegrableOn (fun t => ∑ i : Fin n,
      deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
      (Set.Icc 0 U) :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hcomp : (∫ t in Set.Icc 0 U, ∑ i : Fin n,
      deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∂volume) =
      ∫ t in (0 : ℝ)..U,
        remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
          (if riskSet a s t = 0 then 0 else P.hazard a t) := by
    rw [intervalIntegral.integral_of_le hU0, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ((volume.restrict (Set.Icc 0 U)).ae_ne (0 : ℝ))] with t ht htne
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
    rw [← Finset.mul_sum]
    simpa only [x, mul_assoc] using
      positiveRetention_deathCPIntegrand_observed_compensator c P a s hh ht0
        (by simpa only [U] using ht.2) hDeathPos hNoTies
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
    Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral deathError
  rw [Finset.sum_sub_distrib]
  rw [← integral_finsetSum Finset.univ (fun i _ => hterm i)]
  rw [hcomp]
  apply congrArg (fun z => z - ∫ t in (0 : ℝ)..U,
    remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
      (if riskSet a s t = 0 then 0 else P.hazard a t))
  apply Finset.sum_congr rfl
  intro i _
  simpa only [x, U] using
    deathCPIntegrand_observed_event c P a s hh hh1 hDeathPos hNoTies i

-- @node: positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError_ae
lemma positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (fun s : Fin n → ObsHistory =>
      Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
        (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      (fun s => deathError c P a s h) := by
  filter_upwards [sample_arm_death_exit_pos_ae P hDeath a n,
    sample_death_exit_no_tie P hDeath n] with s hpos hties
  apply positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError
    c P hPoisson hDeath hDeathBounds a s hh hh1 hpos
  intro i j hij hai hdi haj hdj
  exact hties i j hij a hai hdi

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
