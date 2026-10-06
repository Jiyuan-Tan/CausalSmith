module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedDeathOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleMeanEnergy

/-!
# Positive-retention death difference moments

Roadmap (24), (26)--(27): the predictable normalized death coefficient
has finite product energy under the benchmark assumptions. The measurable
hazard representative supplies the exact isometry without endpoint smoothness.
-/

public section

open MeasureTheory Set Filter
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The canonical difference coefficient is jointly measurable. -/
-- @node: positiveRetention_measurable_deathOracleDifferenceIntegrand
@[fun_prop]
lemma positiveRetention_measurable_deathOracleDifferenceIntegrand
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    Measurable (fun p : ℝ × Sample n => deathOracleDifferenceIntegrand c P a p.1 p.2) := by
  unfold deathOracleDifferenceIntegrand
  have hi := positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson hDeath hDeathBounds a
    (n := n) (h := 0) (by norm_num) (by norm_num)
  have ho : Measurable (fun p : ℝ × Sample n => subcriticalDeathOracleWeight c P a p.1) :=
    (positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath hDeathBounds a).comp
      measurable_fst
  fun_prop

/-- The canonical difference has integrable product energy, using the KM
energy envelope and the genuine unbounded oracle energy separately. -/
-- @node: positiveRetention_deathOracleDifferenceIntegrand_energy_integrable_prod
lemma positiveRetention_deathOracleDifferenceIntegrand_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hOverlap : TreatmentOverlap c P)
    (hRecurBounds : RecurrenceBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n :
      ℕ) :
    Integrable (fun p : Sample n × ℝ =>
      deathOracleDifferenceIntegrand c P a p.2 p.1 ^ 2 *
        DeathCP.positiveRetention_referenceHazard P hDeath a p.2 * (∑ i : Fin n, riskIndicator i
          p.2 p.1))
      ((Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)).prod
          (volume.restrict (Icc (0 : ℝ) 1))) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  let f := fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t
  have hf : Integrable f ν := by
    simpa only [f, ν, IntegrableOn] using
      positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn
      c P hPoisson hDeath hRecurBounds hDeathBounds a
  have ho := positiveRetention_deathOracle_energy_integrable_prod c P hOverlap hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon a n
  have hm : Measurable (fun p : Sample n × ℝ =>
      deathOracleDifferenceIntegrand c P a p.2 p.1 ^ 2 *
        DeathCP.positiveRetention_referenceHazard P hDeath a p.2 * (∑ i : Fin n, riskIndicator i
          p.2 p.1)) :=
    (((positiveRetention_measurable_deathOracleDifferenceIntegrand c P hPoisson hDeath
      hDeathBounds a n).comp
      measurable_swap).pow_const 2 |>.mul
        ((DeathCP.positiveRetention_referenceHazard_measurable P hDeath a).comp measurable_snd)).mul
          (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  apply ((hf.comp_snd (μ := μ)).const_mul (2 * (Real.sqrt n) ^ 2) |>.add
    (ho.const_mul (2 / (Real.sqrt n) ^ 2))).mono' hm.aestronglyMeasurable
  have ht : ∀ᵐ p : Sample n × ℝ ∂μ.prod ν, p.2 ∈ Icc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  have hd : ∀ᵐ p : Sample n × ℝ ∂μ.prod ν,
      DeathCP.positiveRetention_referenceHazard P hDeath a p.2 = referenceDeathHazard P a p.2 :=
    Measure.quasiMeasurePreserving_snd.ae
      (DeathCP.positiveRetention_referenceHazard_ae_eq P hDeath a)
  filter_upwards [ht, hd] with p hp hpd
  have hz : 0 ≤ DeathCP.positiveRetention_referenceHazard P hDeath a p.2 :=
    DeathCP.positiveRetention_referenceHazard_nonneg P hDeath a p.2
  have hr : 0 ≤ ∑ i : Fin n, riskIndicator i p.2 p.1 := by
    apply Finset.sum_nonneg
    intro i _
    unfold riskIndicator
    split_ifs <;> norm_num
  have he := DeathCP.energyDensity_le c P a 0 p.2 p.1
    (by rw [← referenceDeathHazard_eq P a hp, ← hpd]; exact hz)
  rw [← referenceDeathHazard_eq P a hp, ← hpd] at he
  have hs : (Real.sqrt n * deathCPIntegrand c P a 0 p.2 p.1 -
      subcriticalDeathOracleWeight c P a p.2 / Real.sqrt n) ^ 2 ≤
      2 * (Real.sqrt n) ^ 2 * deathCPIntegrand c P a 0 p.2 p.1 ^ 2 +
        2 / (Real.sqrt n) ^ 2 * subcriticalDeathOracleWeight c P a p.2 ^ 2 := by
    have h (u v : ℝ) : (u - v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
      nlinarith [sq_nonneg (u + v)]
    convert h (Real.sqrt n * deathCPIntegrand c P a 0 p.2 p.1)
      (subcriticalDeathOracleWeight c P a p.2 / Real.sqrt n) using 1 <;>
      simp only [mul_pow, div_pow, div_eq_mul_inv] <;> ring
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hz) hr)]
  calc
    _ ≤ (2 * (Real.sqrt n) ^ 2 * deathCPIntegrand c P a 0 p.2 p.1 ^ 2 +
        2 / (Real.sqrt n) ^ 2 * subcriticalDeathOracleWeight c P a p.2 ^ 2) *
          DeathCP.positiveRetention_referenceHazard P hDeath a p.2 * (∑ i : Fin n, riskIndicator i
            p.2 p.1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hz) hr
    _ ≤ 2 * (Real.sqrt n) ^ 2 * f p.2 +
        (2 / (Real.sqrt n) ^ 2) * (subcriticalDeathOracleWeight c P a p.2 ^ 2 *
          DeathCP.positiveRetention_referenceHazard P hDeath a p.2 * (∑ i : Fin n, riskIndicator i
            p.2 p.1)) := by
      dsimp only [f]
      rw [hpd, referenceDeathHazard_eq P a hp] at he ⊢
      nlinarith [mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ 2 * (Real.sqrt n) ^ 2)]
    _ = _ := rfl


/-- On regular observed samples, the canonical predictable coefficient is
exactly the actual KM-minus-oracle coefficient at every positive time. -/
-- @node: positiveRetention_deathOracleDifferenceIntegrand_observed_eq_ae
lemma positiveRetention_deathOracleDifferenceIntegrand_observed_eq_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ t : ℝ, 0 < t →
      deathOracleDifferenceIntegrand c P a t (observedDeathSample a s) =
        observedDeathOracleDifferenceWeight c P a s t := by
  filter_upwards [DeathCP.sample_arm_death_exit_pos_ae P hDeath a n,
    sample_death_exit_no_tie P hDeath n] with s hpos hties
  intro t ht
  have hkm := pairDeathKMLeft_observedDeathSample_eq_deathKMLeft a s hpos
    (fun i j hij hai hdi haj _ => hties i j hij a hai hdi) t
  simp only [deathOracleDifferenceIntegrand, deathCPIntegrand,
    observedDeathOracleDifferenceWeight, hkm, observedDeathSample_inverseRisk a s ht]
  ring

/-- The canonical predictable energy on observed records equals the actual
full-horizon quadratic density integral; the zero-time discrepancy is null. -/
-- @node: positiveRetention_deathOracleDifferenceIntegrand_observed_energy_eq_ae
lemma positiveRetention_deathOracleDifferenceIntegrand_observed_energy_eq_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n,
      predictableEnergy (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s) =
      ∫ t in Icc (0 : ℝ) 1,
        observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
          (riskSet a s t : ℝ) := by
  filter_upwards [positiveRetention_deathOracleDifferenceIntegrand_observed_eq_ae c P hPoisson
    hDeath hDeathBounds a n] with s hs
  unfold predictableEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ((volume.restrict (Icc (0 : ℝ) 1)).ae_ne (0 : ℝ))] with t ht htne
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 htne.symm
  rw [hs t ht0, referenceDeathHazard_eq P a ht]
  have hr : (∑ i : Fin n, riskIndicator i t (observedDeathSample a s)) =
      (Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t
        (observedDeathSample a s) : ℝ) := by
    simp only [riskIndicator, Causalean.Stat.RecurrentEvent.CountingProcess.riskSet,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hr, observedDeathSample_riskSet a s ht0]

/-- The actual full-horizon difference integral is centered, square integrable,
and obeys the exact predictable-energy isometry at the full study horizon. -/
-- @node: positiveRetention_deathOracleDifferenceIntegrand_full_moments
lemma positiveRetention_deathOracleDifferenceIntegrand_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hOverlap : TreatmentOverlap c P)
    (hRecurBounds : RecurrenceBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n :
      ℕ) :
    Integrable (aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∧
    (∫ x : Sample n, aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) = 0 ∧
    Integrable (fun x : Sample n => (aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 x) ^ 2)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∧
    (∫ x : Sample n, (aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      ∫ x : Sample n, predictableEnergy (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  have hm := deathAggregateIntegral_moments_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (DeathCP.positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a) _
    (deathOracleDifferenceIntegrand_leftPredictable c P a n)
    (positiveRetention_measurable_deathOracleDifferenceIntegrand c P hPoisson hDeath hDeathBounds
      a n)
    1 (by norm_num)
    (positiveRetention_deathOracleDifferenceIntegrand_energy_integrable_prod
      c P hPoisson hDeath hDeathBounds hOverlap hRecurBounds hHorizon a n)
  have heq : aggregateIntegral (DeathCP.positiveRetention_referenceHazard P hDeath a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1 =
      aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 := by
    funext x
    exact DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a _ x
  simpa only [heq, DeathCP.positiveRetention_referenceHazard_predictableEnergy_eq] using hm

/-- The difference energy is a measurable sample statistic, for the
benchmark coefficients. -/
-- @node: positiveRetention_measurable_deathOracleDifferenceEnergy
@[fun_prop]
lemma positiveRetention_measurable_deathOracleDifferenceEnergy
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    Measurable (predictableEnergy (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1) := by
  have hm : Measurable (fun p : Sample n × ℝ =>
      deathOracleDifferenceIntegrand c P a p.2 p.1 ^ 2 *
        DeathCP.positiveRetention_referenceHazard P hDeath a p.2 *
          (∑ i : Fin n, riskIndicator i p.2 p.1)) :=
    (((positiveRetention_measurable_deathOracleDifferenceIntegrand
      c P hPoisson hDeath hDeathBounds a n).comp measurable_swap).pow_const 2 |>.mul
        ((DeathCP.positiveRetention_referenceHazard_measurable P hDeath a).comp
          measurable_snd)).mul
            (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  have ht : Measurable (predictableEnergy
      (DeathCP.positiveRetention_referenceHazard P hDeath a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1) :=
    hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Icc (0 : ℝ) 1)) |>.measurable
  convert ht using 1
  funext x
  exact (DeathCP.positiveRetention_referenceHazard_predictableEnergy_eq P hDeath a _ x).symm

/-- Stopping the synthetic sample at the study horizon preserves the energy
of the predictable difference coefficient almost surely. -/
-- @node: positiveRetention_deathOracleDifferenceEnergy_stopped_eq_ae
lemma positiveRetention_deathOracleDifferenceEnergy_stopped_eq_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    (fun x : Sample n => predictableEnergy (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 (referenceStoppedSyntheticSample x)) =ᵐ[
        Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a)]
      (predictableEnergy (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1) := by
  filter_upwards [DeathCP.positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx
  unfold predictableEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hh : deathOracleDifferenceIntegrand c P a t (referenceStoppedSyntheticSample x) =
      deathOracleDifferenceIntegrand c P a t x :=
    deathOracleDifferenceIntegrand_leftPredictable c P a n t _ _
      (fun i u _ => DeathCP.referenceStoppedSyntheticSample_counts x hx.1 hx.2.1 hx.2.2 i u)
  rw [hh]
  congr 2
  funext i
  exact DeathCP.referenceStoppedSyntheticSample_riskIndicator x hx.1 hx.2.1 hx.2.2 i ht.1 ht.2

/-- Transport of the exact difference energy uses the joint observed sample
law and preserves KM/risk dependence. -/
-- @node: positiveRetention_deathOracleDifferenceEnergy_expected_eq_observed
lemma positiveRetention_deathOracleDifferenceEnergy_expected_eq_observed
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm) (n : ℕ) :
    (∫ x : Sample n, predictableEnergy (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
        (riskSet a s t : ℝ)) ∂sampleLaw P n := by
  let E := predictableEnergy (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a (n := n)) 1
  have hE : Measurable E := positiveRetention_measurable_deathOracleDifferenceEnergy c P hPoisson
    hDeath hDeathBounds a n
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  calc
    _ = ∫ x : Sample n, E (referenceStoppedSyntheticSample x)
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a) :=
      integral_congr_ae (positiveRetention_deathOracleDifferenceEnergy_stopped_eq_ae c P hPoisson
        hDeath hDeathBounds a n).symm
    _ = ∫ x : Sample n, E x ∂(sampleLaw P n).map (observedDeathSample a) := by
      rw [observedDeathSample_map_eq_reference P hDeath
        hRandom hCensor a]
      exact (integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        hE.aestronglyMeasurable).symm
    _ = ∫ s : Fin n → ObsHistory, E (observedDeathSample a s) ∂sampleLaw P n :=
      integral_map hs.aemeasurable hE.aestronglyMeasurable
    _ = _ := integral_congr_ae
      (positiveRetention_deathOracleDifferenceIntegrand_observed_energy_eq_ae c P hPoisson hDeath
        hDeathBounds a n)


/-- The observable root-n death difference energy tends to zero by exact
risk-fraction algebra and the proved benchmark mean-energy convergence. -/
-- @node: positiveRetention_observedDeathOracleDifferenceWeight_expected_energy_tendsto_zero
lemma positiveRetention_observedDeathOracleDifferenceWeight_expected_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1,
        observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
          (riskSet a s t : ℝ)) ∂sampleLaw P n) atTop (nhds 0) := by
  apply (DeathCP.positiveRetention_deathOracleCoefficient_energy_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hRecurBounds hDeathBounds hHorizon a).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [observedDeathOracleDifferenceWeight_energyDensity_eq c P a (by omega) s ht]
  simp only [deathTargetWeight, sub_zero, if_pos ht]

/-- The canonical predictable difference has vanishing second moment, by
its exact isometry and transport of the vanishing observed mean energy. -/
-- @node: positiveRetention_deathOracleDifferenceIntegral_secondMoment_tendsto_zero
lemma positiveRetention_deathOracleDifferenceIntegral_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ x : Sample n,
      (aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) atTop (nhds 0) := by
  apply (positiveRetention_observedDeathOracleDifferenceWeight_expected_energy_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hRecurBounds hDeathBounds hHorizon a).congr'
  exact Eventually.of_forall (fun n =>
    ((positiveRetention_deathOracleDifferenceIntegrand_full_moments
      c P hPoisson hDeath hDeathBounds hOverlap hRecurBounds hHorizon a n).2.2.2.trans
        (positiveRetention_deathOracleDifferenceEnergy_expected_eq_observed
          c P hPoisson hDeath hDeathBounds hRandom hCensor a n)).symm)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
