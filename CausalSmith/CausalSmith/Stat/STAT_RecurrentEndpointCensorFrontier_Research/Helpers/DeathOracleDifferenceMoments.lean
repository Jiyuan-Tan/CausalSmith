module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathOracleDifferenceEnergy

/-! # Predictable moments of the death oracle difference

Roadmap (18)--(19): the normalized KM coefficient minus the endpoint oracle
is left predictable. Its unbounded quadratic density is integrable, so the
actual counting-process isometry and centering identity apply.
-/

@[expose] public section

open MeasureTheory Set
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Canonical predictable coefficient for the root-n death oracle difference. -/
-- @node: deathOracleDifferenceIntegrand
noncomputable def deathOracleDifferenceIntegrand (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (t : ℝ) (x : Sample n) : ℝ :=
  Real.sqrt n * deathCPIntegrand c P a 0 t x -
    subcriticalDeathOracleWeight c P a t / Real.sqrt n

/-- Subtracting the deterministic oracle preserves strict-past predictability. -/
-- @node: deathOracleDifferenceIntegrand_leftPredictable
lemma deathOracleDifferenceIntegrand_leftPredictable
    (c : ClassConstants) (P : SubjectLaw) (a : Arm) (n : ℕ) :
    LeftPredictable (deathOracleDifferenceIntegrand c P a (n := n)) := by
  intro t x y hh
  unfold deathOracleDifferenceIntegrand
  rw [deathCPIntegrand_leftPredictable c P a 0 t x y hh]

/-- The canonical difference coefficient is jointly measurable. -/
-- @node: measurable_deathOracleDifferenceIntegrand
@[fun_prop]
lemma measurable_deathOracleDifferenceIntegrand
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    Measurable (fun p : ℝ × Sample n => deathOracleDifferenceIntegrand c P a p.1 p.2) := by
  unfold deathOracleDifferenceIntegrand
  have hi := deathCPIntegrand_jointMeasurable c P hP a
    (n := n) (h := 0) (by norm_num) (by norm_num)
  have ho : Measurable (fun p : ℝ × Sample n => subcriticalDeathOracleWeight c P a p.1) :=
    (measurable_subcriticalDeathOracleWeight c P hP a).comp measurable_fst
  fun_prop

/-- The canonical difference has integrable product energy, using the KM
energy envelope and the genuine unbounded oracle energy separately. -/
-- @node: deathOracleDifferenceIntegrand_energy_integrable_prod
lemma deathOracleDifferenceIntegrand_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    Integrable (fun p : Sample n × ℝ =>
      deathOracleDifferenceIntegrand c P a p.2 p.1 ^ 2 *
        referenceDeathHazard P a p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1))
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
    simpa only [sub_zero, f, ν, IntegrableOn] using DeathCP.deathTargetWeight_sq_hazard_integrableOn
      c P hP a (h := 0) (by norm_num) (by norm_num)
  have ho := subcriticalDeathOracle_energy_integrable_prod c P hP hk a n
  have hm : Measurable (fun p : Sample n × ℝ =>
      deathOracleDifferenceIntegrand c P a p.2 p.1 ^ 2 *
        referenceDeathHazard P a p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1)) :=
    (((measurable_deathOracleDifferenceIntegrand c P hP a n).comp
      measurable_swap).pow_const 2 |>.mul
        ((measurable_referenceDeathHazard hP a).comp measurable_snd)).mul
          (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  apply ((hf.comp_snd (μ := μ)).const_mul (2 * (Real.sqrt n) ^ 2) |>.add
    (ho.const_mul (2 / (Real.sqrt n) ^ 2))).mono' hm.aestronglyMeasurable
  have ht : ∀ᵐ p : Sample n × ℝ ∂μ.prod ν, p.2 ∈ Icc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with p hp
  have hz : 0 ≤ referenceDeathHazard P a p.2 := referenceDeathHazard_nonneg hP a p.2
  have hr : 0 ≤ ∑ i : Fin n, riskIndicator i p.2 p.1 := by
    apply Finset.sum_nonneg
    intro i _
    unfold riskIndicator
    split_ifs <;> norm_num
  have he := DeathCP.energyDensity_le c P a 0 p.2 p.1
    (by rw [← referenceDeathHazard_eq P a hp]; exact hz)
  rw [← referenceDeathHazard_eq P a hp] at he
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
          referenceDeathHazard P a p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hz) hr
    _ ≤ 2 * (Real.sqrt n) ^ 2 * f p.2 +
        (2 / (Real.sqrt n) ^ 2) * (subcriticalDeathOracleWeight c P a p.2 ^ 2 *
          referenceDeathHazard P a p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1)) := by
      dsimp only [f]
      rw [← referenceDeathHazard_eq P a hp]
      nlinarith [mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ 2 * (Real.sqrt n) ^ 2)]
    _ = _ := rfl

/-- On regular observed samples, the canonical predictable coefficient is
exactly the actual KM-minus-oracle coefficient at every positive time. -/
-- @node: deathOracleDifferenceIntegrand_observed_eq_ae
lemma deathOracleDifferenceIntegrand_observed_eq_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ t : ℝ, 0 < t →
      deathOracleDifferenceIntegrand c P a t (observedDeathSample a s) =
        observedDeathOracleDifferenceWeight c P a s t := by
  filter_upwards [DeathCP.sample_arm_death_exit_pos_ae P hP.deathHazard a n,
    sample_death_exit_no_tie P hP.deathHazard n] with s hpos hties
  intro t ht
  have hkm := pairDeathKMLeft_observedDeathSample_eq_deathKMLeft a s hpos
    (fun i j hij hai hdi haj _ => hties i j hij a hai hdi) t
  simp only [deathOracleDifferenceIntegrand, deathCPIntegrand,
    observedDeathOracleDifferenceWeight, hkm, observedDeathSample_inverseRisk a s ht]
  ring

/-- The canonical predictable energy on observed records equals the actual
full-horizon quadratic density integral; the zero-time discrepancy is null. -/
-- @node: deathOracleDifferenceIntegrand_observed_energy_eq_ae
lemma deathOracleDifferenceIntegrand_observed_energy_eq_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n,
      predictableEnergy (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s) =
      ∫ t in Icc (0 : ℝ) 1,
        observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
          (riskSet a s t : ℝ) := by
  filter_upwards [deathOracleDifferenceIntegrand_observed_eq_ae c P hP a n] with s hs
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
and obeys the exact predictable-energy isometry even at the singular endpoint. -/
-- @node: deathOracleDifferenceIntegrand_full_moments
lemma deathOracleDifferenceIntegrand_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
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
  exact deathAggregateIntegral_moments_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a) (referenceDeathLaw_hasCensorHazard hP a) _
    (deathOracleDifferenceIntegrand_leftPredictable c P a n)
    (measurable_deathOracleDifferenceIntegrand c P hP a n) 1 (by norm_num)
    (deathOracleDifferenceIntegrand_energy_integrable_prod c P hP hk a n)

/-- The difference energy is a measurable sample statistic, including for
unbounded endpoint coefficients. -/
-- @node: measurable_deathOracleDifferenceEnergy
@[fun_prop]
lemma measurable_deathOracleDifferenceEnergy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    Measurable (predictableEnergy (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1) := by
  have hm : Measurable (fun p : Sample n × ℝ =>
      deathOracleDifferenceIntegrand c P a p.2 p.1 ^ 2 *
        referenceDeathHazard P a p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1)) :=
    (((measurable_deathOracleDifferenceIntegrand c P hP a n).comp
      measurable_swap).pow_const 2 |>.mul
        ((measurable_referenceDeathHazard hP a).comp measurable_snd)).mul
          (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Stopping the synthetic sample at the study horizon preserves the energy
of the predictable difference coefficient almost surely. -/
-- @node: deathOracleDifferenceEnergy_stopped_eq_ae
lemma deathOracleDifferenceEnergy_stopped_eq_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (fun x : Sample n => predictableEnergy (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 (referenceStoppedSyntheticSample x)) =ᵐ[
        Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a)]
      (predictableEnergy (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1) := by
  filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
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
-- @node: deathOracleDifferenceEnergy_expected_eq_observed
lemma deathOracleDifferenceEnergy_expected_eq_observed
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (∫ x : Sample n, predictableEnergy (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
        (riskSet a s t : ℝ)) ∂sampleLaw P n := by
  let E := predictableEnergy (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a (n := n)) 1
  have hE : Measurable E := measurable_deathOracleDifferenceEnergy c P hP a n
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  calc
    _ = ∫ x : Sample n, E (referenceStoppedSyntheticSample x)
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a) :=
      integral_congr_ae (deathOracleDifferenceEnergy_stopped_eq_ae c P hP a n).symm
    _ = ∫ x : Sample n, E x ∂(sampleLaw P n).map (observedDeathSample a) := by
      rw [observedDeathSample_map_eq_reference P hP.deathHazard
        hP.randomAssignment hP.independentCensoring a]
      exact (integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        hE.aestronglyMeasurable).symm
    _ = ∫ s : Fin n → ObsHistory, E (observedDeathSample a s) ∂sampleLaw P n :=
      integral_map hs.aemeasurable hE.aestronglyMeasurable
    _ = _ := integral_congr_ae
      (deathOracleDifferenceIntegrand_observed_energy_eq_ae c P hP a n)

/-- The full-horizon predictable death difference integral has vanishing
second moment, obtained from its exact isometry and observed coefficient energy. -/
-- @node: deathOracleDifferenceIntegral_secondMoment_tendsto_zero
lemma deathOracleDifferenceIntegral_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Filter.Tendsto (fun n : ℕ => ∫ x : Sample n,
      (aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) Filter.atTop (nhds 0) := by
  apply (observedDeathOracleDifferenceWeight_expected_energy_tendsto_zero c P hP hk a).congr'
  apply Filter.Eventually.of_forall
  intro n
  exact ((deathOracleDifferenceIntegrand_full_moments c P hP hk a n).2.2.2.trans
    (deathOracleDifferenceEnergy_expected_eq_observed c P hP a n)).symm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
