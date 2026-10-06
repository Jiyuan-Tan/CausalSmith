module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathTransport

/-!
# Reference-law death energy for the positive-retention benchmark

Transfer the observed predictable-energy bound to the independent reference
sample. Local hazard integrability suffices for measurable energy; no endpoint
smoothness or globally measurable hazard is required. This implements the energy
transport needed by roadmap (6) and (9).
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- Reference samples have nonnegative coordinates and follow-up at most one. -/
-- @node: positiveRetention_referenceSample_regular_ae
lemma positiveRetention_referenceSample_regular_ae (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) (n : ℕ) :
    ∀ᵐ x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a),
      (∀ i, 0 ≤ (x i).1) ∧ (∀ i, (x i).1 ≤ 1) ∧ (∀ i, 0 ≤ (x i).2) := by
  let failureLaw := armDeathFailureLaw P a
  let deathLaw := referenceDeathLaw P a
  letI : IsProbabilityMeasure failureLaw :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure deathLaw := inferInstance
  have hf0 : ∀ᵐ f ∂failureLaw, 0 ≤ f := by
    exact (mem_ae_iff_prob_eq_one measurableSet_Ici).2
      (armDeathFailureLaw_nonnegativeTimeLaw P a).2
  have hf1 : ∀ᵐ f ∂failureLaw, f ≤ 1 := by
    unfold failureLaw armDeathFailureLaw
    apply (ae_map_iff (measurable_armDeathFailureTime a).aemeasurable
      (measurableSet_le measurable_id measurable_const)).2
    exact Filter.Eventually.of_forall (armDeathFailureTime_le_one a)
  have hd0 : ∀ᵐ d ∂deathLaw, 0 ≤ d := by
    exact (mem_ae_iff_prob_eq_one measurableSet_Ici).2
      (referenceDeathLaw_nonnegativeTimeLaw hDeath a).2
  have hpair : ∀ᵐ q ∂failureLaw.prod deathLaw,
      0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_const).inter
          (measurableSet_le measurable_const measurable_snd)))).2
    filter_upwards [hf0, hf1] with f hf0 hf1
    filter_upwards [hd0] with d hd0
    exact ⟨hf0, hf1, hd0⟩
  have hall : ∀ᵐ x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      failureLaw deathLaw, ∀ i, 0 ≤ (x i).1 ∧ (x i).1 ≤ 1 ∧ 0 ≤ (x i).2 := by
    rw [Filter.eventually_all]
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod deathLaw) (i := i)) hpair
  filter_upwards [hall] with x hx
  exact ⟨fun i => (hx i).1, fun i => (hx i).2.1, fun i => (hx i).2.2⟩

/-- Stopping a regular reference sample preserves predictable quadratic energy. -/
-- @node: predictableEnergy_referenceStoppedSyntheticSample
lemma predictableEnergy_referenceStoppedSyntheticSample {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (hPred : Causalean.Stat.RecurrentEvent.CountingProcess.LeftPredictable H)
    (x : Sample n) (hfirst0 : ∀ i, 0 ≤ (x i).1)
    (hfirst1 : ∀ i, (x i).1 ≤ 1) (hsecond0 : ∀ i, 0 ≤ (x i).2)
    {u : ℝ} (hu1 : u ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy hazard H u
      (referenceStoppedSyntheticSample x) =
    Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy hazard H u x := by
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [hPred t _ _ (fun i v _ =>
    referenceStoppedSyntheticSample_counts x hfirst0 hfirst1 hsecond0 i v)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact referenceStoppedSyntheticSample_riskIndicator x hfirst0 hfirst1
    hsecond0 i ht.1 (ht.2.trans hu1)

/-- Local integrability of the paper hazard gives measurable ordinary death energy. -/
-- @node: positiveRetention_measurable_deathCPIntegrand_zero_predictableEnergy
lemma positiveRetention_measurable_deathCPIntegrand_zero_predictableEnergy
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (a : Arm) {n : ℕ} :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (referenceDeathHazard P a) (deathCPIntegrand c P a 0 (n := n)) 1) := by
  classical
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  have hd : Integrable (P.hazard a) ν :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hDeath.1 a)
  let d := hd.aestronglyMeasurable.mk (P.hazard a)
  have hm : Measurable d := hd.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  let e : Sample n × ℝ → ℝ := fun p =>
    (deathCPIntegrand c P a 0 p.2 p.1) ^ 2 * d p.2 *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1)
  have hrisk (i : Fin n) : Measurable (fun p : Sample n × ℝ =>
      Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
    apply Measurable.ite
    · exact (measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd (by fun_prop)).inter
          (measurableSet_le measurable_snd (by fun_prop)))
    · exact measurable_const
    · exact measurable_const
  have he : Measurable e := by
    exact (((positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson
      hDeath hDeathBounds a (by norm_num) (by norm_num)).comp
        measurable_swap).pow_const 2).mul (hm.comp measurable_snd) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have hint := he.stronglyMeasurable.integral_prod_right' (ν := ν)
  convert hint.measurable using 1
  ext x
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    hd.aestronglyMeasurable.ae_eq_mk] with t ht htd
  dsimp [e, d]
  rw [referenceDeathHazard_eq P a ht, htd]

/-- The ordinary reference energy is integrable under the benchmark assumptions. -/
-- @node: positiveRetention_deathCPIntegrand_zero_energy_integrable
lemma positiveRetention_deathCPIntegrand_zero_energy_integrable
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} :
    Integrable
      (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0 (n := n)) 1)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  let f : ℝ → ℝ := fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t
  have hf : Integrable f ν :=
    positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn
      c P hPoisson hDeath hRecurBounds hDeathBounds a
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  apply Integrable.of_bound
    (positiveRetention_measurable_deathCPIntegrand_zero_predictableEnergy
      c P hPoisson hDeath hDeathBounds a).aestronglyMeasurable (∫ t, f t ∂ν)
  filter_upwards [] with x
  let e : ℝ → ℝ := fun t =>
    deathCPIntegrand c P a 0 t x ^ 2 * referenceDeathHazard P a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
  have he0 : ∀ᵐ t ∂ν, 0 ≤ e t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp [e]
    rw [referenceDeathHazard_eq P a ht]
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (c.dMin_pos.le.trans (hDeathBounds a t ht).1))
      (Finset.sum_nonneg (fun i _ => by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num))
  change ‖∫ t, e t ∂ν‖ ≤ ∫ t, f t ∂ν
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg_of_ae he0)]
  apply integral_mono_of_nonneg he0 hf
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  dsimp [e, f]
  rw [referenceDeathHazard_eq P a ht]
  exact energyDensity_le c P a 0 t x
    (c.dMin_pos.le.trans (hDeathBounds a t ht).1)

/-- The observed and reference expected death energies are exactly equal. -/
-- @node: positiveRetention_deathEnergy_zero_reference_eq_observed
lemma positiveRetention_deathEnergy_zero_reference_eq_observed
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hDeathBounds : DeathBounds c P)
    (a : Arm) (n : ℕ) :
    (∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ s : Fin n → ObsHistory,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0) 1
        (observedDeathSample a s) ∂sampleLaw P n := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let E : Sample n → ℝ :=
    Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (referenceDeathHazard P a) (deathCPIntegrand c P a 0) 1
  have hE : Measurable E :=
    positiveRetention_measurable_deathCPIntegrand_zero_predictableEnergy
      c P hPoisson hDeath hDeathBounds a
  have hobsMeas : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  symm
  calc
    _ = ∫ y : Sample n, E y ∂(sampleLaw P n).map (observedDeathSample a) := by
      symm
      exact integral_map hobsMeas.aemeasurable hE.aestronglyMeasurable
    _ = ∫ y : Sample n, E y ∂μ.map referenceStoppedSyntheticSample := by
      rw [observedDeathSample_map_eq_reference P hDeath hRandom hCensor a]
    _ = ∫ x : Sample n, E (referenceStoppedSyntheticSample x) ∂μ :=
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        hE.aestronglyMeasurable
    _ = ∫ x : Sample n, E x ∂μ := by
      apply integral_congr_ae
      filter_upwards [positiveRetention_referenceSample_regular_ae P hDeath a n]
        with x hx
      exact predictableEnergy_referenceStoppedSyntheticSample
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0)
        (deathCPIntegrand_leftPredictable c P a 0) x hx.1 hx.2.1 hx.2.2 le_rfl

/-- The reference predictable death energy has the benchmark parametric rate. -/
-- @node: positiveRetention_reference_deathEnergy_zero_le_inv_sampleSize
lemma positiveRetention_reference_deathEnergy_zero_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      (2 * (c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  rw [positiveRetention_deathEnergy_zero_reference_eq_observed c P hRandom
    hPoisson hDeath hCensor hDeathBounds a n]
  exact positiveRetention_observed_deathEnergy_zero_le_inv_sampleSize c P hRandom
    hAssignment hOverlap hDeath hCensor hRecurBounds hDeathBounds hHorizon a hn

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
