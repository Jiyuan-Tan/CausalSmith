module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionHazardDensity

/-!
# Death isometry in the positive-retention benchmark

Use the canonical counting-process isometry with the measurable hazard
representative, then transport the square moment to observed histories.
This establishes roadmap (6) and (9) under the proposition's assumptions.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

open Causalean.Stat.RecurrentEvent.CountingProcess

/-- Finite canonical quadratic energy is invariant under a null-set change
of the hazard on the integration window. -/
-- @node: positiveRetention_referenceHazard_quadraticEnergyFinite
lemma positiveRetention_referenceHazard_quadraticEnergyFinite
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} :
    QuadraticEnergyFinite (armDeathFailureLaw P a) (referenceDeathLaw P a)
      (positiveRetention_referenceHazard P hDeath a)
      (deathCPIntegrand c P a 0 (n := n)) 1 := by
  have h := positiveRetention_deathCPIntegrand_zero_quadraticEnergyFinite c P
    hPoisson hDeath hRecurBounds hDeathBounds a (n := n)
  unfold QuadraticEnergyFinite at h ⊢
  convert h using 1
  apply lintegral_congr
  intro x
  apply lintegral_congr_ae
  filter_upwards [positiveRetention_referenceHazard_ae_eq P hDeath a] with t ht
  rw [ht]

/-- The canonical compensated integral is measurable for a measurable
hazard and jointly measurable integrand. -/
-- @node: positiveRetention_measurable_aggregateIntegral
@[fun_prop] lemma positiveRetention_measurable_aggregateIntegral {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ) (u : ℝ)
    (hd : Measurable hazard) (hH : Measurable (fun p : ℝ × Sample n => H p.1 p.2)) :
    Measurable (aggregateIntegral hazard H u) := by
  classical
  have hcomp (i : Fin n) : Measurable (fun x : Sample n =>
      ∫ t in Icc 0 u, H t x * hazard t * riskIndicator i t x ∂volume) := by
    have hrisk : Measurable (fun p : Sample n × ℝ => riskIndicator i p.2 p.1) := by
      unfold riskIndicator
      apply Measurable.ite
      · exact (measurableSet_le measurable_const measurable_snd).inter
          ((measurableSet_le measurable_snd (by fun_prop)).inter
            (measurableSet_le measurable_snd (by fun_prop)))
      · exact measurable_const
      · exact measurable_const
    have he : Measurable (fun p : Sample n × ℝ =>
        H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1) :=
      ((hH.comp measurable_swap).mul (hd.comp measurable_snd)).mul hrisk
    exact he.stronglyMeasurable.integral_prod_right'.measurable
  unfold aggregateIntegral subjectIntegral
  apply Finset.measurable_fun_sum
  intro i _
  have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
  have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
  exact (hH.comp (hc.prodMk measurable_id)).ite
    ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
    measurable_const |>.sub (hcomp i)

/-- The benchmark canonical death integral has the expected energy isometry. -/
-- @node: positiveRetention_deathCPIntegrand_zero_aggregate_isometry
lemma positiveRetention_deathCPIntegrand_zero_aggregate_isometry
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} :
    (∫ x : Sample n,
      aggregateIntegral (positiveRetention_referenceHazard P hDeath a)
        (deathCPIntegrand c P a 0) 1 x ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ x : Sample n, predictableEnergy (referenceDeathHazard P a)
      (deathCPIntegrand c P a 0) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  have hE : Integrable (predictableEnergy (positiveRetention_referenceHazard P hDeath a)
      (deathCPIntegrand c P a 0 (n := n)) 1)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    convert positiveRetention_deathCPIntegrand_zero_energy_integrable c P hPoisson
      hDeath hRecurBounds hDeathBounds a (n := n) using 1
    ext x
    exact positiveRetention_referenceHazard_predictableEnergy_eq P hDeath a _ x
  have h := aggregate_integral_isometry (armDeathFailureLaw P a)
    (referenceDeathLaw P a) (positiveRetention_referenceHazard P hDeath a)
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a)
    (deathCPIntegrand c P a 0) (deathCPIntegrand_leftPredictable c P a 0)
    (positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson hDeath
      hDeathBounds a (by norm_num) (by norm_num)) 1 (by norm_num)
    (positiveRetention_referenceHazard_quadraticEnergyFinite c P hPoisson hDeath
      hRecurBounds hDeathBounds a) hE
  simpa only [positiveRetention_referenceHazard_predictableEnergy_eq] using h

/-- The benchmark observed death error has exactly the independent reference
law's expected predictable energy. -/
-- @node: positiveRetention_deathError_zero_secondMoment_eq_predictableEnergy
lemma positiveRetention_deathError_zero_secondMoment_eq_predictableEnergy
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    (∫ s : Fin n → ObsHistory, deathError c P a s 0 ^ 2 ∂sampleLaw P n) =
    ∫ x : Sample n, predictableEnergy (referenceDeathHazard P a)
      (deathCPIntegrand c P a 0) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let d := positiveRetention_referenceHazard P hDeath a
  let H := deathCPIntegrand c P a 0 (n := n)
  let J := aggregateIntegral d H 1
  have hJ : Measurable J := positiveRetention_measurable_aggregateIntegral d H 1
    (positiveRetention_referenceHazard_measurable P hDeath a)
    (positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson hDeath
      hDeathBounds a (by norm_num) (by norm_num))
  have hobs : (fun s : Fin n → ObsHistory => J (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      (fun s => deathError c P a s 0) := by
    simpa only [J, d, H, positiveRetention_referenceHazard_aggregateIntegral_eq,
      sub_zero] using positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError_ae
        c P hPoisson hDeath hDeathBounds a n (h := 0) (by norm_num) (by norm_num)
  have hobsMeas : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  calc
    _ = ∫ s : Fin n → ObsHistory, J (observedDeathSample a s) ^ 2 ∂sampleLaw P n := by
      apply integral_congr_ae
      filter_upwards [hobs] with s hs
      rw [hs]
    _ = ∫ y : Sample n, J y ^ 2 ∂(sampleLaw P n).map (observedDeathSample a) :=
      (integral_map hobsMeas.aemeasurable (hJ.pow_const 2).aestronglyMeasurable).symm
    _ = ∫ y : Sample n, J y ^ 2 ∂μ.map referenceStoppedSyntheticSample := by
      rw [observedDeathSample_map_eq_reference P hDeath hRandom hCensor a]
    _ = ∫ x : Sample n, J (referenceStoppedSyntheticSample x) ^ 2 ∂μ :=
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable
    _ = ∫ x : Sample n, J x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx
      exact congrArg (fun z : ℝ => z ^ 2)
        (aggregateIntegral_referenceStoppedSyntheticSample d H
          (deathCPIntegrand_leftPredictable c P a 0) x hx.1 hx.2.1 hx.2.2
          (by norm_num) le_rfl)
    _ = _ := positiveRetention_deathCPIntegrand_zero_aggregate_isometry c P
      hPoisson hDeath hRecurBounds hDeathBounds a

/-- The ordinary death martingale error has parametric second moment under
positive horizon retention. -/
-- @node: positiveRetention_deathError_zero_secondMoment_le_inv_sampleSize
lemma positiveRetention_deathError_zero_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, deathError c P a s 0 ^ 2 ∂sampleLaw P n) ≤
      (2 * (c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  rw [positiveRetention_deathError_zero_secondMoment_eq_predictableEnergy c P
    hRandom hPoisson hDeath hCensor hRecurBounds hDeathBounds a n]
  exact positiveRetention_reference_deathEnergy_zero_le_inv_sampleSize c P hRandom
    hAssignment hOverlap hPoisson hDeath hCensor hRecurBounds hDeathBounds hHorizon a hn

/-- The observed benchmark death error is square integrable; this follows
from subject event and compensator moments, independently of the Bochner isometry. -/
-- @node: positiveRetention_deathError_zero_sq_integrable
lemma positiveRetention_deathError_zero_sq_integrable
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    Integrable (fun s : Fin n → ObsHistory => deathError c P a s 0 ^ 2)
      (sampleLaw P n) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let d := positiveRetention_referenceHazard P hDeath a
  let H := deathCPIntegrand c P a 0 (n := n)
  let J := aggregateIntegral d H 1
  have hH := positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson hDeath
    hDeathBounds a (n := n) (h := 0) (by norm_num) (by norm_num)
  have hJ : Measurable J := positiveRetention_measurable_aggregateIntegral d H 1
    (positiveRetention_referenceHazard_measurable P hDeath a) hH
  have hE : Integrable (predictableEnergy d H 1) μ := by
    convert positiveRetention_deathCPIntegrand_zero_energy_integrable c P hPoisson
      hDeath hRecurBounds hDeathBounds a (n := n) using 1
    ext x
    exact positiveRetention_referenceHazard_predictableEnergy_eq P hDeath a H x
  have hi : Integrable (fun x : Sample n => J x ^ 2) μ :=
    deathAggregateIntegral_sq_integrable _ _ d
      (armDeathFailureLaw_nonnegativeTimeLaw P a)
      (positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a) H
      (deathCPIntegrand_leftPredictable c P a 0) hH 1 (by norm_num)
      (positiveRetention_referenceHazard_quadraticEnergyFinite c P hPoisson hDeath
        hRecurBounds hDeathBounds a) hE
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hm : Integrable (fun x : Sample n => J x ^ 2)
      ((sampleLaw P n).map (observedDeathSample a)) := by
    rw [observedDeathSample_map_eq_reference P hDeath hRandom hCensor a]
    apply (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2
    apply hi.congr
    filter_upwards [positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx
    exact congrArg (fun z : ℝ => z ^ 2)
      (aggregateIntegral_referenceStoppedSyntheticSample d H
        (deathCPIntegrand_leftPredictable c P a 0) x hx.1 hx.2.1 hx.2.2
        (by norm_num) le_rfl).symm
  have ht := (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable hs.aemeasurable).1 hm
  apply ht.congr
  filter_upwards [positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError_ae
    c P hPoisson hDeath hDeathBounds a n (h := 0) (by norm_num) (by norm_num)] with s hs
  change J (observedDeathSample a s) ^ 2 = _
  dsimp [J, d, H]
  rw [positiveRetention_referenceHazard_aggregateIntegral_eq]
  simpa only [sub_zero] using congrArg (fun z : ℝ => z ^ 2) hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
