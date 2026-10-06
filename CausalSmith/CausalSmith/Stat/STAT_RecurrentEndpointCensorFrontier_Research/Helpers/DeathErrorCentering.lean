module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability

/-!
# Centering of observed compensated death errors

Roadmap (2) and (6): finite quadratic energy makes each event payoff
integrable. The predictable compensator identity centers the aggregate,
and the stopped reference product law transports its mean to observed data.
No boundedness or independence of the integrand and risk set is assumed.
-/

public section

open MeasureTheory Set
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A predictable aggregate with finite quadratic energy is integrable and
centered, including when the predictable integrand is unbounded. -/
-- @node: deathAggregateIntegral_integrable_centered
lemma deathAggregateIntegral_integrable_centered {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    (hEnergy : Integrable (predictableEnergy hazard H u)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw)) :
    Integrable (aggregateIntegral hazard H u)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) ∧
    (∫ x, aggregateIntegral hazard H u x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) = 0 := by
  classical
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw
  letI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  letI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  letI : IsProbabilityMeasure μ := by unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw; infer_instance
  have hi (i : Fin n) : Integrable (subjectIntegral hazard H i u) μ ∧
      (∫ x, subjectIntegral hazard H i u x ∂μ) = 0 := by
    let E := fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0
    have hm : Measurable E := by
      have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
      have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
      exact (hMeasurable.comp (hc.prodMk measurable_id)).ite
        ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
        measurable_const
    have he : Integrable E μ :=
      ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
        (subject_event_payoff_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable i u hu hQuadratic hEnergy)).integrable
            (by norm_num)
    have ha := predictable_censor_compensator_integrable failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable i u hu he
    refine ⟨he.sub ha, ?_⟩
    change (∫ x, E x - _ ∂μ) = 0
    rw [integral_sub he ha]
    exact sub_eq_zero.mpr (predictable_censor_compensator failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable i u hu he ha)
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => (hi i).1), ?_⟩
  change (∫ x, ∑ i : Fin n, subjectIntegral hazard H i u x ∂μ) = 0
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).1)]
  exact Finset.sum_eq_zero (fun i _ => (hi i).2)

/-- Product integrability of the quadratic density supplies both honest
extended-energy finiteness and integrability of the pathwise energy.
This Fubini adapter does not require a bounded endpoint weight. -/
-- @node: deathAggregateIntegral_energy_conditions_of_integrable_prod
lemma deathAggregateIntegral_energy_conditions_of_integrable_prod {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (u : ℝ)
    (hprod : Integrable (fun p : Sample n × ℝ =>
      H p.2 p.1 ^ 2 * hazard p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1))
      ((Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw).prod
        (volume.restrict (Icc 0 u)))) :
    QuadraticEnergyFinite failureLaw censorLaw hazard H u ∧
    Integrable (predictableEnergy hazard H u)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) := by
  letI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  letI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  letI : IsProbabilityMeasure
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  refine ⟨?_, hprod.integral_prod_left⟩
  unfold QuadraticEnergyFinite
  rw [← lintegral_prod _ hprod.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hprod.2).ne

/-- An integrable product quadratic density gives all actual aggregate
moments: integrability, centering, an integrable square, and the exact
predictable-energy second moment. -/
-- @node: deathAggregateIntegral_moments_of_integrable_prod
lemma deathAggregateIntegral_moments_of_integrable_prod {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (u : ℝ) (hu : 0 ≤ u)
    (hprod : Integrable (fun p : Sample n × ℝ =>
      H p.2 p.1 ^ 2 * hazard p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1))
      ((Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw).prod
        (volume.restrict (Icc 0 u)))) :
    Integrable (aggregateIntegral hazard H u)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) ∧
    (∫ x, aggregateIntegral hazard H u x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) = 0 ∧
    Integrable (fun x => aggregateIntegral hazard H u x ^ 2)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) ∧
    (∫ x, aggregateIntegral hazard H u x ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) =
      ∫ x, predictableEnergy hazard H u x
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw := by
  obtain ⟨hq, he⟩ := deathAggregateIntegral_energy_conditions_of_integrable_prod
    failureLaw censorLaw hazard hFailure hHazard H u hprod
  obtain ⟨hi, hz⟩ := deathAggregateIntegral_integrable_centered
    failureLaw censorLaw hazard hFailure hHazard H hPredictable hMeasurable u hu hq he
  exact ⟨hi, hz,
    deathAggregateIntegral_sq_integrable failureLaw censorLaw hazard hFailure hHazard
      H hPredictable hMeasurable u hu hq he,
    aggregate_integral_isometry failureLaw censorLaw hazard hFailure hHazard
      H hPredictable hMeasurable u hu hq he⟩

/-- The canonical reference death integral has zero expectation, derived
from the actual predictable compensator rather than its second moment. -/
-- @node: deathCPIntegrand_aggregate_integrable_centered
lemma deathCPIntegrand_aggregate_integrable_centered
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (aggregateIntegral (referenceDeathHazard P a)
      (deathCPIntegrand c P a h) (1 - h))
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∧
    (∫ x : Sample n, aggregateIntegral (referenceDeathHazard P a)
      (deathCPIntegrand c P a h) (1 - h) x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) = 0 := by
  exact deathAggregateIntegral_integrable_centered _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (referenceDeathLaw_hasCensorHazard hP a) _
    (deathCPIntegrand_leftPredictable c P a h)
    (deathCPIntegrand_jointMeasurable c P hP a hh hh1) _ (by linarith)
    (DeathCP.deathCPIntegrand_quadraticEnergyFinite c P hP a hh hh1)
    (DeathCP.deathCPIntegrand_energy_integrable c P hP a hh hh1)

/-- The observed death error is integrable and exactly centered under the
actual iid sample law, including the ordinary full-horizon estimator. -/
-- @node: deathError_integrable_centered
lemma deathError_integrable_centered (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory => deathError c P a s h) (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory, deathError c P a s h ∂sampleLaw P n) = 0 := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ := aggregateIntegral (referenceDeathHazard P a)
    (deathCPIntegrand c P a h) (1 - h)
  have hJ : Measurable J :=
    DeathCP.measurable_deathCPIntegrand_aggregateIntegral c P hP a hh hh1
  have hj := deathCPIntegrand_aggregate_integrable_centered c P hP a n hh hh1
  have hreg : (fun x => J (referenceStoppedSyntheticSample x)) =ᵐ[μ] J := by
    filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
    exact DeathCP.aggregateIntegral_referenceStoppedSyntheticSample _ _
      (deathCPIntegrand_leftPredictable c P a h) x hx.1 hx.2.1 hx.2.2
      (by linarith) (by linarith)
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hmap : (sampleLaw P n).map (observedDeathSample a) =
      μ.map referenceStoppedSyntheticSample :=
    observedDeathSample_map_eq_reference P hP.deathHazard
      hP.randomAssignment hP.independentCensoring a
  have hobs : (fun s => J (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      (fun s => deathError c P a s h) :=
    DeathCP.aggregateIntegral_observedDeathSample_eq_deathError_ae c P hP a n hh hh1
  have hmi : Integrable J ((sampleLaw P n).map (observedDeathSample a)) := by
    rw [hmap]
    exact (integrable_map_measure hJ.aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2 (hj.1.congr hreg.symm)
  refine ⟨((integrable_map_measure hJ.aestronglyMeasurable hs.aemeasurable).1 hmi).congr hobs, ?_⟩
  calc
    _ = ∫ s, J (observedDeathSample a s) ∂sampleLaw P n := integral_congr_ae hobs.symm
    _ = ∫ x, J x ∂(sampleLaw P n).map (observedDeathSample a) :=
      (integral_map hs.aemeasurable hJ.aestronglyMeasurable).symm
    _ = ∫ x, J x ∂μ.map referenceStoppedSyntheticSample := by rw [hmap]
    _ = ∫ x, J (referenceStoppedSyntheticSample x) ∂μ :=
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable hJ.aestronglyMeasurable
    _ = ∫ x, J x ∂μ := integral_congr_ae hreg
    _ = 0 := hj.2

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
