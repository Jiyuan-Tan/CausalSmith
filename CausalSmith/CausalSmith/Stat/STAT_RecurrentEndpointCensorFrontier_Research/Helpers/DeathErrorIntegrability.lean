module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk

/-! # Square integrability of the observed death score

Finite subject event and compensator square moments give an integrable square
for the aggregate integral. The verified product-law transport transfers this
regularity to the actual observed death error.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Stat.RecurrentEvent.CountingProcess

/-- Subject event and hazard moments imply square integrability of their
finite aggregate, without inferring integrability from a Bochner isometry. -/
-- @node: deathAggregateIntegral_sq_integrable
lemma deathAggregateIntegral_sq_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    (hEnergy : Integrable (predictableEnergy hazard H u)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw)) :
    Integrable (fun x : Sample n => aggregateIntegral hazard H u x ^ 2)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw) := by
  classical
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n failureLaw censorLaw
  let J : Fin n → Sample n → ℝ := fun i x => subjectIntegral hazard H i u x
  have hSquare (i : Fin n) : AEStronglyMeasurable (J i) μ ∧
      Integrable (fun x => J i x ^ 2) μ := by
    let E : Sample n → ℝ := fun x =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0
    let A : Sample n → ℝ := fun x =>
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume
    have hEmeas : Measurable E := by
      have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
      have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
      exact (hMeasurable.comp (hc.prodMk measurable_id)).ite
        ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
        measurable_const
    have hAmeas : Measurable A := by
      let F : Sample n × ℝ → ℝ := fun p =>
        H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1
      have hrisk : Measurable (fun p : Sample n × ℝ =>
          riskIndicator i p.2 p.1) := by
        unfold riskIndicator
        have hf : Measurable (fun p : Sample n × ℝ => (p.1 i).1) := by fun_prop
        have hc : Measurable (fun p : Sample n × ℝ => (p.1 i).2) := by fun_prop
        have hs : MeasurableSet {p : Sample n × ℝ |
            0 ≤ p.2 ∧ p.2 ≤ (p.1 i).1 ∧ p.2 ≤ (p.1 i).2} := by
          simpa only [Set.ofPred_and, Set.inter_assoc, id_eq] using
            (((show MeasurableSet {p : Sample n × ℝ | (0 : ℝ) ≤ p.2} from
              measurableSet_le measurable_const measurable_snd).inter
              (measurableSet_le measurable_snd hf)).inter
              (measurableSet_le measurable_snd hc))
        exact measurable_const.ite hs measurable_const
      have hF : Measurable F :=
        ((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).mul
          (hHazard.2.1.comp measurable_snd)).mul hrisk
      exact hF.stronglyMeasurable.integral_prod_right'.measurable
    have hELp : MemLp E 2 μ :=
      (memLp_two_iff_integrable_sq hEmeas.aestronglyMeasurable).2
        (subject_event_payoff_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable i u hQuadratic)
    have hALp : MemLp A 2 μ :=
      (memLp_two_iff_integrable_sq hAmeas.aestronglyMeasurable).2
        (subject_hazard_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hMeasurable i u hQuadratic)
    constructor
    · change AEStronglyMeasurable (E - A) μ
      exact (hEmeas.sub hAmeas).aestronglyMeasurable
    · simpa [J, subjectIntegral, E, A, Pi.sub_apply] using
        (hELp.sub hALp).integrable_sq
  have hLp := memLp_finsetSum Finset.univ (fun i _ =>
    (memLp_two_iff_integrable_sq (hSquare i).1).2 (hSquare i).2)
  simpa only [aggregateIntegral, J] using hLp.integrable_sq

/-- The observed death error has an integrable square under the actual iid
sample law. -/
-- @node: deathError_sq_integrable
lemma deathError_sq_integrable (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory => deathError c P a s h ^ 2)
      (sampleLaw P n) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ := aggregateIntegral (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
  have hJ : Measurable J :=
    DeathCP.measurable_deathCPIntegrand_aggregateIntegral c P hP a hh hh1
  have hi : Integrable (fun x : Sample n => J x ^ 2) μ :=
    (deathAggregateIntegral_sq_integrable _ _ _
      (armDeathFailureLaw_nonnegativeTimeLaw P a)
      (referenceDeathLaw_hasCensorHazard hP a) _
      (deathCPIntegrand_leftPredictable c P a h)
      (deathCPIntegrand_jointMeasurable c P hP a hh hh1) _ (by linarith)
      (DeathCP.deathCPIntegrand_quadraticEnergyFinite c P hP a hh hh1)
      (DeathCP.deathCPIntegrand_energy_integrable c P hP a hh hh1))
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hm : Integrable (fun x : Sample n => J x ^ 2)
      ((sampleLaw P n).map (observedDeathSample a)) := by
    rw [observedDeathSample_map_eq_reference P hP.deathHazard
      hP.randomAssignment hP.independentCensoring a]
    apply (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2
    apply hi.congr
    filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
    exact congrArg (fun z : ℝ => z ^ 2)
      (DeathCP.aggregateIntegral_referenceStoppedSyntheticSample
        (referenceDeathHazard P a) (deathCPIntegrand c P a h)
        (deathCPIntegrand_leftPredictable c P a h) x hx.1 hx.2.1 hx.2.2
        (by linarith) (by linarith)).symm
  have ht := (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable hs.aemeasurable).1 hm
  apply ht.congr
  filter_upwards [DeathCP.aggregateIntegral_observedDeathSample_eq_deathError_ae
    c P hP a n hh hh1] with s hs
  exact congrArg (fun z : ℝ => z ^ 2) hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
