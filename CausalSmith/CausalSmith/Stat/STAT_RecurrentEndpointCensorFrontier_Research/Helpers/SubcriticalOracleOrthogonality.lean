module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureOrthogonality
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathOracleMoments

/-!
# Full-horizon recurrence and death oracle orthogonality

Roadmap (24): the death oracle depends only on treatment, death, and censor
exposure. Its proved square integrability permits conditional Poisson centering
at the unbounded endpoint weight, without factoring dependent coefficients.
-/

public section

open MeasureTheory
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Same-arm synthetic exposure preserves the observed canonical death pair exactly. -/
-- @node: observedDeathPair_eq_exposureHistory
lemma observedDeathPair_eq_exposureHistory (a : Arm) (z : LatentSubject) :
    observedDeathPair a (observe z) = observedDeathPair a
      (recurrenceExposureHistory (z.treatment, (z.death a, z.censor a))) := by
  by_cases ha : z.treatment = a
  · simp [observedDeathPair, observe, recurrenceExposureHistory, censorHorizon, ha]
  · simp [observedDeathPair, observe, recurrenceExposureHistory, ha]

/-- Square integrability transfers from an actual observed exposure-only
coefficient to its exposure representation by the coordinatewise pushforward. -/
-- @node: integrable_sq_exposure_coefficient_of_observed
lemma integrable_sq_exposure_coefficient_of_observed
    (P : SubjectLaw) (a : Arm) (n : ℕ)
    (g : (Fin n → Arm × (ℝ × ENNReal)) → ℝ) (hg : Measurable g)
    (F : (Fin n → ObsHistory) → ℝ) (hF : Measurable F)
    (hF2 : Integrable (fun s => F s ^ 2) (sampleLaw P n))
    (hfactor : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      F (fun i => observe (z i)) =
        g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))) :
    Integrable (fun e => g e ^ 2)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let e := fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))
  have he : Measurable e := by fun_prop
  letI : IsProbabilityMeasure (P.latent.map e) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  rw [recurrence_sampleLaw_eq_latent_map] at hF2
  have ho : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have hi := (integrable_map_measure (hF.pow_const 2).aestronglyMeasurable
    ho.aemeasurable).1 hF2
  rw [← Measure.pi_map_pi (fun _ : Fin n => he.aemeasurable)]
  apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable
    (show Measurable (fun z : Fin n → LatentSubject => fun i => e (z i)) by
      fun_prop).aemeasurable).2
  apply hi.congr
  filter_upwards [hfactor] with z hz
  dsimp only [Function.comp_def]
  rw [hz]

/-- The full-horizon canonical death oracle is orthogonal to the recurrence
oracle on the actual observed sample. All quadratic moment conditions are
supplied by subcritical overlap and the proved death oracle isometry. -/
-- @node: observedRecurrence_deathOracle_full_orthogonal
lemma observedRecurrence_deathOracle_full_orthogonal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    let J := fun s : Fin n → ObsHistory =>
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s)
    Integrable (fun s => J s * observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s) (sampleLaw P n) ∧
    (∫ s, J s * observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s ∂sampleLaw P n) = 0 := by
  let D := aggregateIntegral (referenceDeathHazard P a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
  let F := fun s : Fin n → ObsHistory => D (observedDeathSample a s)
  let g := fun e : Fin n → Arm × (ℝ × ENNReal) =>
    F (fun i => recurrenceExposureHistory (e i))
  have hD : Measurable D := measurable_deathAggregateIntegral_deterministic _ _
    (measurable_referenceDeathHazard hP a)
    (measurable_subcriticalDeathOracleWeight c P hP a) 1
  have hF : Measurable F := hD.comp (measurable_pi_lambda _ (fun i =>
    (measurable_observedDeathPair a).comp (measurable_pi_apply i)))
  have hg : Measurable g := hF.comp (measurable_pi_lambda _ (fun i =>
    measurable_recurrenceExposureHistory.comp (measurable_pi_apply i)))
  have hfactor : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      F (fun i => observe (z i)) =
        g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply congrArg D
    funext i
    exact observedDeathPair_eq_exposureHistory a (z i)
  have hg2 := integrable_sq_exposure_coefficient_of_observed P a n g hg F hF
    (observedDeathOracle_full_moments c P hP hk a n).2.2.1 hfactor
  exact observedRecurrenceScore_invRetention_orthogonal_of_exposure
    c P hP hk a hn g hg hg2 F hF hfactor

/-- The assembled full-horizon arm oracle is centered and has exactly the
sum of the recurrence and death variance contributions. Orthogonality, rather
than independence, removes its cross term. -/
-- @node: observedSubcriticalArmOracle_full_moments
lemma observedSubcriticalArmOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    let R := observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
    let D := fun s : Fin n → ObsHistory =>
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s)
    Integrable (fun s => R s / P.p a - D s) (sampleLaw P n) ∧
    (∫ s, R s / P.p a - D s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => (R s / P.p a - D s) ^ 2) (sampleLaw P n) ∧
    (∫ s, (R s / P.p a - D s) ^ 2 ∂sampleLaw P n) =
      ((n : ℝ) / P.p a) *
        ((∫ t in (0 : ℝ)..1, survival P a t * P.lam a t / retention P a t) +
          ∫ t in (0 : ℝ)..1, remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)) := by
  let R := observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
  let D := fun s : Fin n → ObsHistory =>
    aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
        (observedDeathSample a s)
  have hr := observedRecurrenceScore_invRetention_full_moments c P hP hk a hn
  have hd := observedDeathOracle_full_moments c P hP hk a n
  have hx := observedRecurrence_deathOracle_full_orthogonal c P hP hk a hn
  have hR : MemLp R 2 (sampleLaw P n) :=
    (memLp_two_iff_integrable_sq hr.1.aestronglyMeasurable).2 hr.2.2.1
  have hD : MemLp D 2 (sampleLaw P n) :=
    (memLp_two_iff_integrable_sq hd.1.aestronglyMeasurable).2 hd.2.2.1
  have hi := (hr.1.div_const (P.p a)).sub hd.1
  refine ⟨hi, ?_, ?_, ?_⟩
  · rw [integral_sub (hr.1.div_const _) hd.1, integral_div, hr.2.1, hd.2.1]
    simp
  · exact (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).1
      (by
        simpa only [div_eq_mul_inv, mul_comm] using
          (hR.const_mul (P.p a)⁻¹).sub hD)
  · calc
      _ = ∫ s, R s ^ 2 / P.p a ^ 2 + D s ^ 2 -
          (2 / P.p a) * (D s * R s) ∂sampleLaw P n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by ring)
      _ = (∫ s, R s ^ 2 ∂sampleLaw P n) / P.p a ^ 2 +
          (∫ s, D s ^ 2 ∂sampleLaw P n) := by
        rw [integral_sub (f := fun s => R s ^ 2 / P.p a ^ 2 + D s ^ 2)
          (g := fun s => (2 / P.p a) * (D s * R s))
          ((hr.2.2.1.div_const _).add hd.2.2.1) (hx.1.const_mul _),
          integral_add (f := fun s => R s ^ 2 / P.p a ^ 2)
            (g := fun s => D s ^ 2) (hr.2.2.1.div_const _) hd.2.2.1,
          integral_div, integral_const_mul, hx.2]
        ring
      _ = _ := by
        rw [observedRecurrenceScore_invRetention_full_secondMoment c P hP hk a hn,
          hd.2.2.2]
        have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).ne'
        field_simp
        <;> ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
