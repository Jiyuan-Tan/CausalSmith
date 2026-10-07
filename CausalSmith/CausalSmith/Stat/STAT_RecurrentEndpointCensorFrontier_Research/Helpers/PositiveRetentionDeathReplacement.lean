module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathDifferenceMoments

/-!
# Positive-retention observed death oracle replacement

Roadmap (26)--(27): transport the predictable difference isometry through
the stopped reference law to the actual observed experiment. Chebyshev then
makes the root-n death difference negligible under the benchmark assumptions.
-/

public section

open MeasureTheory Set Filter
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed predictable difference integral is centered and square
integrable; its second moment equals the canonical reference second moment. -/
-- @node: positiveRetention_observedDeathOracleDifferenceIntegral_moments
lemma positiveRetention_observedDeathOracleDifferenceIntegral_moments
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hCensor : IndependentCensoring P)
    (hOverlap : TreatmentOverlap c P) (hRecurBounds : RecurrenceBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    let J := aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1
    Integrable (fun s => J (observedDeathSample a s)) (sampleLaw P n) ∧
    (∫ s, J (observedDeathSample a s) ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => J (observedDeathSample a s) ^ 2) (sampleLaw P n) ∧
    (∫ s, J (observedDeathSample a s) ^ 2 ∂sampleLaw P n) =
      ∫ x : Sample n, J x ^ 2
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J := aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a (n := n)) 1
  have heq : J = aggregateIntegral
      (DeathCP.positiveRetention_referenceHazard P hDeath a)
      (deathOracleDifferenceIntegrand c P a) 1 := by
    funext x
    exact (DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a _ x).symm
  have hJ : Measurable J := by
    rw [heq]
    exact DeathCP.positiveRetention_measurable_aggregateIntegral _ _ 1
      (DeathCP.positiveRetention_referenceHazard_measurable P hDeath a)
      (positiveRetention_measurable_deathOracleDifferenceIntegrand c P hPoisson hDeath
        hDeathBounds a n)
  have hj := positiveRetention_deathOracleDifferenceIntegrand_full_moments c P hPoisson hDeath
    hDeathBounds hOverlap hRecurBounds hHorizon a n
  have hreg : (fun x => J (referenceStoppedSyntheticSample x)) =ᵐ[μ] J := by
    filter_upwards [DeathCP.positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx
    exact DeathCP.aggregateIntegral_referenceStoppedSyntheticSample _ _
      (deathOracleDifferenceIntegrand_leftPredictable c P a n) x hx.1 hx.2.1 hx.2.2
      (by norm_num) (by norm_num)
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hmap : (sampleLaw P n).map (observedDeathSample a) =
      μ.map referenceStoppedSyntheticSample :=
    observedDeathSample_map_eq_reference P hDeath
      hRandom hCensor a
  have transfer (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ s, f (J (observedDeathSample a s)) ∂sampleLaw P n) =
        ∫ x, f (J x) ∂μ := by
    change (∫ s, (f ∘ J) (observedDeathSample a s) ∂sampleLaw P n) =
      ∫ x, (f ∘ J) x ∂μ
    rw [← integral_map hs.aemeasurable (hf.comp hJ).aestronglyMeasurable, hmap,
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hf.comp hJ).aestronglyMeasurable]
    exact integral_congr_ae (hreg.fun_comp f)
  have integrable_transfer (f : ℝ → ℝ) (hf : Measurable f)
      (hi : Integrable (fun x => f (J x)) μ) :
      Integrable (fun s => f (J (observedDeathSample a s))) (sampleLaw P n) := by
    apply (integrable_map_measure (hf.comp hJ).aestronglyMeasurable hs.aemeasurable).1
    rw [hmap]
    exact (integrable_map_measure (hf.comp hJ).aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2
        (hi.congr (hreg.fun_comp f).symm)
  refine ⟨integrable_transfer id measurable_id hj.1, ?_,
    integrable_transfer (fun x : ℝ => x ^ 2) (by fun_prop) hj.2.2.1,
    transfer (fun x : ℝ => x ^ 2) (by fun_prop)⟩
  exact (transfer id measurable_id).trans hj.2.1

/-- The actual observed full-horizon death difference vanishes in second
mean, by stopped-law transport of the predictable isometry. -/
-- @node: positiveRetention_observedDeathOracleDifferenceIntegral_secondMoment_tendsto_zero
lemma positiveRetention_observedDeathOracleDifferenceIntegral_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hCensor : IndependentCensoring P)
    (hOverlap : TreatmentOverlap c P) (hRecurBounds : RecurrenceBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s,
      (aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)) ^ 2
      ∂sampleLaw P n) atTop (nhds 0) := by
  apply (positiveRetention_deathOracleDifferenceIntegral_secondMoment_tendsto_zero
    c P hRandom hAssignment hOverlap hPoisson hDeath hCensor hRecurBounds hDeathBounds hHorizon
      a).congr'
  exact Eventually.of_forall (fun n =>
    (positiveRetention_observedDeathOracleDifferenceIntegral_moments c P hPoisson hDeath
      hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon a n).2.2.2.symm)

/-- Chebyshev gives the full-horizon observed death difference probability
limit, using its proved integrable energy. -/
-- @node: positiveRetention_observedDeathOracleDifferenceIntegral_probability_tendsto_zero
lemma positiveRetention_observedDeathOracleDifferenceIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hCensor : IndependentCensoring P)
    (hOverlap : TreatmentOverlap c P) (hRecurBounds : RecurrenceBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hlim := (positiveRetention_observedDeathOracleDifferenceIntegral_secondMoment_tendsto_zero
    c P hPoisson hDeath hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon
      a).div_const (ε ^ 2)
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  apply Eventually.of_forall
  intro n
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let J := fun s : Fin n → ObsHistory => aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)
  have hi := (positiveRetention_observedDeathOracleDifferenceIntegral_moments c P hPoisson hDeath
    hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon a n).2.2.1
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (J s))) hi (ε ^ 2)
  have hsub : {s | ε < |J s|} ⊆ {s | ε ^ 2 ≤ J s ^ 2} := by
    intro s hs
    change ε < |J s| at hs
    change ε ^ 2 ≤ J s ^ 2
    nlinarith [sq_abs (J s)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [mul_comm, J] using
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
      (sq_nonneg ε)).trans hm


/-- Finite quadratic energies supply the pathwise integrability needed for
linearity of the normalized death difference on the reference law. -/
-- @node: positiveRetention_deathOracleDifferenceIntegral_eq_scaled_difference_ae
lemma positiveRetention_deathOracleDifferenceIntegral_eq_scaled_difference_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hCensor : IndependentCensoring P) (hOverlap : TreatmentOverlap c P)
    (hRecurBounds : RecurrenceBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n :
      ℕ) :
    (aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1) =ᵐ[
        Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a)]
      fun x => Real.sqrt n * aggregateIntegral (referenceDeathHazard P a)
        (deathCPIntegrand c P a 0) 1 x -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x /
            Real.sqrt n := by
  classical
  have heq (H : ℝ → Sample n → ℝ) :
      aggregateIntegral (referenceDeathHazard P a) H 1 =
        aggregateIntegral (DeathCP.positiveRetention_referenceHazard P hDeath a) H 1 := by
    funext x
    exact (DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a H x).symm
  simp only [heq]
  have hq := (deathAggregateIntegral_energy_conditions_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
      (DeathCP.positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t)
    1 (positiveRetention_deathOracle_energy_integrable_prod c P hOverlap hPoisson hDeath
      hRecurBounds hDeathBounds hHorizon a n)).1
  have hp : ∀ᵐ x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a), ∀ i : Fin n,
      Integrable (fun t => deathCPIntegrand c P a 0 t x *
        DeathCP.positiveRetention_referenceHazard P hDeath a t * riskIndicator i t x)
        (volume.restrict (Icc (0 : ℝ) 1)) ∧
      Integrable (fun t => subcriticalDeathOracleWeight c P a t *
        DeathCP.positiveRetention_referenceHazard P hDeath a t * riskIndicator i t x)
        (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Filter.eventually_all]
    intro i
    exact (subject_hazard_path_integrable_ae _ _ _
        (DeathCP.positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a)
      _ (positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson hDeath hDeathBounds a (by
        norm_num) (by norm_num))
      i 1
      (DeathCP.positiveRetention_referenceHazard_quadraticEnergyFinite
        c P hPoisson hDeath hRecurBounds hDeathBounds a)).and
      (subject_hazard_path_integrable_ae _ _ _
          (DeathCP.positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a)
        _ ((positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath hDeathBounds
          a).comp measurable_fst)
        i 1 hq)
  filter_upwards [hp] with x hx
  unfold aggregateIntegral
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold subjectIntegral deathOracleDifferenceIntegrand
  have he : (fun t => (Real.sqrt n * deathCPIntegrand c P a 0 t x -
      subcriticalDeathOracleWeight c P a t / Real.sqrt n) *
        DeathCP.positiveRetention_referenceHazard P hDeath a t * riskIndicator i t x) =
      fun t => Real.sqrt n * (deathCPIntegrand c P a 0 t x *
        DeathCP.positiveRetention_referenceHazard P hDeath a t * riskIndicator i t x) -
        (subcriticalDeathOracleWeight c P a t * DeathCP.positiveRetention_referenceHazard P hDeath
          a t *
          riskIndicator i t x) / Real.sqrt n := by funext t; ring
  rw [he, integral_sub ((hx i).1.const_mul _) ((hx i).2.div_const _),
    integral_const_mul, integral_div]
  split_ifs <;> ring

/-- The predictable integral equals the actual root-n estimated death error
minus the normalized endpoint oracle, almost surely on observed samples. -/
-- @node: positiveRetention_observedDeathOracleDifferenceIntegral_eq_deathError_ae
lemma positiveRetention_observedDeathOracleDifferenceIntegral_eq_deathError_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hCensor : IndependentCensoring P) (hOverlap : TreatmentOverlap c P)
    (hRecurBounds : RecurrenceBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n :
      ℕ) :
    (fun s => aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      fun s => Real.sqrt n * deathError c P a s 0 -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s) / Real.sqrt n := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J := aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a (n := n)) 1
  let K := aggregateIntegral (referenceDeathHazard P a)
    (deathCPIntegrand c P a 0 (n := n)) 1
  let O := aggregateIntegral (referenceDeathHazard P a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
  have meas (H : ℝ → Sample n → ℝ)
      (hH : Measurable (fun p : ℝ × Sample n => H p.1 p.2)) :
      Measurable (aggregateIntegral (referenceDeathHazard P a) H 1) := by
    have heq : aggregateIntegral (referenceDeathHazard P a) H 1 =
        aggregateIntegral (DeathCP.positiveRetention_referenceHazard P hDeath a) H 1 := by
      funext x
      exact (DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a H x).symm
    rw [heq]
    exact DeathCP.positiveRetention_measurable_aggregateIntegral _ _ 1
      (DeathCP.positiveRetention_referenceHazard_measurable P hDeath a) hH
  have hJ : Measurable J := meas _
    (positiveRetention_measurable_deathOracleDifferenceIntegrand c P hPoisson hDeath hDeathBounds
      a n)
  have hK : Measurable K := meas _
    (positiveRetention_deathCPIntegrand_jointMeasurable c P hPoisson hDeath hDeathBounds a
      (by norm_num) (by norm_num))
  have hO : Measurable O := meas _
    ((positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath hDeathBounds a).comp
      measurable_fst)
  have he : J =ᵐ[μ.map referenceStoppedSyntheticSample]
      fun x => Real.sqrt n * K x - O x / Real.sqrt n := by
    apply (ae_map_iff measurable_referenceStoppedSyntheticSample.aemeasurable
      (measurableSet_eq_fun hJ ((hK.const_mul _).sub (hO.div_const _)))).2
    filter_upwards [positiveRetention_deathOracleDifferenceIntegral_eq_scaled_difference_ae c P
      hPoisson hDeath hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon a n,
      DeathCP.positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx hr
    have stop (H : ℝ → Sample n → ℝ) (hH : LeftPredictable H) :=
      DeathCP.aggregateIntegral_referenceStoppedSyntheticSample
        (referenceDeathHazard P a) H hH x hr.1 hr.2.1 hr.2.2
        (u := 1) (by norm_num) (by norm_num)
    change J (referenceStoppedSyntheticSample x) =
      Real.sqrt n * K (referenceStoppedSyntheticSample x) -
        O (referenceStoppedSyntheticSample x) / Real.sqrt n
    dsimp only [J, K, O]
    rw [stop _ (deathOracleDifferenceIntegrand_leftPredictable c P a n),
      stop _ (deathCPIntegrand_leftPredictable c P a 0),
      stop _ (by intro t x y hh; rfl)]
    exact hx
  rw [← observedDeathSample_map_eq_reference P hDeath
    hRandom hCensor a] at he
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have ho := (ae_map_iff hs.aemeasurable
    (measurableSet_eq_fun hJ ((hK.const_mul _).sub (hO.div_const _)))).1 he
  have hd := DeathCP.positiveRetention_aggregateIntegral_observedDeathSample_eq_deathError_ae
    c P hPoisson hDeath hDeathBounds a n (h := 0) (by norm_num) (by norm_num)
  simp only [sub_zero] at hd
  filter_upwards [ho, hd] with s hs hd
  change J (observedDeathSample a s) = _ at hs ⊢
  rw [hs]
  change Real.sqrt n * K (observedDeathSample a s) -
    O (observedDeathSample a s) / Real.sqrt n = _
  rw [show K (observedDeathSample a s) = deathError c P a s 0 from hd]

/-- The actual ordinary death martingale admits full-horizon endpoint oracle
replacement at root-n scale, as required in roadmap (18)--(19). -/
-- @node: positiveRetention_deathError_zero_oracle_difference_probability_tendsto_zero
lemma positiveRetention_deathError_zero_oracle_difference_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hCensor : IndependentCensoring P) (hOverlap : TreatmentOverlap c P)
    (hRecurBounds : RecurrenceBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε :
      ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * deathError c P a s 0 -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s) / Real.sqrt n|}) atTop (nhds 0) := by
  apply (positiveRetention_observedDeathOracleDifferenceIntegral_probability_tendsto_zero c P
    hPoisson hDeath hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon a
    hε).congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  filter_upwards [positiveRetention_observedDeathOracleDifferenceIntegral_eq_deathError_ae c P
    hPoisson hDeath hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon a n]
    with s hs
  change (ε < |aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)|) =
      (ε < |Real.sqrt n * deathError c P a s 0 -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s) / Real.sqrt n|)
  rw [hs]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
