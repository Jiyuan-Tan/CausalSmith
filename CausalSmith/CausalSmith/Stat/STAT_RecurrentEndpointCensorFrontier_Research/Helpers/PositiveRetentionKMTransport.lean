module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionProjection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability

/-!
# Observed KM oracle moments under positive horizon retention

Roadmap (19)--(22): transfer the full-horizon canonical KM isometry to the
observed iid histories using the stopped reference sample. This requires
no endpoint smoothness, and preserves the actual dependent KM integrand.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The fixed-horizon aggregate KM action is measurable under a bounded integrable death hazard. -/
-- @node: positiveRetention_measurable_kmOracle_aggregateIntegral
@[fun_prop] lemma positiveRetention_measurable_kmOracle_aggregateIntegral (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T (n := n)) T) := by
  classical
  have hcomp (i : Fin n) : Measurable (fun x : Sample n =>
      ∫ t in Set.Icc 0 T,
        kmOracleIntegrand P a T t x * positiveRetention_referenceHazard P hDeath a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∂volume) := by
    let e : Sample n × ℝ → ℝ := fun p =>
      kmOracleIntegrand P a T p.2 p.1 * positiveRetention_referenceHazard P hDeath a p.2 *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1
    have hrisk : Measurable (fun p : Sample n × ℝ =>
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1) := by
      unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
      apply Measurable.ite
      · exact (measurableSet_le measurable_const measurable_snd).inter
          ((measurableSet_le measurable_snd (by fun_prop)).inter
            (measurableSet_le measurable_snd (by fun_prop)))
      · exact measurable_const
      · exact measurable_const
    have he : Measurable e :=
      (((positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1).comp
        measurable_swap).mul
        ((positiveRetention_referenceHazard_measurable P hDeath a).comp measurable_snd)).mul hrisk
    let g : Sample n × ℝ → ℝ := fun p =>
      if p.2 ∈ Set.Icc (0 : ℝ) T then e p else 0
    have hg : Measurable g := he.ite
      (measurableSet_Icc.preimage measurable_snd) measurable_const
    have hint := hg.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ))
    convert hint.measurable using 1
    ext x
    rw [← integral_indicator measurableSet_Icc]
    congr 1
    funext t
    simp [g, e, Set.indicator]
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
    Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral
  apply Finset.measurable_fun_sum
  intro i _
  have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
  have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
  exact ((positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1).comp
    (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
      measurable_const |>.sub (hcomp i)

/-- Squared KM actions transfer exactly from observed histories to the independent reference sample. -/
-- @node: positiveRetention_observedDeathSample_oracleAggregate_secondMoment_eq_reference
lemma positiveRetention_observedDeathSample_oracleAggregate_secondMoment_eq_reference
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ s : Fin n → ObsHistory,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) =
    ∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ :=
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T
  have hJ : Measurable J :=
    positiveRetention_measurable_kmOracle_aggregateIntegral c P hDeath hDeathBounds a hT0 hT1
  have hreg := positiveRetention_referenceSample_regular_ae P hDeath a n
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
      rw [observedDeathSample_map_eq_reference P hDeath
        hRandom hCensor a]
    _ = ∫ x : Sample n, (J (referenceStoppedSyntheticSample x)) ^ 2 ∂μ := by
      exact integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable
    _ = ∫ x : Sample n, (J x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hreg] with x hx
      exact congrArg (fun z : ℝ => z ^ 2)
        (aggregateIntegral_referenceStoppedSyntheticSample
          (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T)
          (kmOracleIntegrand_leftPredictable P a T) x hx.1 hx.2.1 hx.2.2
          hT0 hT1)

/-- The observed KM action has an integrable square by canonical quadratic energy and reference transport. -/
-- @node: positiveRetention_observedDeathSample_oracleAggregate_sq_integrable
lemma positiveRetention_observedDeathSample_oracleAggregate_sq_integrable
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory =>
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2) (sampleLaw P n) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ :=
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T
  have hJ : Measurable J :=
    positiveRetention_measurable_kmOracle_aggregateIntegral c P hDeath hDeathBounds a hT0 hT1
  have hi : Integrable (fun x : Sample n => J x ^ 2) μ :=
    deathAggregateIntegral_sq_integrable _ _ _
      (armDeathFailureLaw_nonnegativeTimeLaw P a)
      (positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a) _
      (kmOracleIntegrand_leftPredictable P a T)
      (positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1) T hT0
      (positiveRetention_kmOracleIntegrand_quadraticEnergyFinite c P hDeath hDeathBounds a hT0 hT1)
      (positiveRetention_kmOracle_predictableEnergy_integrable c P hDeath hDeathBounds a hT0 hT1)
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  apply (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
    hs.aemeasurable).1
  rw [observedDeathSample_map_eq_reference P hDeath
    hRandom hCensor a]
  apply (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
    measurable_referenceStoppedSyntheticSample.aemeasurable).2
  apply hi.congr
  filter_upwards [positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx
  exact congrArg (fun z : ℝ => z ^ 2)
    (aggregateIntegral_referenceStoppedSyntheticSample
      (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T)
      (kmOracleIntegrand_leftPredictable P a T) x hx.1 hx.2.1 hx.2.2
      hT0 hT1).symm


/-- The full-horizon observed KM action inherits the canonical parametric bound. -/
-- @node: positiveRetention_observedKMOracle_secondMoment_le_inv_sampleSize
lemma positiveRetention_observedKMOracle_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a 1) 1
        (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) ≤
      (2 * (Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  rw [positiveRetention_observedDeathSample_oracleAggregate_secondMoment_eq_reference
    c P hDeath hDeathBounds hRandom hCensor a n (by norm_num) (by norm_num)]
  exact positiveRetention_kmOracle_secondMoment_le_inv_sampleSize c P hRandom
    hAssignment hOverlap hDeath hDeathBounds hHorizon a hn

/-- The observed full-horizon KM oracle action vanishes in probability, by its
transferred second moment rather than an independence assumption on KM weights. -/
-- @node: positiveRetention_observedKMOracle_probability_tendsto_zero
lemma positiveRetention_observedKMOracle_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a 1) 1
        (observedDeathSample a s)|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw
    infer_instance
  let C : ℝ := 2 * (Real.exp c.dMax) ^ 2 * c.dMax /
    (c.pMin * Real.exp (-c.dMax) * c.Ghor)
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ) / ε ^ 2) atTop (nhds 0) := by
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul, Pi.inv_apply] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C).div_const (ε ^ 2)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (positiveRetention_probability_le_secondMoment (sampleLaw P n) _
    (positiveRetention_observedDeathSample_oracleAggregate_sq_integrable
      c P hDeath hDeathBounds hRandom hCensor a n (by norm_num) (by norm_num)) hε).trans
    (div_le_div_of_nonneg_right
      (positiveRetention_observedKMOracle_secondMoment_le_inv_sampleSize
        c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
        (by omega)) (sq_nonneg ε))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
