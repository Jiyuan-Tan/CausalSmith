module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathIsometry
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionInfluenceMeasurability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathOracleMoments

/-!
# Death oracle moments under positive horizon retention

Roadmap (25)--(28) of the benchmark: bounded deterministic oracle weights
and the measurable hazard representative yield centered, square-integrable
canonical death contributions without endpoint smoothness assumptions.
-/

public section

open MeasureTheory Set
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The full-horizon death oracle is measurable under the benchmark hazards. -/
-- @node: positiveRetention_measurable_deathOracleWeight
@[fun_prop] lemma positiveRetention_measurable_deathOracleWeight
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) :
    Measurable (subcriticalDeathOracleWeight c P a) := by
  exact (positiveRetention_measurable_deathTargetWeight c P hPoisson hDeath
    hDeathBounds a (by norm_num) (by norm_num)).div
      (measurable_const.mul (measurable_retention P a))

/-- Positive horizon retention bounds the actual deterministic oracle globally;
its target multiplier vanishes outside the study window. -/
-- @node: positiveRetention_deathOracleWeight_abs_le
lemma positiveRetention_deathOracleWeight_abs_le
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (t : ℝ) :
    |subcriticalDeathOracleWeight c P a t| ≤
      (c.lambdaMax * Real.exp c.dMax) / (c.pMin * c.Ghor) := by
  have hL : 0 ≤ c.lambdaMax * Real.exp c.dMax :=
    mul_nonneg (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) (Real.exp_pos _).le
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hp := c.pMin_pos.trans_le (hOverlap a)
    have hg := c.Ghor_pos.trans_le (hHorizon a t ht)
    rw [subcriticalDeathOracleWeight, abs_div,
      abs_of_pos (mul_pos hp hg)]
    exact div_le_div₀ hL
      (positiveRetention_deathTargetWeight_zero_abs_le c P hRecurBounds hDeathBounds a t)
      (mul_pos c.pMin_pos c.Ghor_pos)
      (mul_le_mul (hOverlap a) (hHorizon a t ht) c.Ghor_pos.le hp.le)
  · simpa [subcriticalDeathOracleWeight, deathTargetWeight, ht] using
      div_nonneg hL (mul_pos c.pMin_pos c.Ghor_pos).le

/-- Bounded oracle weights and the integrable measurable hazard give finite
product quadratic energy for any sample size, including zero. -/
-- @node: positiveRetention_deathOracle_energy_integrable_prod
lemma positiveRetention_deathOracle_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    Integrable (fun p : Sample n × ℝ => subcriticalDeathOracleWeight c P a p.2 ^ 2 *
      DeathCP.positiveRetention_referenceHazard P hDeath a p.2 *
        (∑ i : Fin n, riskIndicator i p.2 p.1))
      ((Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)).prod
          (volume.restrict (Icc (0 : ℝ) 1))) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by dsimp [μ]; unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw; infer_instance
  let B := (c.lambdaMax * Real.exp c.dMax) / (c.pMin * c.Ghor)
  have hB : 0 ≤ B := by
    dsimp [B]
    have hl := c.lambdaMin_pos.trans c.lambdaMin_lt
    have hp := c.pMin_pos
    have hg := c.Ghor_pos
    positivity
  have hm : Measurable (fun p : Sample n × ℝ =>
      subcriticalDeathOracleWeight c P a p.2 ^ 2 *
        (∑ i : Fin n, riskIndicator i p.2 p.1)) :=
    (((positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath
      hDeathBounds a).comp measurable_snd).pow_const 2).mul
        (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  have hi := (DeathCP.positiveRetention_referenceHazard_integrableOn c P hDeath
    hDeathBounds a 1).comp_snd μ
  have hb : ∀ᵐ p : Sample n × ℝ ∂μ.prod (volume.restrict (Icc (0 : ℝ) 1)),
      ‖subcriticalDeathOracleWeight c P a p.2 ^ 2 *
        (∑ i : Fin n, riskIndicator i p.2 p.1)‖ ≤ B ^ 2 * n := by
    filter_upwards [] with p
    have hr0 : 0 ≤ ∑ i : Fin n, riskIndicator i p.2 p.1 := by
      apply Finset.sum_nonneg
      intro i _
      unfold riskIndicator
      split_ifs <;> norm_num
    have hr1 : (∑ i : Fin n, riskIndicator i p.2 p.1) ≤ n := by
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          unfold riskIndicator
          split_ifs <;> norm_num
        _ = _ := by simp
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hr0)]
    apply mul_le_mul _ hr1 hr0 (sq_nonneg B)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (positiveRetention_deathOracleWeight_abs_le c P hOverlap hRecurBounds
        hDeathBounds hHorizon a p.2) 2
  apply (hi.bdd_mul hm.aestronglyMeasurable hb).congr
  filter_upwards [] with p
  ring

/-- The full canonical death oracle is centered and square integrable, with
second moment given by its predictable energy under the benchmark assumptions. -/
-- @node: positiveRetention_deathOracle_full_moments
lemma positiveRetention_deathOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    let J := aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
    let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a)
    Integrable J μ ∧ (∫ x, J x ∂μ) = 0 ∧
      Integrable (fun x => J x ^ 2) μ ∧
      (∫ x, J x ^ 2 ∂μ) =
        ∫ x, predictableEnergy (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x ∂μ := by
  have hm := deathAggregateIntegral_moments_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (DeathCP.positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t)
    (fun _ _ _ _ => rfl)
    ((positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath
      hDeathBounds a).comp measurable_fst) 1 (by norm_num)
    (positiveRetention_deathOracle_energy_integrable_prod c P hOverlap hPoisson
      hDeath hRecurBounds hDeathBounds hHorizon a n)
  have heq : aggregateIntegral (DeathCP.positiveRetention_referenceHazard P hDeath a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 =
      aggregateIntegral (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 := by
    funext x
    exact DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a _ x
  simpa only [heq, DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq,
    DeathCP.positiveRetention_referenceHazard_predictableEnergy_eq] using hm

/-- A subject's canonical at-risk expectation is the product of its two time tails. -/
-- @node: positiveRetention_referenceDeath_riskIndicator_integral
lemma positiveRetention_referenceDeath_riskIndicator_integral
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P) (a : Arm)
    (n : ℕ) (i : Fin n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x : Sample n, riskIndicator i t x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      P.p a * retention P a t * survival P a t := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  let R : Set (ℝ × ℝ) := Ici t ×ˢ Ici t
  have hR : MeasurableSet R := measurableSet_Ici.prod measurableSet_Ici
  have heq : (fun x : Sample n => riskIndicator i t x) =
      fun x => R.indicator (fun _ => (1 : ℝ)) (x i) := by
    funext x
    simp [riskIndicator, R, Set.indicator, ht.1.le, Prod.le_def]
  rw [heq]
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
  rw [integral_comp_eval (measurable_const.indicator hR).aestronglyMeasurable,
    integral_indicator_const _ hR]
  simp only [smul_eq_mul, mul_one, R, Measure.real, Measure.prod_prod,
    ENNReal.toReal_mul]
  rw [← Measure.real, ← Measure.real,
    DeathCP.armDeathFailureLaw_real_Ici P hRandom hAssignment a ht.1 ht.2.le,
    referenceDeathLaw_real_Ici hDeath a ⟨ht.1.le, ht.2.le⟩]

/-- Summing canonical at-risk indicators gives the exact finite-sample risk marginal. -/
-- @node: positiveRetention_referenceDeath_riskSum_integral
lemma positiveRetention_referenceDeath_riskSum_integral
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P) (a : Arm)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x : Sample n, (∑ i : Fin n, riskIndicator i t x)
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      (n : ℝ) * (P.p a * retention P a t * survival P a t) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  have hi (i : Fin n) : Integrable (fun x : Sample n => riskIndicator i t x)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    apply Integrable.of_bound
      ((measurable_referenceDeath_riskIndicator i).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
    filter_upwards [] with x
    dsimp only [Function.comp_def, id_eq]
    unfold riskIndicator
    split_ifs <;> norm_num
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [positiveRetention_referenceDeath_riskIndicator_integral P hRandom hAssignment hDeath a n _ ht]
  simp

/-- One inverse-retention factor cancels in the canonical death oracle energy. -/
-- @node: positiveRetention_deathOracle_energy_marginal
lemma positiveRetention_deathOracle_energy_marginal
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hOverlap : TreatmentOverlap c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x : Sample n, subcriticalDeathOracleWeight c P a t ^ 2 *
      referenceDeathHazard P a t * (∑ i : Fin n, riskIndicator i t x)
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      ((n : ℝ) / P.p a) *
        (remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t)) := by
  rw [integral_const_mul, positiveRetention_referenceDeath_riskSum_integral P hRandom hAssignment hDeath a n ht,
    referenceDeathHazard_eq P a ⟨ht.1.le, ht.2.le⟩]
  have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hOverlap a)).ne'
  have hg : retention P a t ≠ 0 :=
    (c.Ghor_pos.trans_le (hHorizon a t ⟨ht.1.le, ht.2.le⟩)).ne'
  have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  simp only [subcriticalDeathOracleWeight, deathTargetWeight,
    if_pos (show t ∈ Icc (0 : ℝ) (1 - 0) by simpa using ⟨ht.1.le, ht.2.le⟩)]
  field_simp
  <;> ring

/-- Fubini and the exact randomized risk marginal identify the death oracle's
second moment with the death contribution to the benchmark variance. -/
-- @node: positiveRetention_deathOracle_full_secondMoment
lemma positiveRetention_deathOracle_full_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    (∫ x : Sample n, (aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      ((n : ℝ) / P.p a) * ∫ t in (0 : ℝ)..1,
        remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  rw [(positiveRetention_deathOracle_full_moments c P hOverlap hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon a n).2.2.2]
  have heq : predictableEnergy (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 =
      predictableEnergy (DeathCP.positiveRetention_referenceHazard P hDeath a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 := by
    funext x
    exact (DeathCP.positiveRetention_referenceHazard_predictableEnergy_eq P hDeath a _ x).symm
  rw [heq]
  unfold predictableEnergy
  rw [integral_integral_swap (positiveRetention_deathOracle_energy_integrable_prod
    c P hOverlap hPoisson hDeath hRecurBounds hDeathBounds hHorizon a n),
    ← restrict_Ioo_eq_restrict_Icc]
  have hd := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 from fun _ ht => ⟨ht.1.le, ht.2.le⟩)
    (DeathCP.positiveRetention_referenceHazard_ae_eq P hDeath a)
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, ((n : ℝ) / P.p a) *
        (remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t)) := by
      apply integral_congr_ae
      filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
      rw [hdt]
      exact positiveRetention_deathOracle_energy_marginal c P hRandom hAssignment
        hDeath hOverlap hHorizon a n ht
    _ = _ := by
      rw [integral_const_mul,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]

/-- The full endpoint death oracle on actual observed samples has centered,
square-integrable moments and the exact paper variance. Stopped reference-law
transport preserves the deterministic integral almost surely. -/
-- @node: positiveRetention_observedDeathOracle_full_moments
lemma positiveRetention_observedDeathOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ) :
    let J := fun x : Sample n => aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x
    Integrable (fun s => J (observedDeathSample a s)) (sampleLaw P n) ∧
    (∫ s, J (observedDeathSample a s) ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => J (observedDeathSample a s) ^ 2) (sampleLaw P n) ∧
    (∫ s, J (observedDeathSample a s) ^ 2 ∂sampleLaw P n) =
      ((n : ℝ) / P.p a) * ∫ t in (0 : ℝ)..1,
        remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) := by
  let J := fun x : Sample n => aggregateIntegral (referenceDeathHazard P a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  have heq : J = aggregateIntegral
      (DeathCP.positiveRetention_referenceHazard P hDeath a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 := by
    funext x
    exact (DeathCP.positiveRetention_referenceHazard_aggregateIntegral_eq P hDeath a _ x).symm
  have hJ : Measurable J := by
    rw [heq]
    exact measurable_deathAggregateIntegral_deterministic _ _
      (DeathCP.positiveRetention_referenceHazard_measurable P hDeath a)
      (positiveRetention_measurable_deathOracleWeight c P hPoisson hDeath hDeathBounds a) 1
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hmap : (sampleLaw P n).map (observedDeathSample a) =
      μ.map referenceStoppedSyntheticSample :=
    observedDeathSample_map_eq_reference P hDeath
      hRandom hCensor a
  have hreg : (fun x => J (referenceStoppedSyntheticSample x)) =ᵐ[μ] J := by
    filter_upwards [DeathCP.positiveRetention_referenceSample_regular_ae P hDeath a n] with x hx
    exact DeathCP.aggregateIntegral_referenceStoppedSyntheticSample _ _
      (fun _ _ _ _ => rfl) x hx.1 hx.2.1 hx.2.2 (by norm_num) le_rfl
  have hreg2 := hreg.fun_comp (fun r : ℝ => r ^ 2)
  have hm := positiveRetention_deathOracle_full_moments c P hOverlap hPoisson hDeath
    hRecurBounds hDeathBounds hHorizon a n
  have hi : Integrable J ((sampleLaw P n).map (observedDeathSample a)) := by
    rw [hmap]
    exact (integrable_map_measure hJ.aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2 (hm.1.congr hreg.symm)
  have hi2 : Integrable (fun x => J x ^ 2)
      ((sampleLaw P n).map (observedDeathSample a)) := by
    rw [hmap]
    exact (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2
        (hm.2.2.1.congr hreg2.symm)
  have he : (∫ s, J (observedDeathSample a s) ∂sampleLaw P n) = ∫ x, J x ∂μ := by
    rw [← integral_map hs.aemeasurable hJ.aestronglyMeasurable, hmap,
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        hJ.aestronglyMeasurable]
    exact integral_congr_ae hreg
  have he2 : (∫ s, J (observedDeathSample a s) ^ 2 ∂sampleLaw P n) =
      ∫ x, J x ^ 2 ∂μ := by
    rw [← integral_map hs.aemeasurable (hJ.pow_const 2).aestronglyMeasurable, hmap,
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable]
    exact integral_congr_ae hreg2
  exact ⟨(integrable_map_measure hJ.aestronglyMeasurable hs.aemeasurable).1 hi,
    he.trans hm.2.1,
    (integrable_map_measure (hJ.pow_const 2).aestronglyMeasurable hs.aemeasurable).1 hi2,
    he2.trans (positiveRetention_deathOracle_full_secondMoment c P hRandom hAssignment
      hOverlap hPoisson hDeath hRecurBounds hDeathBounds hHorizon a n)⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

