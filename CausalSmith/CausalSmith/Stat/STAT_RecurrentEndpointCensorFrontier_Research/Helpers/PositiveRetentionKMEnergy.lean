module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMControl
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRiskSet

/-!
# Kaplan--Meier oracle isometry for positive retention

Roadmap (19)--(22): the genuine dependent KM integrand has finite quadratic
energy and an integrable predictable variation under the independent reference
law. The counting-process isometry therefore applies at the full horizon,
without endpoint smoothness assumptions or independence of KM and risk.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The measurable reference hazard has an integrable deterministic KM envelope. -/
-- @node: positiveRetention_kmOracle_hazard_integrableOn
lemma positiveRetention_kmOracle_hazard_integrableOn (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    IntegrableOn (fun t => (Real.exp c.dMax) ^ 2 *
      positiveRetention_referenceHazard P hDeath a t) (Set.Icc (0 : ℝ) T) := by
  exact (positiveRetention_referenceHazard_integrableOn c P hDeath hDeathBounds a T).const_mul _

/-- The KM quadratic-energy density is dominated by an integrable hazard envelope. -/
-- @node: positiveRetention_kmOracle_energyDensity_le_envelope
lemma positiveRetention_kmOracle_energyDensity_le_envelope (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) {n : ℕ} (t : ℝ) (x : Sample n) :
    (kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ≤
      (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t := by
  calc
    _ ≤ (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x :=
      positiveRetention_kmOracle_energyDensity_le c P hDeath hDeathBounds a hT0 hT1 t x
    _ ≤ (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t * 1 :=
      mul_le_mul_of_nonneg_left (pairInverseRisk_mem_Icc t x).2
        (mul_nonneg (sq_nonneg _) (positiveRetention_referenceHazard_nonneg P hDeath a t))
    _ = _ := by ring

/-- The fixed-horizon oracle integrand has finite canonical quadratic energy. -/
-- @node: positiveRetention_kmOracleIntegrand_quadraticEnergyFinite
lemma positiveRetention_kmOracleIntegrand_quadraticEnergyFinite (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.QuadraticEnergyFinite
      (armDeathFailureLaw P a) (referenceDeathLaw P a)
      (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T (n := n)) T := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t
  have hf : Integrable f ν := positiveRetention_kmOracle_hazard_integrableOn c P hDeath hDeathBounds a hT0 hT1
  have hf0 : ∀ᵐ t ∂ν, 0 ≤ f t := by
    filter_upwards [] with t
    exact mul_nonneg (sq_nonneg _) (positiveRetention_referenceHazard_nonneg P hDeath a t)
  have hinner (x : Sample n) :
      (∫⁻ t, ENNReal.ofReal
        ((kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
          (∑ i : Fin n,
            Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν) ≤
        ENNReal.ofReal (∫ t, f t ∂ν) := by
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (f t) ∂ν := by
        apply lintegral_mono
        intro t
        exact ENNReal.ofReal_le_ofReal
          (positiveRetention_kmOracle_energyDensity_le_envelope c P hDeath hDeathBounds a hT0 hT1 t x)
      _ = ENNReal.ofReal (∫ t, f t ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hf hf0).symm
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.QuadraticEnergyFinite
  change (∫⁻ x : Sample n, ∫⁻ t, ENNReal.ofReal
    ((kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν ∂μ) ≠ ⊤
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫⁻ _x : Sample n, ENNReal.ofReal (∫ t, f t ∂ν) ∂μ :=
      lintegral_mono hinner
    _ = ENNReal.ofReal (∫ t, f t ∂ν) := by simp

/-- The fixed-horizon predictable oracle energy is measurable in the sample. -/
-- @node: positiveRetention_measurable_kmOracle_predictableEnergy
@[fun_prop] lemma positiveRetention_measurable_kmOracle_predictableEnergy (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T (n := n)) T) := by
  classical
  let e : Sample n × ℝ → ℝ := fun p =>
    (kmOracleIntegrand P a T p.2 p.1) ^ 2 * positiveRetention_referenceHazard P hDeath a p.2 *
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
    exact (((positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1).comp
      measurable_swap).pow_const 2).mul
      ((positiveRetention_referenceHazard_measurable P hDeath a).comp measurable_snd) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have hset : MeasurableSet {p : Sample n × ℝ |
      p.2 ∈ Set.Icc (0 : ℝ) T} := measurableSet_Icc.preimage measurable_snd
  let g : Sample n × ℝ → ℝ := fun p =>
    if p.2 ∈ Set.Icc (0 : ℝ) T then e p else 0
  have hg : Measurable g := he.ite hset measurable_const
  have hint := hg.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))
  convert hint.measurable using 1
  ext x
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext t
  simp [g, e, Set.indicator]

/-- The fixed-horizon predictable oracle energy is integrable under the
reference iid product law. -/
-- @node: positiveRetention_kmOracle_predictableEnergy_integrable
lemma positiveRetention_kmOracle_predictableEnergy_integrable (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Integrable
      (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T (n := n)) T)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t
  have hf : Integrable f ν := positiveRetention_kmOracle_hazard_integrableOn c P hDeath hDeathBounds a hT0 hT1
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  apply Integrable.of_bound
    (positiveRetention_measurable_kmOracle_predictableEnergy c P hDeath hDeathBounds a hT0 hT1).aestronglyMeasurable
    (∫ t, f t ∂ν)
  filter_upwards [] with x
  have heMeas : Measurable (fun t =>
      (kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) := by
    have hrisk (i : Fin n) : Measurable (fun t : ℝ =>
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
      unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
      apply Measurable.ite
      · exact (measurableSet_le measurable_const measurable_id).inter
          ((measurableSet_le measurable_id measurable_const).inter
            (measurableSet_le measurable_id measurable_const))
      · exact measurable_const
      · exact measurable_const
    exact (((positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1).comp
      (measurable_id.prodMk measurable_const)).pow_const 2).mul
      (positiveRetention_referenceHazard_measurable P hDeath a) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have he : Integrable (fun t =>
      (kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ν :=
    hf.mono' heMeas.aestronglyMeasurable.restrict (by
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact positiveRetention_kmOracle_energyDensity_le_envelope c P hDeath hDeathBounds a hT0 hT1 t x
      · exact mul_nonneg (mul_nonneg (sq_nonneg _)
          (positiveRetention_referenceHazard_nonneg P hDeath a t))
          (Finset.sum_nonneg (fun i _ => by
            unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
            split_ifs <;> norm_num)))
  change ‖∫ t,
    (kmOracleIntegrand P a T t x) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ∂ν‖ ≤
    ∫ t, f t ∂ν
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (positiveRetention_referenceHazard_nonneg P hDeath a t))
      (Finset.sum_nonneg (fun i _ => by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num))))]
  apply integral_mono_ae he hf
  filter_upwards [] with t
  exact positiveRetention_kmOracle_energyDensity_le_envelope c P hDeath hDeathBounds a hT0 hT1 t x

/-- Canonical isometry for the fixed-horizon Kaplan--Meier oracle action. -/
-- @node: positiveRetention_kmOracle_aggregate_isometry
lemma positiveRetention_kmOracle_aggregate_isometry (c : ClassConstants) (P : SubjectLaw)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  exact Causalean.Stat.RecurrentEvent.CountingProcess.aggregate_integral_isometry
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
    (positiveRetention_referenceHazard P hDeath a)
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (positiveRetention_referenceDeathLaw_hasCensorHazard c P hDeath hDeathBounds a)
    (kmOracleIntegrand P a T)
    (kmOracleIntegrand_leftPredictable P a T)
    (positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1)
    T hT0 (positiveRetention_kmOracleIntegrand_quadraticEnergyFinite c P hDeath hDeathBounds a hT0 hT1)
    (positiveRetention_kmOracle_predictableEnergy_integrable c P hDeath hDeathBounds a hT0 hT1)


/-- The fixed-horizon aggregate oracle action is bounded by its deterministic
hazard envelope weighted by the expected reciprocal risk set. -/
-- @node: positiveRetention_kmOracle_aggregate_secondMoment_le_expectedInverseRisk
lemma positiveRetention_kmOracle_aggregate_secondMoment_le_expectedInverseRisk
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      ∫ t in Set.Icc 0 T,
        (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t *
          (∫ x : Sample n,
            Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
            ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
              (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∂volume := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let e : Sample n × ℝ → ℝ := fun p =>
    (kmOracleIntegrand P a T p.2 p.1) ^ 2 * positiveRetention_referenceHazard P hDeath a p.2 *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t
  let r : ℝ → ℝ := fun t => ∫ x : Sample n,
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∂μ
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  have hrisk (i : Fin n) : Measurable (fun p : Sample n × ℝ =>
      Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
    apply Measurable.ite
    · exact (measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd (by fun_prop)).inter
          (measurableSet_le measurable_snd (by fun_prop)))
    · exact measurable_const
    · exact measurable_const
  have heMeas : Measurable e := by
    exact (((positiveRetention_kmOracleIntegrand_jointMeasurable c P hDeath hDeathBounds a hT0 hT1).comp
      measurable_swap).pow_const 2).mul
      ((positiveRetention_referenceHazard_measurable P hDeath a).comp measurable_snd) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have heNonneg (p : Sample n × ℝ) : 0 ≤ e p := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (positiveRetention_referenceHazard_nonneg P hDeath a p.2))
      (Finset.sum_nonneg (fun i _ => by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num))
  have heInt : Integrable e (μ.prod ν) := by
    apply (lintegral_ofReal_ne_top_iff_integrable heMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall heNonneg)).1
    rw [lintegral_prod _ heMeas.ennreal_ofReal.aemeasurable]
    exact positiveRetention_kmOracleIntegrand_quadraticEnergyFinite c P hDeath hDeathBounds a hT0 hT1
  have hrMeas : Measurable r := by
    exact (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
      measurable_swap).stronglyMeasurable.integral_prod_left'.measurable
  have hrBounds (t : ℝ) : 0 ≤ r t ∧ r t ≤ 1 := by
    have hi : Integrable (fun x : Sample n =>
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) μ := by
      apply Integrable.of_bound
        (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      filter_upwards [] with x
      change |Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x| ≤ 1
      rw [abs_of_nonneg (pairInverseRisk_mem_Icc t x).1]
      exact (pairInverseRisk_mem_Icc t x).2
    constructor
    · exact integral_nonneg (fun x => (pairInverseRisk_mem_Icc t x).1)
    · simpa [r] using integral_mono hi (integrable_const 1)
        (fun x => (pairInverseRisk_mem_Icc t x).2)
  have hf : Integrable f ν := positiveRetention_kmOracle_hazard_integrableOn c P hDeath hDeathBounds a hT0 hT1
  have hfr : Integrable (fun t => f t * r t) ν := by
    apply hf.mono' (hf.aestronglyMeasurable.mul hrMeas.aestronglyMeasurable)
    filter_upwards [] with t
    have hf0 : 0 ≤ f t :=
      mul_nonneg (sq_nonneg _) (positiveRetention_referenceHazard_nonneg P hDeath a t)
    change |f t * r t| ≤ f t
    rw [abs_of_nonneg (mul_nonneg hf0 (hrBounds t).1)]
    exact mul_le_of_le_one_right hf0 (hrBounds t).2
  rw [positiveRetention_kmOracle_aggregate_isometry (n := n) c P hDeath hDeathBounds a hT0 hT1]
  change (∫ x : Sample n, ∫ t : ℝ, e (x, t) ∂ν ∂μ) ≤
    ∫ t : ℝ, f t * r t ∂ν
  rw [integral_integral_swap heInt]
  apply integral_mono_ae heInt.integral_prod_right hfr
  filter_upwards [heInt.prod_left_ae] with t het
  have hconst : Integrable (fun x : Sample n => f t *
      Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) μ := by
    apply Integrable.of_bound
      ((Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
        (measurable_const.prodMk measurable_id)).const_mul (f t)).aestronglyMeasurable
      |f t|
    filter_upwards [] with x
    change |f t * Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x| ≤
      |f t|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (by rw [abs_of_nonneg (pairInverseRisk_mem_Icc t x).1]
          exact (pairInverseRisk_mem_Icc t x).2)
  calc
    (∫ x : Sample n, e (x, t) ∂μ) ≤
        ∫ x : Sample n, f t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∂μ := by
      apply integral_mono het hconst
      intro x
      exact positiveRetention_kmOracle_energyDensity_le c P hDeath hDeathBounds a hT0 hT1 t x
    _ = f t * r t := by rw [integral_const_mul]


/-- The independent reference risk has the same positive population floor,
including at the endpoint. The reciprocal-binomial bound needs no smoothness. -/
-- @node: positiveRetention_reference_inverseRisk_le
lemma positiveRetention_reference_inverseRisk_le
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∫ x : Sample n, Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor)) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  have hq : 0 < c.pMin * Real.exp (-c.dMax) * c.Ghor :=
    mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  apply integral_inverseRisk_le_two_div hn
    (armDeathFailureLaw P a) (referenceDeathLaw P a) ht0.le hq
  change c.pMin * Real.exp (-c.dMax) * c.Ghor ≤
    (armDeathFailureLaw P a).real (Ici t) * (referenceDeathLaw P a).real (Ici t)
  rw [armDeathFailureLaw_real_Ici P hRandom hAssignment a ht0 ht1,
    referenceDeathLaw_real_Ici hDeath a ⟨ht0.le, ht1⟩]
  have hb := positiveRetention_arm_risk_probability_lower c P hOverlap
    hDeathBounds hHorizon a ⟨ht0.le, ht1⟩
  convert hb using 1 <;> ring

/-- The full-horizon KM oracle action has a genuine parametric second moment,
derived from its isometry and the reciprocal-risk envelope. -/
-- @node: positiveRetention_kmOracle_secondMoment_le_inv_sampleSize
lemma positiveRetention_kmOracle_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a 1) 1 x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      (2 * (Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * positiveRetention_referenceHazard P hDeath a t
  let r : ℝ → ℝ := fun t => ∫ x : Sample n,
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∂μ
  let C : ℝ := 2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor))
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  have hf : Integrable f ν := positiveRetention_kmOracle_hazard_integrableOn
    c P hDeath hDeathBounds a (by norm_num) (by norm_num)
  have hrMeas : Measurable r :=
    (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
      measurable_swap).stronglyMeasurable.integral_prod_left'.measurable
  have hrBounds (t : ℝ) : 0 ≤ r t ∧ r t ≤ 1 := by
    have hi : Integrable (fun x : Sample n =>
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) μ := by
      apply Integrable.of_bound
        (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      filter_upwards [] with x
      change |Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x| ≤ 1
      rw [abs_of_nonneg (pairInverseRisk_mem_Icc t x).1]
      exact (pairInverseRisk_mem_Icc t x).2
    constructor
    · exact integral_nonneg (fun x => (pairInverseRisk_mem_Icc t x).1)
    · simpa [r] using integral_mono hi (integrable_const 1)
        (fun x => (pairInverseRisk_mem_Icc t x).2)
  have hf0 (t : ℝ) : 0 ≤ f t :=
    mul_nonneg (sq_nonneg _) (positiveRetention_referenceHazard_nonneg P hDeath a t)
  have hfr : Integrable (fun t => f t * r t) ν := by
    apply hf.mono' (hf.aestronglyMeasurable.mul hrMeas.aestronglyMeasurable)
    filter_upwards [] with t
    change |f t * r t| ≤ f t
    rw [abs_of_nonneg (mul_nonneg (hf0 t) (hrBounds t).1)]
    exact mul_le_of_le_one_right (hf0 t) (hrBounds t).2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg c.pMin_pos.le (Real.exp_pos _).le) c.Ghor_pos.le))
  have hint : (∫ t, f t ∂ν) ≤ (Real.exp c.dMax) ^ 2 * c.dMax := by
    have heq := positiveRetention_referenceHazard_ae_eq P hDeath a
    calc
      _ ≤ ∫ _t, (Real.exp c.dMax) ^ 2 * c.dMax ∂ν := by
        apply integral_mono_ae hf (integrable_const _)
        filter_upwards [heq, ae_restrict_mem measurableSet_Icc] with t ht htmem
        dsimp [f]
        rw [ht, referenceDeathHazard_eq P a htmem]
        exact mul_le_mul_of_nonneg_left (hDeathBounds a t htmem).2 (sq_nonneg _)
      _ = _ := by simp [ν]
  calc
    _ ≤ ∫ t, f t * r t ∂ν :=
      positiveRetention_kmOracle_aggregate_secondMoment_le_expectedInverseRisk
        c P hDeath hDeathBounds a n (by norm_num) (by norm_num)
    _ ≤ ∫ t, C * f t ∂ν := by
      apply integral_mono_ae hfr (hf.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (ν.ae_ne (0 : ℝ))] with t ht htne
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hb := positiveRetention_reference_inverseRisk_le c P hRandom hAssignment
        hOverlap hDeath hDeathBounds hHorizon a hn ht0 ht.2
      simpa only [r, μ, C, mul_comm] using mul_le_mul_of_nonneg_left hb (hf0 t)
    _ = C * ∫ t, f t ∂ν := integral_const_mul _ _
    _ ≤ C * ((Real.exp c.dMax) ^ 2 * c.dMax) :=
      mul_le_mul_of_nonneg_left hint hC
    _ = _ := by dsimp [C]; ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
