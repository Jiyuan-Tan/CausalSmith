module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleControl

/-!
# Fixed-horizon second moment for the death Kaplan--Meier oracle action

This module supplies the finite-energy and isometry layer for the predictable
fixed-horizon Kaplan--Meier oracle integrand.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

private lemma kmOracle_hazard_integrableOn (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    IntegrableOn (fun t => (Real.exp c.dMax) ^ 2 *
      referenceDeathHazard P a t) (Set.Icc (0 : ℝ) T) := by
  have hhazI : IntervalIntegrable (P.hazard a) volume 0 T :=
    (hP.deathHazard.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
      exact Set.Icc_subset_Icc le_rfl hT1)
  have hhaz : IntegrableOn (P.hazard a) (Set.Icc (0 : ℝ) T) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hT0] at hhazI
  apply (hhaz.const_mul ((Real.exp c.dMax) ^ 2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans hT1⟩]

private lemma kmOracle_energyDensity_le_envelope (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) {n : ℕ} (t : ℝ) (x : Sample n) :
    (kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ≤
      (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t := by
  calc
    _ ≤ (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x :=
      kmOracle_energyDensity_le c P hP a hT0 hT1 t x
    _ ≤ (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t * 1 :=
      mul_le_mul_of_nonneg_left (pairInverseRisk_mem_Icc t x).2
        (mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t))
    _ = _ := by ring

/-- The fixed-horizon oracle integrand has finite canonical quadratic energy. -/
lemma kmOracleIntegrand_quadraticEnergyFinite (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.QuadraticEnergyFinite
      (armDeathFailureLaw P a) (referenceDeathLaw P a)
      (referenceDeathHazard P a) (kmOracleIntegrand P a T (n := n)) T := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t
  have hf : Integrable f ν := kmOracle_hazard_integrableOn c P hP a hT0 hT1
  have hf0 : ∀ᵐ t ∂ν, 0 ≤ f t := by
    filter_upwards [] with t
    exact mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t)
  have hinner (x : Sample n) :
      (∫⁻ t, ENNReal.ofReal
        ((kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
          (∑ i : Fin n,
            Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν) ≤
        ENNReal.ofReal (∫ t, f t ∂ν) := by
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (f t) ∂ν := by
        apply lintegral_mono
        intro t
        exact ENNReal.ofReal_le_ofReal
          (kmOracle_energyDensity_le_envelope c P hP a hT0 hT1 t x)
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
    ((kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν ∂μ) ≠ ⊤
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫⁻ _x : Sample n, ENNReal.ofReal (∫ t, f t ∂ν) ∂μ :=
      lintegral_mono hinner
    _ = ENNReal.ofReal (∫ t, f t ∂ν) := by simp

/-- The fixed-horizon predictable oracle energy is measurable in the sample. -/
lemma measurable_kmOracle_predictableEnergy (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (referenceDeathHazard P a) (kmOracleIntegrand P a T (n := n)) T) := by
  classical
  let e : Sample n × ℝ → ℝ := fun p =>
    (kmOracleIntegrand P a T p.2 p.1) ^ 2 * referenceDeathHazard P a p.2 *
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
    exact (((kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1).comp
      measurable_swap).pow_const 2).mul
      ((measurable_referenceDeathHazard hP a).comp measurable_snd) |>.mul
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
lemma kmOracle_predictableEnergy_integrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Integrable
      (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (kmOracleIntegrand P a T (n := n)) T)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t
  have hf : Integrable f ν := kmOracle_hazard_integrableOn c P hP a hT0 hT1
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_kmOracle_predictableEnergy c P hP a hT0 hT1).aestronglyMeasurable
    (∫ t, f t ∂ν)
  filter_upwards [] with x
  have heMeas : Measurable (fun t =>
      (kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
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
    exact (((kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1).comp
      (measurable_id.prodMk measurable_const)).pow_const 2).mul
      (measurable_referenceDeathHazard hP a) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have he : Integrable (fun t =>
      (kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ν :=
    hf.mono' heMeas.aestronglyMeasurable.restrict (by
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact kmOracle_energyDensity_le_envelope c P hP a hT0 hT1 t x
      · exact mul_nonneg (mul_nonneg (sq_nonneg _)
          (referenceDeathHazard_nonneg hP a t))
          (Finset.sum_nonneg (fun i _ => by
            unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
            split_ifs <;> norm_num)))
  change ‖∫ t,
    (kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ∂ν‖ ≤
    ∫ t, f t ∂ν
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (referenceDeathHazard_nonneg hP a t))
      (Finset.sum_nonneg (fun i _ => by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num))))]
  apply integral_mono_ae he hf
  filter_upwards [] with t
  exact kmOracle_energyDensity_le_envelope c P hP a hT0 hT1 t x

/-- Canonical isometry for the fixed-horizon Kaplan--Meier oracle action. -/
lemma kmOracle_aggregate_isometry (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  exact Causalean.Stat.RecurrentEvent.CountingProcess.aggregate_integral_isometry
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
    (referenceDeathHazard P a)
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (referenceDeathLaw_hasCensorHazard hP a)
    (kmOracleIntegrand P a T)
    (kmOracleIntegrand_leftPredictable P a T)
    (kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1)
    T hT0 (kmOracleIntegrand_quadraticEnergyFinite c P hP a hT0 hT1)
    (kmOracle_predictableEnergy_integrable c P hP a hT0 hT1)

/-- The canonical fixed-horizon aggregate oracle action is measurable. -/
lemma measurable_kmOracle_aggregateIntegral (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T (n := n)) T) := by
  classical
  have hcomp (i : Fin n) : Measurable (fun x : Sample n =>
      ∫ t in Set.Icc 0 T,
        kmOracleIntegrand P a T t x * referenceDeathHazard P a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∂volume) := by
    let e : Sample n × ℝ → ℝ := fun p =>
      kmOracleIntegrand P a T p.2 p.1 * referenceDeathHazard P a p.2 *
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
      (((kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1).comp
        measurable_swap).mul
        ((measurable_referenceDeathHazard hP a).comp measurable_snd)).mul hrisk
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
  exact ((kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1).comp
    (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
      measurable_const |>.sub (hcomp i)

/-- The fixed-horizon aggregate oracle action is bounded by its deterministic
hazard envelope weighted by the expected reciprocal risk set. -/
lemma kmOracle_aggregate_secondMoment_le_expectedInverseRisk
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      ∫ t in Set.Icc 0 T,
        (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t *
          (∫ x : Sample n,
            Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
            ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
              (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∂volume := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let e : Sample n × ℝ → ℝ := fun p =>
    (kmOracleIntegrand P a T p.2 p.1) ^ 2 * referenceDeathHazard P a p.2 *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t
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
    exact (((kmOracleIntegrand_jointMeasurable c P hP a hT0 hT1).comp
      measurable_swap).pow_const 2).mul
      ((measurable_referenceDeathHazard hP a).comp measurable_snd) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have heNonneg (p : Sample n × ℝ) : 0 ≤ e p := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (referenceDeathHazard_nonneg hP a p.2))
      (Finset.sum_nonneg (fun i _ => by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num))
  have heInt : Integrable e (μ.prod ν) := by
    apply (lintegral_ofReal_ne_top_iff_integrable heMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall heNonneg)).1
    rw [lintegral_prod _ heMeas.ennreal_ofReal.aemeasurable]
    exact kmOracleIntegrand_quadraticEnergyFinite c P hP a hT0 hT1
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
  have hf : Integrable f ν := kmOracle_hazard_integrableOn c P hP a hT0 hT1
  have hfr : Integrable (fun t => f t * r t) ν := by
    apply hf.mono' (hf.aestronglyMeasurable.mul hrMeas.aestronglyMeasurable)
    filter_upwards [] with t
    have hf0 : 0 ≤ f t :=
      mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t)
    change |f t * r t| ≤ f t
    rw [abs_of_nonneg (mul_nonneg hf0 (hrBounds t).1)]
    exact mul_le_of_le_one_right hf0 (hrBounds t).2
  rw [kmOracle_aggregate_isometry (n := n) c P hP a hT0 hT1]
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
      exact kmOracle_energyDensity_le c P hP a hT0 hT1 t x
    _ = f t * r t := by rw [integral_const_mul]

/-- On a strict fixed horizon, the canonical oracle action has an explicit
`1/n` second-moment bound with a deterministic positive at-risk floor. -/
lemma kmOracle_aggregate_secondMoment_le_fixedRate
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      (2 / ((n : ℝ) *
        (c.pMin * retention P a T * Real.exp (-c.dMax)))) *
        ∫ t in Set.Icc 0 T,
          (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t ∂volume := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)
  let f : ℝ → ℝ := fun t =>
    (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t
  let r : ℝ → ℝ := fun t => ∫ x : Sample n,
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∂μ
  let C : ℝ := 2 / ((n : ℝ) *
    (c.pMin * retention P a T * Real.exp (-c.dMax)))
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  have hrT : 0 < retention P a T :=
    retention_pos_of_modelClass c P hP a T hT0 hT1
  have hf : Integrable f ν :=
    kmOracle_hazard_integrableOn c P hP a hT0 hT1.le
  have hfr : Integrable (fun t => f t * r t) ν := by
    have hrMeas : Measurable r := by
      exact (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
        measurable_swap).stronglyMeasurable.integral_prod_left'.measurable
    apply hf.mono' (hf.aestronglyMeasurable.mul hrMeas.aestronglyMeasurable)
    filter_upwards [] with t
    have hf0 : 0 ≤ f t :=
      mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t)
    have hr0 : 0 ≤ r t := integral_nonneg fun x => (pairInverseRisk_mem_Icc t x).1
    have hr1 : r t ≤ 1 := by
      have hi : Integrable (fun x : Sample n =>
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) μ := by
        apply Integrable.of_bound
          (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
            (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
        filter_upwards [] with x
        change |Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x| ≤ 1
        rw [abs_of_nonneg (pairInverseRisk_mem_Icc t x).1]
        exact (pairInverseRisk_mem_Icc t x).2
      simpa [r] using integral_mono hi (integrable_const 1)
        (fun x => (pairInverseRisk_mem_Icc t x).2)
    change |f t * r t| ≤ f t
    rw [abs_of_nonneg (mul_nonneg hf0 hr0)]
    exact mul_le_of_le_one_right hf0 hr1
  calc
    _ ≤ ∫ t : ℝ, f t * r t ∂ν :=
      kmOracle_aggregate_secondMoment_le_expectedInverseRisk
        c P hP a n hT0 hT1.le
    _ ≤ ∫ t : ℝ, C * f t ∂ν := by
      apply integral_mono_ae hfr (hf.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ((volume.restrict (Set.Icc 0 T)).ae_ne (0 : ℝ))] with t ht htne
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hinv := integral_inverseRisk_le_arm_tail c P hP a hn ht0
        (ht.2.trans_lt hT1)
      have hr : retention P a T ≤ retention P a t :=
        (retention_antitone P a) ht.2
      have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a
        ⟨ht.1, ht.2.trans hT1.le⟩).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hf0 : 0 ≤ f t :=
        mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t)
      calc
        f t * r t ≤ f t * C := mul_le_mul_of_nonneg_left (by
          calc
            r t ≤ 2 / ((n : ℝ) *
                (P.p a * retention P a t * survival P a t)) := hinv
            _ ≤ C := by
              dsimp [C]
              have hp : c.pMin ≤ P.p a := hP.treatmentOverlap a
              have hp0 : 0 ≤ P.p a := c.pMin_pos.le.trans hp
              have hr0 : 0 ≤ retention P a t := hrT.le.trans hr
              have hs0 : 0 ≤ survival P a t := (Real.exp_pos _).le
              have hprod : c.pMin * retention P a T * Real.exp (-c.dMax) ≤
                  P.p a * retention P a t * survival P a t :=
                mul_le_mul (mul_le_mul hp hr hrT.le hp0) hs
                  (Real.exp_pos _).le (mul_nonneg hp0 hr0)
              apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
              · exact mul_pos hnR (mul_pos (mul_pos c.pMin_pos hrT)
                  (Real.exp_pos _))
              · exact mul_le_mul_of_nonneg_left hprod hnR.le) hf0
        _ = C * f t := by ring
    _ = C * ∫ t : ℝ, f t ∂ν := by rw [integral_const_mul]
    _ = _ := rfl

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
