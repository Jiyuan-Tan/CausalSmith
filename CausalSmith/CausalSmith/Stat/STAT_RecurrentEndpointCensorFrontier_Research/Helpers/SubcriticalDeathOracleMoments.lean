module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorCentering
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleEnergy

/-!
# Unbounded full-horizon death oracle moments

Roadmap (2), (5), (6), and (24): the deterministic oracle's quadratic
energy is integrated against the exact at-risk marginal before applying the
unbounded counting-process isometry. Subcritical overlap supplies finiteness.
-/

@[expose] public section

open MeasureTheory Set
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The deterministic full-horizon death oracle weight, with totalized inverse retention. -/
-- @node: subcriticalDeathOracleWeight
noncomputable def subcriticalDeathOracleWeight (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (t : ℝ) : ℝ :=
  deathTargetWeight c P a 0 t / (P.p a * retention P a t)

/-- Canonical at-risk indicators are jointly measurable in the time and sample. -/
-- @node: measurable_referenceDeath_riskIndicator
@[fun_prop]
lemma measurable_referenceDeath_riskIndicator {n : ℕ} (i : Fin n) :
    Measurable (fun p : Sample n × ℝ => riskIndicator i p.2 p.1) := by
  unfold riskIndicator
  apply Measurable.ite
    ((measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd (by fun_prop)).inter
        (measurableSet_le measurable_snd (by fun_prop))))
    <;> exact measurable_const

/-- A subject's canonical at-risk expectation is the product of its two time tails. -/
-- @node: referenceDeath_riskIndicator_integral
lemma referenceDeath_riskIndicator_integral
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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
    DeathCP.armDeathFailureLaw_real_Ici P hP.randomAssignment hP.assignmentLaw a ht.1 ht.2.le,
    referenceDeathLaw_real_Ici hP.deathHazard a ⟨ht.1.le, ht.2.le⟩]

/-- Summing canonical at-risk indicators gives the exact finite-sample risk marginal. -/
-- @node: referenceDeath_riskSum_integral
lemma referenceDeath_riskSum_integral
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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
  simp_rw [referenceDeath_riskIndicator_integral c P hP a n _ ht]
  simp

/-- The deterministic endpoint oracle is measurable without a hazard extension premise. -/
-- @node: measurable_subcriticalDeathOracleWeight
@[fun_prop]
lemma measurable_subcriticalDeathOracleWeight (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) : Measurable (subcriticalDeathOracleWeight c P a) := by
  exact (measurable_deathTargetWeight c P hP a (by norm_num) (by norm_num)).div
    (measurable_const.mul (measurable_retention P a))

/-- One inverse-retention factor cancels in the canonical death oracle energy. -/
-- @node: subcriticalDeathOracle_energy_marginal
lemma subcriticalDeathOracle_energy_marginal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x : Sample n, subcriticalDeathOracleWeight c P a t ^ 2 *
      referenceDeathHazard P a t * (∑ i : Fin n, riskIndicator i t x)
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      ((n : ℝ) / P.p a) *
        (remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t)) := by
  rw [integral_const_mul, referenceDeath_riskSum_integral c P hP a n ht,
    referenceDeathHazard_eq P a ⟨ht.1.le, ht.2.le⟩]
  have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).ne'
  have hg : retention P a t ≠ 0 :=
    (retention_pos_of_modelClass c P hP a t ht.1.le ht.2).ne'
  have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  simp only [subcriticalDeathOracleWeight, deathTargetWeight,
    if_pos (show t ∈ Icc (0 : ℝ) (1 - 0) by simpa using ⟨ht.1.le, ht.2.le⟩)]
  field_simp
  <;> ring

/-- Subcritical overlap supplies product quadratic-energy integrability for the
unbounded death oracle itself. -/
-- @node: subcriticalDeathOracle_energy_integrable_prod
lemma subcriticalDeathOracle_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    Integrable (fun p : Sample n × ℝ => subcriticalDeathOracleWeight c P a p.2 ^ 2 *
      referenceDeathHazard P a p.2 * (∑ i : Fin n, riskIndicator i p.2 p.1))
      ((Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)).prod
          (volume.restrict (Icc (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  let E := fun (x : Sample n) (t : ℝ) => subcriticalDeathOracleWeight c P a t ^ 2 *
    referenceDeathHazard P a t * (∑ i : Fin n, riskIndicator i t x)
  have hm : Measurable (fun p : Sample n × ℝ => E p.1 p.2) := by
    dsimp [E]
    exact (((measurable_subcriticalDeathOracleWeight c P hP a).comp
      measurable_snd).pow_const 2 |>.mul
        ((measurable_referenceDeathHazard hP a).comp measurable_snd)).mul
          (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  have hnonneg (x : Sample n) (t : ℝ) : 0 ≤ E x t := by
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t))
    apply Finset.sum_nonneg
    intro i _
    unfold riskIndicator
    split_ifs <;> norm_num
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with t
    apply Integrable.of_bound
      ((hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (subcriticalDeathOracleWeight c P a t ^ 2 * referenceDeathHazard P a t * n)
    filter_upwards [] with x
    dsimp only [Function.comp_def, id_eq]
    rw [Real.norm_of_nonneg (hnonneg x t)]
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (sq_nonneg _) (referenceDeathHazard_nonneg hP a t))
    calc
      (∑ i : Fin n, riskIndicator i t x) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        unfold riskIndicator
        split_ifs <;> norm_num
      _ = (n : ℝ) := by simp
  · have hi := (subcritical_death_energy_intervalIntegrable c P hP hk a).const_mul
      ((n : ℝ) / P.p a)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp_rw [Real.norm_of_nonneg (hnonneg _ t)]
    exact (subcriticalDeathOracle_energy_marginal c P hP a n ht).symm

/-- The full canonical endpoint death oracle is centered and square integrable;
its second moment is its genuine predictable energy. -/
-- @node: subcriticalDeathOracle_full_moments
lemma subcriticalDeathOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    Integrable (aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∧
    (∫ x : Sample n, aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) = 0 ∧
    Integrable (fun x : Sample n => (aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x) ^ 2)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∧
    (∫ x : Sample n, (aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
      ∫ x : Sample n, predictableEnergy (referenceDeathHazard P a)
        (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  exact deathAggregateIntegral_moments_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (referenceDeathLaw_hasCensorHazard hP a) _
    (fun _ _ _ _ => rfl)
    ((measurable_subcriticalDeathOracleWeight c P hP a).comp measurable_fst)
    1 (by norm_num) (subcriticalDeathOracle_energy_integrable_prod c P hP hk a n)

/-- Fubini and the exact risk marginal identify the full endpoint death oracle
second moment with the paper's death variance contribution. -/
-- @node: subcriticalDeathOracle_full_secondMoment
lemma subcriticalDeathOracle_full_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
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
  rw [(subcriticalDeathOracle_full_moments c P hP hk a n).2.2.2]
  unfold predictableEnergy
  rw [integral_integral_swap (subcriticalDeathOracle_energy_integrable_prod c P hP hk a n),
    ← restrict_Ioo_eq_restrict_Icc]
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, ((n : ℝ) / P.p a) *
        (remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact subcriticalDeathOracle_energy_marginal c P hP a n ht
    _ = _ := by
      rw [integral_const_mul,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]

/-- Deterministic measurable weights give a measurable canonical aggregate,
including unbounded weights. The compensator integral is a measurable parameter integral. -/
-- @node: measurable_deathAggregateIntegral_deterministic
lemma measurable_deathAggregateIntegral_deterministic {n : ℕ}
    (hazard w : ℝ → ℝ) (hh : Measurable hazard) (hw : Measurable w) (u : ℝ) :
    Measurable (aggregateIntegral hazard (fun t (_ : Sample n) => w t) u) := by
  unfold aggregateIntegral
  apply Finset.measurable_sum
  intro i _
  unfold subjectIntegral
  apply Measurable.sub
  · have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
    have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
    exact (hw.comp hc).ite
      ((measurableSet_le hc measurable_const).inter
        (measurableSet_lt hc hf)) measurable_const
  · have hm : Measurable (fun p : Sample n × ℝ =>
        w p.2 * hazard p.2 * riskIndicator i p.2 p.1) :=
      ((hw.comp measurable_snd).mul (hh.comp measurable_snd)).mul
        (measurable_referenceDeath_riskIndicator i)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The full endpoint death oracle on actual observed samples has centered,
square-integrable moments and the exact paper variance. Stopped reference-law
transport preserves the deterministic integral almost surely. -/
-- @node: observedDeathOracle_full_moments
lemma observedDeathOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
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
  have hJ : Measurable J := measurable_deathAggregateIntegral_deterministic _ _
    (measurable_referenceDeathHazard hP a)
    (measurable_subcriticalDeathOracleWeight c P hP a) 1
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hmap : (sampleLaw P n).map (observedDeathSample a) =
      μ.map referenceStoppedSyntheticSample :=
    observedDeathSample_map_eq_reference P hP.deathHazard
      hP.randomAssignment hP.independentCensoring a
  have hreg : (fun x => J (referenceStoppedSyntheticSample x)) =ᵐ[μ] J := by
    filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
    exact DeathCP.aggregateIntegral_referenceStoppedSyntheticSample _ _
      (fun _ _ _ _ => rfl) x hx.1 hx.2.1 hx.2.2 (by norm_num) le_rfl
  have hreg2 := hreg.fun_comp (fun r : ℝ => r ^ 2)
  have hm := subcriticalDeathOracle_full_moments c P hP hk a n
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
    he2.trans (subcriticalDeathOracle_full_secondMoment c P hP hk a n)⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
