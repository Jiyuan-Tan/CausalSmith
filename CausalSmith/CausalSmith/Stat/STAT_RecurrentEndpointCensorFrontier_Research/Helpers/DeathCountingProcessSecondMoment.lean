module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessObservedAdapter

/-! # Second moment of the death counting-process error -/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

namespace DeathCP

abbrev Sample (n : ℕ) :=
  Causalean.Stat.RecurrentEvent.CountingProcess.Sample n

/-- The quadratic-energy density of the death integrand is dominated by its
deterministic target multiplier squared times the hazard. -/
lemma energyDensity_le (c : ClassConstants) (P : SubjectLaw) (a : Arm)
    (h : ℝ) {n : ℕ} (t : ℝ) (x : Sample n) (hhaz : 0 ≤ P.hazard a t) :
    (deathCPIntegrand c P a h t x) ^ 2 * P.hazard a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ≤
      (deathTargetWeight c P a h t) ^ 2 * P.hazard a t := by
  have hkm := pairDeathKMLeft_mem_Icc t x
  have hinv := pairInverseRisk_mem_Icc t x
  have hrisk :=
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_square_risk t x
  have hkmSq : (pairDeathKMLeft t x) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hkm.1 (sub_nonneg.mpr hkm.2)]
  have hweightSq : 0 ≤ (deathTargetWeight c P a h t) ^ 2 := sq_nonneg _
  rw [deathCPIntegrand]
  calc
    (deathTargetWeight c P a h t * pairDeathKMLeft t x *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) ^ 2 *
          P.hazard a t *
          (∑ i : Fin n,
            Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) =
        (deathTargetWeight c P a h t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
          P.hazard a t *
          ((Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) ^ 2 *
            (∑ i : Fin n,
              Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) := by
      ring
    _ = (deathTargetWeight c P a h t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
          P.hazard a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      rw [hrisk]
    _ ≤ (deathTargetWeight c P a h t) ^ 2 *
          (pairDeathKMLeft t x) ^ 2 * P.hazard a t * 1 :=
      mul_le_mul_of_nonneg_left hinv.2
        (mul_nonneg (mul_nonneg hweightSq (sq_nonneg _)) hhaz)
    _ = (deathTargetWeight c P a h t) ^ 2 *
          (pairDeathKMLeft t x) ^ 2 * P.hazard a t := by ring
    _ ≤ (deathTargetWeight c P a h t) ^ 2 * 1 * P.hazard a t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkmSq hweightSq) hhaz
    _ = (deathTargetWeight c P a h t) ^ 2 * 1 * P.hazard a t * 1 := by ring
    _ = (deathTargetWeight c P a h t) ^ 2 * P.hazard a t := by ring

/-- The deterministic death multiplier is uniformly bounded on the compact
estimation interval. -/
lemma exists_deathTargetWeight_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 - h),
      |deathTargetWeight c P a h t| ≤ C := by
  have hc := (continuousOn_deathTargetWeight c P hP a hh hh1).abs
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by exact ⟨0, by constructor <;> linarith⟩) hc
  exact ⟨|deathTargetWeight c P a h t|, abs_nonneg _, fun s hs => hmax hs⟩

/-- The deterministic envelope dominating the predictable death energy is
integrable on the estimation interval. -/
lemma deathTargetWeight_sq_hazard_integrableOn (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    IntegrableOn (fun t => (deathTargetWeight c P a h t) ^ 2 * P.hazard a t)
      (Set.Icc 0 (1 - h)) := by
  have hU0 : (0 : ℝ) ≤ 1 - h := by linarith
  have hhazI : IntervalIntegrable (P.hazard a) volume 0 (1 - h) :=
    (hP.deathHazard.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hU0]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have hhaz : IntegrableOn (P.hazard a) (Set.Icc 0 (1 - h)) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at hhazI
  obtain ⟨C, hC0, hC⟩ := exists_deathTargetWeight_bound c P hP a hh hh1
  apply hhaz.bdd_mul
  · exact ((continuousOn_deathTargetWeight c P hP a hh hh1).pow 2).aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC t ht) 2

/-- The paper death integrand has finite canonical quadratic energy under the
spliced reference death law. -/
lemma deathCPIntegrand_quadraticEnergyFinite (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.QuadraticEnergyFinite
      (armDeathFailureLaw P a) (referenceDeathLaw P a)
      (referenceDeathHazard P a) (deathCPIntegrand c P a h (n := n))
      (1 - h) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 (1 - h))
  let f : ℝ → ℝ := fun t =>
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t
  have hf : Integrable f ν :=
    deathTargetWeight_sq_hazard_integrableOn c P hP a hh hh1
  have hf0 : ∀ᵐ t ∂ν, 0 ≤ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _)
      (c.dMin_pos.le.trans
        (hP.deathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
  have hinner (x : Sample n) :
      (∫⁻ t, ENNReal.ofReal
        ((deathCPIntegrand c P a h t x) ^ 2 * referenceDeathHazard P a t *
          (∑ i : Fin n,
            Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν) ≤
        ENNReal.ofReal (∫ t, f t ∂ν) := by
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (f t) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        apply ENNReal.ofReal_le_ofReal
        rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans (by linarith)⟩]
        exact energyDensity_le c P a h t x
          (c.dMin_pos.le.trans
            (hP.deathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
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
    ((deathCPIntegrand c P a h t x) ^ 2 * referenceDeathHazard P a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν ∂μ) ≠ ⊤
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫⁻ _x : Sample n, ENNReal.ofReal (∫ t, f t ∂ν) ∂μ :=
      lintegral_mono hinner
    _ = ENNReal.ofReal (∫ t, f t ∂ν) := by simp

/-- The predictable energy is a measurable sample statistic. -/
lemma measurable_deathCPIntegrand_predictableEnergy (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (referenceDeathHazard P a) (deathCPIntegrand c P a h (n := n))
      (1 - h)) := by
  classical
  let e : Sample n × ℝ → ℝ := fun p =>
    (deathCPIntegrand c P a h p.2 p.1) ^ 2 * referenceDeathHazard P a p.2 *
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
    exact (((deathCPIntegrand_jointMeasurable c P hP a hh hh1).comp
      measurable_swap).pow_const 2).mul
      ((measurable_referenceDeathHazard hP a).comp measurable_snd) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have hset : MeasurableSet {p : Sample n × ℝ |
      p.2 ∈ Set.Icc (0 : ℝ) (1 - h)} :=
    measurableSet_Icc.preimage measurable_snd
  let g : Sample n × ℝ → ℝ := fun p => if p.2 ∈ Set.Icc (0 : ℝ) (1 - h)
    then e p else 0
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

/-- The predictable energy of the paper death integrand is integrable under
the canonical reference sample law. -/
lemma deathCPIntegrand_energy_integrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable
      (Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a h (n := n))
        (1 - h))
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 (1 - h))
  let f : ℝ → ℝ := fun t =>
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t
  have hf : Integrable f ν :=
    deathTargetWeight_sq_hazard_integrableOn c P hP a hh hh1
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_deathCPIntegrand_predictableEnergy c P hP a hh hh1).aestronglyMeasurable
    (∫ t, f t ∂ν)
  filter_upwards [] with x
  let e : ℝ → ℝ := fun t =>
    (deathCPIntegrand c P a h t x) ^ 2 * referenceDeathHazard P a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
  have heMeas : Measurable e := by
    have hrisk (i : Fin n) : Measurable (fun t : ℝ =>
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
      unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
      apply Measurable.ite
      · exact (measurableSet_le measurable_const measurable_id).inter
          ((measurableSet_le measurable_id measurable_const).inter
            (measurableSet_le measurable_id measurable_const))
      · exact measurable_const
      · exact measurable_const
    exact (((deathCPIntegrand_jointMeasurable c P hP a hh hh1).comp
      (measurable_id.prodMk measurable_const)).pow_const 2).mul
      (measurable_referenceDeathHazard hP a) |>.mul
      (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
  have he : Integrable e ν := hf.mono' heMeas.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold e f
      rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans (by linarith)⟩]
      exact energyDensity_le c P a h t x
        (c.dMin_pos.le.trans
          (hP.deathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
    · exact mul_nonneg (mul_nonneg (sq_nonneg _)
        (referenceDeathHazard_nonneg hP a t))
        (Finset.sum_nonneg (fun i _ => by
          unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
          split_ifs <;> norm_num)))
  change ‖∫ t, e t ∂ν‖ ≤ ∫ t, f t ∂ν
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (referenceDeathHazard_nonneg hP a t))
      (Finset.sum_nonneg (fun i _ => by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        split_ifs <;> norm_num))))]
  apply integral_mono_ae he hf
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  unfold e f
  rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans (by linarith)⟩]
  exact energyDensity_le c P a h t x
    (c.dMin_pos.le.trans
      (hP.deathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)

/-- Canonical second-moment identity for the death integrand under the
reference product law. -/
lemma deathCPIntegrand_aggregate_isometry (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h) x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) =
    ∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h) x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  exact Causalean.Stat.RecurrentEvent.CountingProcess.aggregate_integral_isometry
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
    (referenceDeathHazard P a)
    (armDeathFailureLaw_nonnegativeTimeLaw P a)
    (referenceDeathLaw_hasCensorHazard hP a)
    (deathCPIntegrand c P a h)
    (deathCPIntegrand_leftPredictable c P a h)
    (deathCPIntegrand_jointMeasurable c P hP a hh hh1)
    (1 - h) (by linarith)
    (deathCPIntegrand_quadraticEnergyFinite c P hP a hh hh1)
    (deathCPIntegrand_energy_integrable c P hP a hh hh1)

/-- On a regular observed path, the canonical compensator density is exactly
the paper death-error compensator density at positive times in the horizon. -/
lemma deathCPIntegrand_observed_compensator (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h t : ℝ} (hh : 0 ≤ h) (ht0 : 0 < t)
    (htU : t ≤ 1 - h)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    deathCPIntegrand c P a h t (observedDeathSample a s) *
        referenceDeathHazard P a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
            (observedDeathSample a s)) =
      remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
        (if riskSet a s t = 0 then 0 else P.hazard a t) := by
  have ht1 : t ≤ 1 := by linarith
  rw [referenceDeathHazard_eq P a ⟨ht0.le, ht1⟩]
  rw [deathCPIntegrand, deathTargetWeight, if_pos ⟨ht0.le, htU⟩]
  rw [pairDeathKMLeft_observedDeathSample_eq_deathKMLeft a s hDeathPos hNoTies]
  rw [observedDeathSample_inverseRisk a s ht0]
  have hrisk : (∑ i : Fin n,
      Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
        (observedDeathSample a s)) = (riskSet a s t : ℝ) := by
    calc
      _ = (Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t
          (observedDeathSample a s) : ℝ) := by
        simp [Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskSet]
      _ = _ := by rw [observedDeathSample_riskSet a s ht0]
  rw [hrisk]
  convert deathCompensator_integrand c P a s h t using 1 <;> ring

/-- The canonical event payoff of a synthetic observed subject is the event
summand in the paper death error. -/
lemma deathCPIntegrand_observed_event (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit)
    (i : Fin n) :
    (if (observedDeathSample a s i).2 ≤ 1 - h ∧
        (observedDeathSample a s i).2 < (observedDeathSample a s i).1 then
      deathCPIntegrand c P a h (observedDeathSample a s i).2
        (observedDeathSample a s) else 0) =
    if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ 1 - h then
      remainingTarget c P a h (s i).exit * deathKMLeft a s (s i).exit /
        survival P a (s i).exit * invRisk a s (s i).exit else 0 := by
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd
    · by_cases he : (s i).exit ≤ 1 - h
      · have heq : (observedDeathSample a s i).2 = (s i).exit := by
          simp [observedDeathSample, observedDeathPair, ha, hd]
        have hlt : (observedDeathSample a s i).2 <
            (observedDeathSample a s i).1 := by
          simp [observedDeathSample, observedDeathPair, ha, hd]
        rw [if_pos ⟨heq.trans_le he, hlt⟩, if_pos ⟨ha, hd, he⟩, heq]
        rw [deathCPIntegrand, deathTargetWeight,
          if_pos ⟨(hDeathPos i ha hd).le, he⟩]
        rw [pairDeathKMLeft_observedDeathSample_eq_deathKMLeft a s hDeathPos hNoTies]
        rw [observedDeathSample_inverseRisk a s (hDeathPos i ha hd)]
        ring
      · have heq : (observedDeathSample a s i).2 = (s i).exit := by
          simp [observedDeathSample, observedDeathPair, ha, hd]
        rw [if_neg (by simp [heq, he]), if_neg (by simp [ha, hd, he])]
    · simp [observedDeathSample, observedDeathPair, ha, hd]
  · simp [observedDeathSample, observedDeathPair, ha]

/-- On a regular observed path, the canonical aggregate compensated integral
is the paper's death-error term. -/
lemma aggregateIntegral_observedDeathSample_eq_deathError
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit) :
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
      (observedDeathSample a s) = deathError c P a s h := by
  classical
  let U : ℝ := 1 - h
  let x := observedDeathSample a s
  have hU0 : 0 ≤ U := by dsimp [U]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_deathTargetWeight_bound c P hP a hh hh1
  have hhazI : IntervalIntegrable (P.hazard a) volume 0 U :=
    (hP.deathHazard.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hU0]
      exact Set.Icc_subset_Icc le_rfl (by dsimp [U]; linarith))
  have hhaz : IntegrableOn (P.hazard a) (Set.Icc 0 U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at hhazI
  have hterm (i : Fin n) : IntegrableOn (fun t =>
      deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
      (Set.Icc 0 U) := by
    have hm : Measurable (fun t =>
        deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
      have hrisk : Measurable (fun t : ℝ =>
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) := by
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
        apply Measurable.ite
        · exact (measurableSet_le measurable_const measurable_id).inter
            ((measurableSet_le measurable_id measurable_const).inter
              (measurableSet_le measurable_id measurable_const))
        · exact measurable_const
        · exact measurable_const
      exact ((deathCPIntegrand_jointMeasurable c P hP a hh hh1).comp
        (measurable_id.prodMk measurable_const)).mul
        (measurable_referenceDeathHazard hP a) |>.mul hrisk
    apply (hhaz.const_mul C).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hri : 0 ≤
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∧
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ≤ 1 := by
      unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
      split_ifs <;> norm_num
    rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans (by dsimp [U] at ht ⊢; linarith)⟩]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t
        ⟨ht.1, ht.2.trans (by dsimp [U] at ht ⊢; linarith)⟩).1),
      abs_of_nonneg hri.1]
    calc
      |deathCPIntegrand c P a h t x| * P.hazard a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x
          ≤ C * P.hazard a t *
              Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            ((deathCPIntegrand_abs_le c P a h t x).trans (hC t ht))
            (c.dMin_pos.le.trans (hP.deathBounds a t
              ⟨ht.1, ht.2.trans (by dsimp [U] at ht ⊢; linarith)⟩).1)) hri.1
      _ ≤ C * P.hazard a t * 1 :=
        mul_le_mul_of_nonneg_left hri.2
          (mul_nonneg hC0 (c.dMin_pos.le.trans (hP.deathBounds a t
            ⟨ht.1, ht.2.trans (by dsimp [U] at ht ⊢; linarith)⟩).1))
      _ = C * P.hazard a t := by ring
  have hsumInt : IntegrableOn (fun t => ∑ i : Fin n,
      deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)
      (Set.Icc 0 U) :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hcomp : (∫ t in Set.Icc 0 U, ∑ i : Fin n,
      deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∂volume) =
      ∫ t in (0 : ℝ)..U,
        remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
          (if riskSet a s t = 0 then 0 else P.hazard a t) := by
    rw [intervalIntegral.integral_of_le hU0, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ((volume.restrict (Set.Icc 0 U)).ae_ne (0 : ℝ))] with t ht htne
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
    rw [← Finset.mul_sum]
    simpa only [x, mul_assoc] using
      deathCPIntegrand_observed_compensator c P hP a s hh ht0
        (by simpa only [U] using ht.2) hDeathPos hNoTies
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
    Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral deathError
  rw [Finset.sum_sub_distrib]
  rw [← integral_finsetSum Finset.univ (fun i _ => hterm i)]
  rw [hcomp]
  apply congrArg (fun z => z - ∫ t in (0 : ℝ)..U,
    remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
      (if riskSet a s t = 0 then 0 else P.hazard a t))
  apply Finset.sum_congr rfl
  intro i _
  simpa only [x, U] using
    deathCPIntegrand_observed_event c P a s hh hh1 hDeathPos hNoTies i

/-- The canonical aggregate death integral is a measurable sample statistic. -/
lemma measurable_deathCPIntegrand_aggregateIntegral (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (deathCPIntegrand c P a h (n := n))
      (1 - h)) := by
  classical
  have hset : MeasurableSet {p : Sample n × ℝ |
      p.2 ∈ Set.Icc (0 : ℝ) (1 - h)} :=
    measurableSet_Icc.preimage measurable_snd
  have hcomp (i : Fin n) : Measurable (fun x : Sample n =>
      ∫ t in Set.Icc 0 (1 - h),
        deathCPIntegrand c P a h t x * referenceDeathHazard P a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x ∂volume) := by
    let e : Sample n × ℝ → ℝ := fun p =>
      deathCPIntegrand c P a h p.2 p.1 * referenceDeathHazard P a p.2 *
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
      (((deathCPIntegrand_jointMeasurable c P hP a hh hh1).comp measurable_swap).mul
        ((measurable_referenceDeathHazard hP a).comp measurable_snd)).mul hrisk
    let g : Sample n × ℝ → ℝ := fun p =>
      if p.2 ∈ Set.Icc (0 : ℝ) (1 - h) then e p else 0
    have hg : Measurable g := he.ite hset measurable_const
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
  exact ((deathCPIntegrand_jointMeasurable c P hP a hh hh1).comp
    (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
      measurable_const |>.sub (hcomp i)

end DeathCP

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
