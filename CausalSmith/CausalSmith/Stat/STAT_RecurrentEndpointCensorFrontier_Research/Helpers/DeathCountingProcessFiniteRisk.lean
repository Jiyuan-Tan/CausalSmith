module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessSecondMomentTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.StoppedKL
public import Causalean.Stat.Sample.Stratified.NestedCountBound

/-! # Finite-sample inverse-risk bounds for the death process

This module turns the iid at-risk count into a binomial reciprocal-count
bound and applies the model's assignment, survival, and retention tails.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

namespace DeathCP

/-- Retaining the inverse-risk factor gives the sharp pathwise energy
domination used for the finite-sample rate. -/
lemma energyDensity_le_target_mul_inverseRisk (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) (h : ℝ) {n : ℕ} (t : ℝ) (x : Sample n)
    (hhaz : 0 ≤ P.hazard a t) :
    (deathCPIntegrand c P a h t x) ^ 2 * P.hazard a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ≤
      (deathTargetWeight c P a h t) ^ 2 * P.hazard a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
  have hkm := pairDeathKMLeft_mem_Icc t x
  have hinv := pairInverseRisk_mem_Icc t x
  have hrisk :=
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_square_risk t x
  have hkmSq : (pairDeathKMLeft t x) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hkm.1 (sub_nonneg.mpr hkm.2)]
  have hweightSq : 0 ≤ (deathTargetWeight c P a h t) ^ 2 := sq_nonneg _
  rw [deathCPIntegrand]
  calc
    _ = (deathTargetWeight c P a h t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
        P.hazard a t *
          ((Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) ^ 2 *
            (∑ i : Fin n,
              Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) := by
      ring
    _ = (deathTargetWeight c P a h t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
        P.hazard a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      rw [hrisk]
    _ ≤ (deathTargetWeight c P a h t) ^ 2 * 1 * P.hazard a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkmSq hweightSq) hhaz) hinv.1
    _ = _ := by ring

/-- At positive study times, assigned-arm follow-up has tail probability equal
to assignment probability times censoring retention. -/
lemma armDeathFailureLaw_real_Ici (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssign : AssignmentLaw P) (a : Arm)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (armDeathFailureLaw P a).real (Set.Ici t) =
      P.p a * retention P a t := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hind : IndepFun LatentSubject.treatment
      (fun z : LatentSubject => z.censor a) P.latent := by
    have h := hRandom.comp measurable_id
      (show Measurable (fun r : (Arm → RecurConfig) ×
        ((Arm → ℝ) × (Arm → ENNReal)) => r.2.2 a) by fun_prop)
    simpa only [Function.comp_def, id_eq] using h
  have hevent : (armDeathFailureTime a) ⁻¹' Set.Ici t =
      LatentSubject.treatment ⁻¹' ({a} : Set Arm) ∩
        (fun z : LatentSubject => z.censor a) ⁻¹' Set.Ici (ENNReal.ofReal t) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    unfold armDeathFailureTime
    by_cases ha : z.treatment = a
    · simp only [if_pos ha]
      rw [censorHorizon_eq_value,
        le_censorHorizonValue_iff (z.censor a) t ht0.le ht1]
      simp [ha]
    · simp [if_neg ha, ha, not_le_of_gt ht0]
  have hprod := hind.measure_inter_preimage_eq_mul
    ({a} : Set Arm) (Set.Ici (ENNReal.ofReal t))
    (MeasurableSet.singleton a) measurableSet_Ici
  rw [armDeathFailureLaw, measureReal_def, Measure.map_apply
    (measurable_armDeathFailureTime a) measurableSet_Ici, hevent, hprod,
    ENNReal.toReal_mul]
  change P.latent.real {z : LatentSubject | z.treatment = a} *
      P.latent.real {z : LatentSubject | ENNReal.ofReal t ≤ z.censor a} = _
  rw [hAssign a]
  rfl

private lemma sampleIndexSet_Ici_prod_card {n : ℕ} (x : Sample n)
    {t : ℝ} (ht : 0 ≤ t) :
    (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x
      (Set.Ici t ×ˢ Set.Ici t)).card =
      Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t x := by
  classical
  unfold Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet
    Causalean.Stat.RecurrentEvent.CountingProcess.riskSet
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Set.mem_prod, Set.mem_Ici]
  change (if t ≤ (x i).1 ∧ t ≤ (x i).2 then 1 else 0) =
    if 0 ≤ t ∧ t ≤ (x i).1 ∧ t ≤ (x i).2 then 1 else 0
  simp [ht]

/-- For iid independent pairs, the expected zero-safe reciprocal at-risk
count is at most twice the reciprocal of sample size times one-subject at-risk
probability. -/
lemma integral_inverseRisk_le_two_div {n : ℕ} (hn : 0 < n)
    (failureLaw deathLaw : Measure ℝ) [IsProbabilityMeasure failureLaw]
    [IsProbabilityMeasure deathLaw] {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q)
    (hprob : q ≤ (failureLaw (Set.Ici t)).toReal *
      (deathLaw (Set.Ici t)).toReal) :
    (∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        failureLaw deathLaw) ≤ 2 / ((n : ℝ) * q) := by
  classical
  let μ := failureLaw.prod deathLaw
  let R : Set (ℝ × ℝ) := Set.Ici t ×ˢ Set.Ici t
  have hR : MeasurableSet R := measurableSet_Ici.prod measurableSet_Ici
  have hμR : (μ R).toReal =
      (failureLaw (Set.Ici t)).toReal * (deathLaw (Set.Ici t)).toReal := by
    dsimp [μ, R]
    change ((failureLaw.prod deathLaw) (Set.Ici t ×ˢ Set.Ici t)).toReal = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hraw :=
    Causalean.Stat.FiniteStratumMarkedRatioMse.integral_nested_count_sq_mul_totalized_inverse_le
      (m := n) μ Set.univ R MeasurableSet.univ hR (Set.subset_univ R) q hq (by
        simpa [hμR] using hprob)
  have hrewrite (x : Sample n) :
      ((Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x Set.univ).card : ℝ) ^ 2 *
          (if 0 < (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x R).card then
            ((Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x R).card : ℝ)⁻¹
          else 0) =
        (n : ℝ) ^ 2 *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
    have hcard :
        (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x Set.univ).card = n := by
      simp [Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet]
    have hrisk := sampleIndexSet_Ici_prod_card x ht
    rw [hcard, hrisk]
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk
    by_cases hz : Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t x = 0
    · simp [hz]
    · simp [hz, Nat.pos_of_ne_zero hz, one_div]
  have hleft :
      (∫ x : Sample n,
          ((Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x Set.univ).card : ℝ) ^ 2 *
            (if 0 < (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x R).card then
              ((Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet x R).card : ℝ)⁻¹
            else 0) ∂Measure.pi (fun _ : Fin n => μ)) =
        (n : ℝ) ^ 2 * ∫ x : Sample n,
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
          ∂Measure.pi (fun _ : Fin n => μ) := by
    simp_rw [hrewrite]
    rw [integral_const_mul]
  rw [hleft] at hraw
  have hμuniv : (μ Set.univ).toReal = 1 := by simp
  rw [hμuniv, mul_one] at hraw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ 2 / ((n : ℝ) * q)
  calc
    _ ≤ (2 * (n : ℝ) / q) / (n : ℝ) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hnR)).2 (by simpa [mul_comm] using hraw)
    _ = 2 / ((n : ℝ) * q) := by field_simp

/-- In the paper's reference product model, the at-risk probability is the
assignment probability times censoring retention times death survival. -/
lemma integral_inverseRisk_le_arm_tail (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      2 / ((n : ℝ) *
        (P.p a * retention P a t * survival P a t)) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hr : 0 < retention P a t :=
    retention_pos_of_modelClass c P hP a t ht0.le ht1
  have hs : 0 < survival P a t := Real.exp_pos _
  apply integral_inverseRisk_le_two_div hn
    (armDeathFailureLaw P a) (referenceDeathLaw P a) ht0.le
    (mul_pos (mul_pos hp hr) hs)
  change P.p a * retention P a t * survival P a t ≤
    (armDeathFailureLaw P a).real (Set.Ici t) *
      (referenceDeathLaw P a).real (Set.Ici t)
  rw [armDeathFailureLaw_real_Ici P hP.randomAssignment hP.assignmentLaw a ht0 ht1.le,
    referenceDeathLaw_real_Ici hP.deathHazard a ⟨ht0.le, ht1.le⟩]

/-- The observed death-error second moment is bounded by the target energy
weighted by the expected reciprocal risk set. -/
lemma deathError_secondMoment_le_expectedInverseRiskEnergy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, (deathError c P a s h) ^ 2 ∂sampleLaw P n) ≤
      ∫ t in Set.Icc 0 (1 - h),
        (deathTargetWeight c P a h t) ^ 2 * P.hazard a t *
          (∫ x : Sample n,
            Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
            ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
              (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∂volume := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 (1 - h))
  let e : Sample n × ℝ → ℝ := fun p =>
    (deathCPIntegrand c P a h p.2 p.1) ^ 2 * referenceDeathHazard P a p.2 *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i p.2 p.1)
  let f : ℝ → ℝ := fun t =>
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t
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
    exact (((deathCPIntegrand_jointMeasurable c P hP a hh hh1).comp
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
    exact deathCPIntegrand_quadraticEnergyFinite c P hP a hh hh1
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
      rw [abs_of_nonneg
        (pairInverseRisk_mem_Icc t x).1]
      exact (pairInverseRisk_mem_Icc t x).2
    constructor
    · exact integral_nonneg fun x =>
        (pairInverseRisk_mem_Icc t x).1
    · simpa using integral_mono hi (integrable_const 1) (fun x =>
        (pairInverseRisk_mem_Icc t x).2)
  have hf : Integrable f ν :=
    deathTargetWeight_sq_hazard_integrableOn c P hP a hh hh1
  have hfr : Integrable (fun t => f t * r t) ν := by
    apply hf.mono' (hf.aestronglyMeasurable.mul hrMeas.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change |f t * r t| ≤ f t
    dsimp only [f]
    rw [abs_of_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _)
        (c.dMin_pos.le.trans (hP.deathBounds a t
          ⟨ht.1, ht.2.trans (by linarith)⟩).1)) (hrBounds t).1)]
    exact mul_le_of_le_one_right
      (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans
        (hP.deathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1))
      (hrBounds t).2
  rw [deathError_secondMoment_eq_predictableEnergy c P hP a n hh hh1]
  change (∫ x : Sample n, ∫ t : ℝ, e (x, t) ∂ν ∂μ) ≤
    ∫ t : ℝ, f t * r t ∂ν
  rw [integral_integral_swap heInt]
  apply integral_mono_ae heInt.integral_prod_right hfr
  filter_upwards [heInt.prod_left_ae,
    ae_restrict_mem measurableSet_Icc] with t het ht
  have hconst : Integrable (fun x : Sample n => f t *
      Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) μ := by
    exact (Integrable.of_bound
      (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1 (by
          filter_upwards [] with x
          change |Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x| ≤ 1
          rw [abs_of_nonneg
            (pairInverseRisk_mem_Icc t x).1]
          exact (pairInverseRisk_mem_Icc t x).2)).const_mul (f t)
  calc
    (∫ x : Sample n, e (x, t) ∂μ) ≤
        ∫ x : Sample n, f t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∂μ := by
      apply integral_mono het hconst
      intro x
      dsimp [e, f]
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (by linarith)⟩
      rw [referenceDeathHazard_eq P a htI]
      exact energyDensity_le_target_mul_inverseRisk c P a h t x
        (c.dMin_pos.le.trans (hP.deathBounds a t htI).1)
    _ = f t * r t := by rw [integral_const_mul]

/-- The finite-horizon death-rate energy is integrable when the estimation
bandwidth is positive. -/
lemma deathRateEnergy_integrableOn (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    IntegrableOn (fun t =>
      (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
        (retention P a t * survival P a t)) (Set.Icc 0 (1 - h)) := by
  let U := 1 - h
  change Integrable (fun t =>
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
      (retention P a t * survival P a t))
    ((volume : Measure ℝ).restrict (Set.Icc 0 U))
  have hU0 : (0 : ℝ) ≤ U := by dsimp [U]; linarith
  have hU1 : U < 1 := by dsimp [U]; linarith
  have hrU : 0 < retention P a U :=
    retention_pos_of_modelClass c P hP a U hU0 hU1
  have hs0 : 0 < Real.exp (-c.dMax) := Real.exp_pos _
  obtain ⟨C, hC0, hC⟩ := exists_deathTargetWeight_bound c P hP a hh.le hh1
  have hhazI : IntervalIntegrable (P.hazard a) volume 0 U :=
    (hP.deathHazard.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hU0]
      exact Set.Icc_subset_Icc le_rfl hU1.le)
  have hhaz : IntegrableOn (P.hazard a) (Set.Icc 0 U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at hhazI
  have hmul : Integrable (fun t =>
      ((deathTargetWeight c P a h t) ^ 2 /
        (retention P a t * survival P a t)) * P.hazard a t)
      ((volume : Measure ℝ).restrict (Set.Icc 0 U)) := by
    refine hhaz.bdd_mul (c := C ^ 2 /
      (retention P a U * Real.exp (-c.dMax))) ?_ ?_
    · have htarg : AEStronglyMeasurable
          (fun t => (deathTargetWeight c P a h t) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Icc 0 U)) :=
        ((continuousOn_deathTargetWeight c P hP a hh.le hh1).pow 2).aestronglyMeasurable
          measurableSet_Icc
      have hret : AEStronglyMeasurable (retention P a)
          ((volume : Measure ℝ).restrict (Set.Icc 0 U)) :=
        (measurable_retention P a).aestronglyMeasurable
      have hsurv : AEStronglyMeasurable (survival P a)
          ((volume : Measure ℝ).restrict (Set.Icc 0 U)) :=
        ((modelClass_survival_continuousOn c P hP a).mono
        (Set.Icc_subset_Icc le_rfl hU1.le)).aestronglyMeasurable measurableSet_Icc
      change AEStronglyMeasurable
        ((fun t => (deathTargetWeight c P a h t) ^ 2) *
          (retention P a * survival P a)⁻¹)
        ((volume : Measure ℝ).restrict (Set.Icc 0 U))
      exact htarg.mul (hret.mul hsurv).inv₀
    · show ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc 0 U),
        ‖(deathTargetWeight c P a h t) ^ 2 /
          (retention P a t * survival P a t)‖ ≤
            C ^ 2 / (retention P a U * Real.exp (-c.dMax))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hr : retention P a U ≤ retention P a t :=
        (retention_antitone P a) ht.2
      have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a
        ⟨ht.1, ht.2.trans hU1.le⟩).1
      have hden : 0 < retention P a t * survival P a t :=
        mul_pos (hrU.trans_le hr) (hs0.trans_le hs)
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
      calc
        _ ≤ C ^ 2 / (retention P a t * survival P a t) := by
          gcongr
          exact hC t (by simpa only [U] using ht)
        _ ≤ C ^ 2 / (retention P a U * Real.exp (-c.dMax)) := by
          apply div_le_div_of_nonneg_left (sq_nonneg C)
            (mul_pos hrU hs0)
          exact mul_le_mul hr hs hs0.le (hrU.trans_le hr).le
  simpa only [U, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The death error has the parametric `1/n` factor times the paper's
survival-retention weighted death energy. -/
lemma deathError_secondMoment_le_finiteRateEnergy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, (deathError c P a s h) ^ 2 ∂sampleLaw P n) ≤
      (2 / ((n : ℝ) * c.pMin)) *
        ∫ t in Set.Icc 0 (1 - h),
          (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
            (retention P a t * survival P a t) ∂volume := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 (1 - h))
  let r : ℝ → ℝ := fun t => ∫ x : Sample n,
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∂μ
  let f : ℝ → ℝ := fun t =>
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t
  let k : ℝ → ℝ := fun t => f t / (retention P a t * survival P a t)
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
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
    have hle := integral_mono hi (integrable_const 1)
      (fun x => (pairInverseRisk_mem_Icc t x).2)
    exact ⟨integral_nonneg (fun x => (pairInverseRisk_mem_Icc t x).1),
      by simpa [r] using hle⟩
  have hf : Integrable f ν :=
    deathTargetWeight_sq_hazard_integrableOn c P hP a hh.le hh1
  have hfr : Integrable (fun t => f t * r t) ν := by
    apply hf.mono' (hf.aestronglyMeasurable.mul hrMeas.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hf0 : 0 ≤ f t := mul_nonneg (sq_nonneg _)
      (c.dMin_pos.le.trans
        (hP.deathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
    change |f t * r t| ≤ f t
    rw [abs_of_nonneg (mul_nonneg hf0 (hrBounds t).1)]
    exact mul_le_of_le_one_right hf0 (hrBounds t).2
  have hk : Integrable k ν :=
    deathRateEnergy_integrableOn c P hP a hh hh1
  calc
    _ ≤ ∫ t : ℝ, f t * r t ∂ν :=
      deathError_secondMoment_le_expectedInverseRiskEnergy
        c P hP a n hh.le hh1
    _ ≤ ∫ t : ℝ, (2 / ((n : ℝ) * c.pMin)) * k t ∂ν := by
      apply integral_mono_ae hfr (hk.const_mul (2 / ((n : ℝ) * c.pMin)))
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ((volume.restrict (Set.Icc 0 (1 - h))).ae_ne (0 : ℝ))] with t ht htne
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have ht1 : t < 1 := ht.2.trans_lt (by linarith)
      have hinv := integral_inverseRisk_le_arm_tail c P hP a hn ht0 ht1
      have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
      have hr : 0 < retention P a t :=
        retention_pos_of_modelClass c P hP a t ht0.le ht1
      have hs : 0 < survival P a t := Real.exp_pos _
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hf0 : 0 ≤ f t := mul_nonneg (sq_nonneg _)
        (c.dMin_pos.le.trans
          (hP.deathBounds a t ⟨ht.1, ht1.le⟩).1)
      calc
        f t * r t ≤ f t *
            (2 / ((n : ℝ) * (P.p a * retention P a t * survival P a t))) :=
          mul_le_mul_of_nonneg_left hinv hf0
        _ ≤ f t *
            (2 / ((n : ℝ) * (c.pMin * retention P a t * survival P a t))) := by
          apply mul_le_mul_of_nonneg_left _ hf0
          apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
          · exact mul_pos hnR (mul_pos (mul_pos c.pMin_pos hr) hs)
          · gcongr
            exact hP.treatmentOverlap a
        _ = (2 / ((n : ℝ) * c.pMin)) * k t := by
          dsimp [k]
          field_simp
    _ = (2 / ((n : ℝ) * c.pMin)) * ∫ t : ℝ, k t ∂ν := by
      rw [integral_const_mul]
    _ = _ := rfl

end DeathCP

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
