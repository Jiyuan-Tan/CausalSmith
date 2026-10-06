module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleIntegratedEnergy

/-!
# KM second-mean consistency throughout the positive-retention horizon

Roadmap (19)--(24): extend the dependent oracle energy bound to every study
time, including time one, and control the integrated observable KM error.
The benchmark assumptions require no endpoint smoothness.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- Null-set changes of the hazard preserve compensation at any study time. -/
-- @node: positiveRetention_referenceHazard_at_aggregateIntegral_eq
lemma positiveRetention_referenceHazard_at_aggregateIntegral_eq (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) {n : ℕ} (T : ℝ)
    (H : ℝ → Sample n → ℝ) (x : Sample n) :
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (positiveRetention_referenceHazard P hDeath a) H T x =
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) H T x := by
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
  apply Finset.sum_congr rfl
  intro i _
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [(positiveRetention_referenceHazard_ae_eq_global P hDeath a).restrict
    (s := Icc (0 : ℝ) T)] with t ht
  rw [ht]

/-- The oracle energy bound holds at every study time, with a common constant. -/
-- @node: positiveRetention_kmOracle_at_secondMoment_le_inv_sampleSize
lemma positiveRetention_kmOracle_at_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      (2 * (Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (s := Icc (0 : ℝ) T)
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
    c P hDeath hDeathBounds a hT0 hT1
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
    have heq := (positiveRetention_referenceHazard_ae_eq_global P hDeath a).restrict (s := Icc (0 : ℝ) T)
    calc
      _ ≤ ∫ _t, (Real.exp c.dMax) ^ 2 * c.dMax ∂ν := by
        apply integral_mono_ae hf (integrable_const _)
        filter_upwards [heq, ae_restrict_mem measurableSet_Icc] with t ht htmem
        dsimp [f]
        rw [ht, referenceDeathHazard_eq P a ⟨htmem.1, htmem.2.trans hT1⟩]
        exact mul_le_mul_of_nonneg_left (hDeathBounds a t ⟨htmem.1, htmem.2.trans hT1⟩).2 (sq_nonneg _)
      _ = ((Real.exp c.dMax) ^ 2 * c.dMax) * T := by
        simp [ν, Real.volume_Icc, hT0, mul_comm]
      _ ≤ ((Real.exp c.dMax) ^ 2 * c.dMax) * 1 :=
        mul_le_mul_of_nonneg_left hT1 (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans c.dMin_lt.le))
      _ = _ := mul_one _
  calc
    _ ≤ ∫ t, f t * r t ∂ν :=
      positiveRetention_kmOracle_aggregate_secondMoment_le_expectedInverseRisk
        c P hDeath hDeathBounds a n hT0 hT1
    _ ≤ ∫ t, C * f t ∂ν := by
      apply integral_mono_ae hfr (hf.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (ν.ae_ne (0 : ℝ))] with t ht htne
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hb := positiveRetention_reference_inverseRisk_le c P hRandom hAssignment
        hOverlap hDeath hDeathBounds hHorizon a hn ht0 (ht.2.trans hT1)
      simpa only [r, μ, C, mul_comm] using mul_le_mul_of_nonneg_left hb (hf0 t)
    _ = C * ∫ t, f t ∂ν := integral_const_mul _ _
    _ ≤ C * ((Real.exp c.dMax) ^ 2 * c.dMax) :=
      mul_le_mul_of_nonneg_left hint hC
    _ = _ := by dsimp [C]; ring


/-- Observed histories inherit the common oracle bound at every time. -/
-- @node: positiveRetention_observedKMOracle_at_secondMoment_le_inv_sampleSize
lemma positiveRetention_observedKMOracle_at_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ s : Fin n → ObsHistory,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (positiveRetention_referenceHazard P hDeath a) (kmOracleIntegrand P a T) T
        (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) ≤
      (2 * (Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  rw [positiveRetention_observedDeathSample_oracleAggregate_secondMoment_eq_reference
    c P hDeath hDeathBounds hRandom hCensor a n hT0 hT1]
  exact positiveRetention_kmOracle_at_secondMoment_le_inv_sampleSize c P hRandom
    hAssignment hOverlap hDeath hDeathBounds hHorizon a hn hT0 hT1


/-- The second moment at any time is bounded by oracle energy and extinction. -/
-- @node: positiveRetention_deathKM_at_secondMoment_le_oracleAggregate_add_emptyRisk
lemma positiveRetention_deathKM_at_secondMoment_le_oracleAggregate_add_emptyRisk
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ s : Fin n → ObsHistory,
      (deathKM a s T - survival P a T) ^ 2 ∂sampleLaw P n) ≤
      (∫ s : Fin n → ObsHistory,
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
          (observedDeathSample a s)) ^ 2 ∂sampleLaw P n) +
      (sampleLaw P n).real {s | riskSet a s T = 0} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E : Set (Fin n → ObsHistory) := {s | riskSet a s T = 0}
  let J : (Fin n → ObsHistory) → ℝ := fun s =>
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (kmOracleIntegrand P a T) T
      (observedDeathSample a s)
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun
      ((measurable_recurrenceRiskSet_joint a).comp
        (measurable_id.prodMk measurable_const)) measurable_const
  have hJ : Integrable (fun s => J s ^ 2) (sampleLaw P n) := by
    have hi := positiveRetention_observedDeathSample_oracleAggregate_sq_integrable
        c P hDeath hDeathBounds hRandom hCensor a n (T := T) hT0 hT1
    simpa only [J, positiveRetention_referenceHazard_at_aggregateIntegral_eq] using hi
  have hR : Integrable (fun s => J s ^ 2 + E.indicator (fun _ => 1) s)
      (sampleLaw P n) := hJ.add ((integrable_const 1).indicator hE)
  calc
    _ ≤ ∫ s, J s ^ 2 + E.indicator (fun _ => 1) s ∂sampleLaw P n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        hR (by
          filter_upwards [positiveRetention_deathKM_error_sq_le_oracleAggregate_sq_add_emptyRisk_ae
            c P hDeath hDeathBounds a n (T := T) hT0 hT1] with s hs
          by_cases hz : riskSet a s T = 0
          · simpa [J, E, hz] using hs
          · simpa [J, E, hz] using hs)
    _ = (∫ s, J s ^ 2 ∂sampleLaw P n) +
        ∫ s, E.indicator (fun _ => 1) s ∂sampleLaw P n := integral_add hJ
          ((integrable_const 1).indicator hE)
    _ = _ := by
      rw [integral_indicator_const 1 hE]
      simp [J, E]


/-- Second-mean consistency holds at every time through the endpoint. -/
-- @node: positiveRetention_deathKM_at_secondMoment_tendsto_zero
lemma positiveRetention_deathKM_at_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (deathKM a s T - survival P a T) ^ 2 ∂sampleLaw P n)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let C : ℝ := 2 * (Real.exp c.dMax) ^ 2 * c.dMax /
    (c.pMin * Real.exp (-c.dMax) * c.Ghor)
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Pi.inv_apply] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C
  have hempty := positiveRetention_terminal_emptyRisk_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
  apply squeeze_zero' (Eventually.of_forall (fun _ =>
    integral_nonneg (fun _ => sq_nonneg _))) _
    (by simpa only [add_zero] using hlim.add hempty)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := positiveRetention_observedKMOracle_at_secondMoment_le_inv_sampleSize
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
    (n := n) (by omega) hT.1 hT.2
  simp only [positiveRetention_referenceHazard_at_aggregateIntegral_eq] at hb
  exact (positiveRetention_deathKM_at_secondMoment_le_oracleAggregate_add_emptyRisk
    c P hDeath hDeathBounds hRandom hCensor a n hT.1 hT.2).trans (add_le_add hb (by
      apply measureReal_mono _ (by finiteness)
      intro s hs
      change riskSet a s T = 0 at hs
      change riskSet a s 1 = 0
      have hle : riskSet a s 1 ≤ riskSet a s T := by
        unfold riskSet
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨hi.1, hT.2.trans hi.2⟩
      omega))

/-- At deterministic times the KM left limit has the same second-mean limit. -/
-- @node: positiveRetention_deathKMLeft_at_secondMoment_tendsto_zero
lemma positiveRetention_deathKMLeft_at_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (deathKMLeft a s T - survival P a T) ^ 2 ∂sampleLaw P n)
      atTop (nhds 0) := by
  have heq (n : ℕ) : (∫ s : Fin n → ObsHistory,
      (deathKMLeft a s T - survival P a T) ^ 2 ∂sampleLaw P n) =
      ∫ s : Fin n → ObsHistory,
        (deathKM a s T - survival P a T) ^ 2 ∂sampleLaw P n := by
    apply integral_congr_ae
    filter_upwards [deathKMLeft_eq_deathKM_ae_fixed P hDeath a n T] with s hs
    rw [hs]
  simp only [heq]
  exact positiveRetention_deathKM_at_secondMoment_tendsto_zero c P hRandom
    hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a hT

/-- Joint integrability permits exchanging observed-sample and time integrals. -/
-- @node: positiveRetention_deathKMLeft_error_sq_integrable_prod
lemma positiveRetention_deathKMLeft_error_sq_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm)
    (n : ℕ) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (positiveRetention_survival_continuousOn P hDeath a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - g p.2) ^ 2) :=
    ((measurable_recurrenceDeathKMLeft_joint a).sub (hg.comp measurable_snd)).pow_const 2
  have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1)), p.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  have heq : (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - g p.2) ^ 2) =ᵐ[
        (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))]
      (fun p => (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2) := by
    filter_upwards [htprod] with p hp
    simp only [g, Set.piecewise, if_pos hp]
  apply Integrable.congr _ heq
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [htprod] with p hp
  simp only [g, Set.piecewise, if_pos hp, Real.norm_eq_abs, abs_pow, sq_abs]
  have hk := deathKMLeft_mem_Icc a p.1 p.2
  have hs := survival_bounds_of_deathBounds c P hDeathBounds a hp
  nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]


/-- The actual observable KM error vanishes in integrated second mean. -/
-- @node: positiveRetention_deathKMLeft_integrated_error_secondMoment_tendsto_zero
lemma positiveRetention_deathKMLeft_integrated_error_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1, (deathKMLeft a s t - survival P a t) ^ 2)
      ∂sampleLaw P n) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hi (n : ℕ) := positiveRetention_deathKMLeft_error_sq_integrable_prod c P hDeath hDeathBounds a n
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (F := fun n t => ∫ s : Fin n → ObsHistory,
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => (hi n).integral_prod_right.aestronglyMeasurable) (integrable_const 1)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Icc, (hi n).prod_left_ae] with t ht hit
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
      calc
        _ ≤ ∫ _s : Fin n → ObsHistory, (1 : ℝ) ∂sampleLaw P n := by
          apply integral_mono hit (integrable_const 1)
          intro s
          have hk := deathKMLeft_mem_Icc a s t
          have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
          nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
        _ = 1 := by simp)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact positiveRetention_deathKMLeft_at_secondMoment_tendsto_zero c P hRandom
        hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a ht)
  simp only [integral_zero] at h
  convert h using 1
  funext n
  exact integral_integral_swap (hi n)


/-- Markov's inequality turns integrated second mean into vanishing energy
in probability for the observable left-limit KM error. -/
-- @node: positiveRetention_deathKMLeft_integrated_error_probability_tendsto_zero
lemma positiveRetention_deathKMLeft_integrated_error_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1,
        (deathKMLeft a s t - survival P a t) ^ 2}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hlim := (positiveRetention_deathKMLeft_integrated_error_secondMoment_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).div_const ε
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [zero_div] using hlim)
  intro n
  have hi := (positiveRetention_deathKMLeft_error_sq_integrable_prod
    c P hDeath hDeathBounds a n).integral_prod_left
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory =>
      integral_nonneg (fun _ => sq_nonneg _))) hi ε
  apply (le_div_iff₀ hε).2
  have hsub : {s : Fin n → ObsHistory | ε < ∫ t in Icc (0 : ℝ) 1,
        (deathKMLeft a s t - survival P a t) ^ 2} ⊆
      {s | ε ≤ ∫ t in Icc (0 : ℝ) 1,
        (deathKMLeft a s t - survival P a t) ^ 2} := by
    intro s hs
    exact (show ε < ∫ t in Icc (0 : ℝ) 1,
      (deathKMLeft a s t - survival P a t) ^ 2 from hs).le
  exact (mul_le_mul_of_nonneg_right (measureReal_mono hsub (by finiteness))
    hε.le).trans (by simpa only [mul_comm] using hm)

/-- Each observed path has a time-integrable squared KM error. -/
-- @node: positiveRetention_deathKMLeft_error_sq_integrable_time
lemma positiveRetention_deathKMLeft_error_sq_integrable_time
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) :
    IntegrableOn (fun t => (deathKMLeft a s t - survival P a t) ^ 2)
      (Icc (0 : ℝ) 1) := by
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (positiveRetention_survival_continuousOn P hDeath a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hm : Measurable (fun t => (deathKMLeft a s t - g t) ^ 2) := by
    exact ((measurable_deathKMLeft a s).sub hg).pow_const 2
  have heq : (fun t => (deathKMLeft a s t - g t) ^ 2) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun t => (deathKMLeft a s t - survival P a t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [g, ht]
  apply Integrable.congr _ heq
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [g, Set.piecewise, if_pos ht, Real.norm_eq_abs, abs_pow, sq_abs]
  have hk := deathKMLeft_mem_Icc a s t
  have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
  nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]

/-- Full-horizon denominator localization upgrades integrated KM consistency
to the inverse-risk weighted energy used in observable oracle replacement. -/
-- @node: positiveRetention_deathKMLeft_scaledInvRisk_error_probability_tendsto_zero
lemma positiveRetention_deathKMLeft_scaledInvRisk_error_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1,
        ((n : ℝ) * invRisk a s t) * (deathKMLeft a s t - survival P a t) ^ 2})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let K := (c.pMin * Real.exp (-c.dMax) * c.Ghor / 2)⁻¹
  have hK : 0 < K := inv_pos.mpr (half_pos
    (mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos))
  have hlim := (positiveRetention_uniform_scaledInvRisk_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).add
    (positiveRetention_deathKMLeft_integrated_error_probability_tendsto_zero
      c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
      (div_pos hε hK))
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [add_zero] using hlim)
  intro n
  let B : Set (Fin n → ObsHistory) := {s | ∃ t ≤ (1 : ℝ), K < (n : ℝ) * invRisk a s t}
  let E : Set (Fin n → ObsHistory) := {s | ε / K < ∫ t in Icc (0 : ℝ) 1,
    (deathKMLeft a s t - survival P a t) ^ 2}
  apply (measureReal_mono (s₂ := B ∪ E) ?_ (by finiteness)).trans (measureReal_union_le B E)
  intro s hs
  by_cases hb : s ∈ B
  · exact Or.inl hb
  · right
    have hbound (t : ℝ) (ht : t ≤ 1) : (n : ℝ) * invRisk a s t ≤ K := by
      exact le_of_not_gt (fun h => hb ⟨t, ht, h⟩)
    have hi := positiveRetention_deathKMLeft_error_sq_integrable_time c P hDeath hDeathBounds a s
    have hw : (∫ t in Icc (0 : ℝ) 1,
        ((n : ℝ) * invRisk a s t) * (deathKMLeft a s t - survival P a t) ^ 2) ≤
        K * ∫ t in Icc (0 : ℝ) 1,
          (deathKMLeft a s t - survival P a t) ^ 2 := by
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg _ (hi.const_mul K) _
      · filter_upwards [] with t
        apply mul_nonneg _ (sq_nonneg _)
        unfold invRisk
        split_ifs <;> positivity
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact mul_le_mul_of_nonneg_right (hbound t ht.2) (sq_nonneg _)
    change ε / K < _
    exact (div_lt_iff₀ hK).2 (by simpa only [mul_comm] using hs.trans_le hw)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
