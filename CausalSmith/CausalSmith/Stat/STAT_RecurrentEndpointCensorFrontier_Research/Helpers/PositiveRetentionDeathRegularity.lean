module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessFiniteRisk

/-!
# Death integrand regularity for the positive-retention benchmark

Roadmap (6), (8), and (9): the deterministic death multiplier is continuous,
measurable, bounded, and has finite quadratic energy using only the benchmark
hazard assumptions. Endpoint Hölder regularity is unnecessary.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Absolute continuity of the cumulative death hazard suffices for survival continuity. -/
-- @node: positiveRetention_survival_continuousOn
lemma positiveRetention_survival_continuousOn (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) :
    ContinuousOn (survival P a) (Icc (0 : ℝ) 1) := by
  have hprim : ContinuousOn
      (fun t : ℝ => ∫ u in (0 : ℝ)..t, P.hazard a u) (Icc (0 : ℝ) 1) := by
    simpa using intervalIntegral.continuousOn_primitive_interval'
      (a := (0 : ℝ)) (hDeath.1 a) (by norm_num : (0 : ℝ) ∈ Set.uIcc 0 1)
  exact Real.continuous_exp.comp_continuousOn hprim.neg

-- @node: positiveRetention_continuousOn_deathTargetWeight
lemma positiveRetention_continuousOn_deathTargetWeight (c : ClassConstants) (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ContinuousOn (deathTargetWeight c P a h) (Set.Icc 0 (1 - h)) := by
  let U : ℝ := 1 - h
  let target : ℝ → ℝ := fun t => continuationWeight (holderOrder c) h t *
    survival P a t * P.lam a t
  have hU0 : 0 ≤ U := by dsimp [U]; linarith
  have htarget : IntervalIntegrable target volume 0 U := by
    simpa only [target] using weightedTarget_intervalIntegrable c P
      hPoisson hDeath hDeathBounds a hh hU0
      (by dsimp [U]; linarith)
  have htargetOn : IntegrableOn target (Set.Icc (0 : ℝ) U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at htarget
  have hremaining : ContinuousOn (remainingTarget c P a h) (Set.Icc 0 U) := by
    change ContinuousOn (fun t => ∫ u in t..U, target u) (Set.Icc 0 U)
    simpa only [Set.uIcc_of_le hU0] using
      (intervalIntegral.continuousOn_primitive_interval_left
        (a := (0 : ℝ)) (b := U) (by
          simpa only [Set.uIcc_of_le hU0] using htargetOn))
  have hsurvival : ContinuousOn (survival P a) (Set.Icc 0 U) :=
    (positiveRetention_survival_continuousOn P hDeath a).mono
      (Set.Icc_subset_Icc le_rfl (by dsimp [U]; linarith))
  have hratio : ContinuousOn
      (fun t => remainingTarget c P a h t / survival P a t) (Set.Icc 0 U) :=
    hremaining.div hsurvival (fun t _ => (Real.exp_pos _).ne')
  apply hratio.congr
  intro t ht
  simp [deathTargetWeight, show t ∈ Set.Icc (0 : ℝ) (1 - h) by
    simpa only [U] using ht]

/-- On a valid horizon the extended death target weight is measurable. -/
-- @node: positiveRetention_measurable_deathTargetWeight
lemma positiveRetention_measurable_deathTargetWeight (c : ClassConstants) (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (deathTargetWeight c P a h) := by
  let U : ℝ := 1 - h
  let target : ℝ → ℝ := fun t => continuationWeight (holderOrder c) h t *
    survival P a t * P.lam a t
  have hU0 : 0 ≤ U := by dsimp [U]; linarith
  have htarget : IntervalIntegrable target volume 0 U := by
    simpa only [target] using weightedTarget_intervalIntegrable c P
      hPoisson hDeath hDeathBounds a hh hU0
      (by dsimp [U]; linarith)
  have htargetOn : IntegrableOn target (Set.Icc (0 : ℝ) U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at htarget
  have htargetU : IntegrableOn target (Set.uIcc (0 : ℝ) U) := by
    simpa only [Set.uIcc_of_le hU0] using htargetOn
  have hremaining : ContinuousOn (remainingTarget c P a h) (Set.Icc (0 : ℝ) U) := by
    change ContinuousOn (fun t => ∫ u in t..U, target u) (Set.Icc (0 : ℝ) U)
    simpa only [Set.uIcc_of_le hU0] using
      (intervalIntegral.continuousOn_primitive_interval_left
        (a := (0 : ℝ)) (b := U) htargetU)
  have hsurvival : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) U) :=
    (positiveRetention_survival_continuousOn P hDeath a).mono
      (Set.Icc_subset_Icc le_rfl (by dsimp [U]; linarith))
  have hratio : ContinuousOn
      (fun t => remainingTarget c P a h t / survival P a t)
      (Set.Icc (0 : ℝ) U) :=
    hremaining.div hsurvival (fun t _ => (Real.exp_pos _).ne')
  unfold deathTargetWeight
  exact hratio.measurable_piecewise continuousOn_const measurableSet_Icc

/-- The actual predictable coefficient is measurable without endpoint assumptions. -/
-- @node: positiveRetention_deathCPIntegrand_jointMeasurable
lemma positiveRetention_deathCPIntegrand_jointMeasurable (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) {n : ℕ} :
    Measurable (fun p : ℝ × Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
      deathCPIntegrand c P a h p.1 p.2) := by
  unfold deathCPIntegrand
  exact (((positiveRetention_measurable_deathTargetWeight c P hPoisson hDeath
    hDeathBounds a hh hh1).comp measurable_fst).mul
    pairDeathKMLeft_jointMeasurable).mul
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable

/-- Roadmap (8) gives an explicit envelope for the ordinary death multiplier. -/
-- @node: positiveRetention_deathTargetWeight_zero_abs_le
lemma positiveRetention_deathTargetWeight_zero_abs_le (c : ClassConstants)
    (P : SubjectLaw) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (t : ℝ) :
    |deathTargetWeight c P a 0 t| ≤ c.lambdaMax * Real.exp c.dMax := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
    have hinv : (survival P a t)⁻¹ ≤ Real.exp c.dMax := by
      calc
        _ ≤ (Real.exp (-c.dMax))⁻¹ :=
          (inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _)).2 hs.1
        _ = _ := by rw [Real.exp_neg]; simp
    rw [deathTargetWeight, if_pos (by simpa using ht), abs_div,
      abs_of_pos (show 0 < survival P a t from Real.exp_pos _), div_eq_mul_inv]
    have hr := positiveRetention_remainingTarget_zero_abs_le c P hRecurBounds hDeathBounds a ht
    have hr' : |remainingTarget c P a 0 t| ≤ c.lambdaMax := by
      have hl : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
      nlinarith [ht.1]
    exact mul_le_mul hr' hinv (inv_nonneg.mpr (Real.exp_pos _).le)
      (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  · simp [deathTargetWeight, ht, mul_nonneg
      (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) (Real.exp_pos _).le]

/-- The ordinary target energy is integrable under the benchmark assumptions. -/
-- @node: positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn
lemma positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) :
    IntegrableOn (fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) := by
  have hd : IntegrableOn (P.hazard a) (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hDeath.1 a)
  apply hd.bdd_mul
  · exact ((positiveRetention_measurable_deathTargetWeight c P hPoisson hDeath
      hDeathBounds a (by norm_num) (by norm_num)).pow_const 2).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (positiveRetention_deathTargetWeight_zero_abs_le c P hRecurBounds hDeathBounds a t) 2

-- @node: positiveRetention_deathCPIntegrand_zero_quadraticEnergyFinite
lemma positiveRetention_deathCPIntegrand_zero_quadraticEnergyFinite (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ} :
    Causalean.Stat.RecurrentEvent.CountingProcess.QuadraticEnergyFinite
      (armDeathFailureLaw P a) (referenceDeathLaw P a)
      (referenceDeathHazard P a) (deathCPIntegrand c P a 0 (n := n))
      (1 : ℝ) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 (1 : ℝ))
  let f : ℝ → ℝ := fun t =>
    (deathTargetWeight c P a 0 t) ^ 2 * P.hazard a t
  have hf : Integrable f ν :=
    positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn c P hPoisson hDeath hRecurBounds hDeathBounds a
  have hf0 : ∀ᵐ t ∂ν, 0 ≤ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _)
      (c.dMin_pos.le.trans
        (hDeathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
  have hinner (x : DeathCP.Sample n) :
      (∫⁻ t, ENNReal.ofReal
        ((deathCPIntegrand c P a 0 t x) ^ 2 * referenceDeathHazard P a t *
          (∑ i : Fin n,
            Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν) ≤
        ENNReal.ofReal (∫ t, f t ∂ν) := by
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (f t) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        apply ENNReal.ofReal_le_ofReal
        rw [referenceDeathHazard_eq P a ⟨ht.1, ht.2.trans (by linarith)⟩]
        exact DeathCP.energyDensity_le c P a 0 t x
          (c.dMin_pos.le.trans
            (hDeathBounds a t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
      _ = ENNReal.ofReal (∫ t, f t ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hf hf0).symm
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.QuadraticEnergyFinite
  change (∫⁻ x : DeathCP.Sample n, ∫⁻ t, ENNReal.ofReal
    ((deathCPIntegrand c P a 0 t x) ^ 2 * referenceDeathHazard P a t *
      (∑ i : Fin n,
        Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) ∂ν ∂μ) ≠ ⊤
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫⁻ _x : DeathCP.Sample n, ENNReal.ofReal (∫ t, f t ∂ν) ∂μ :=
      lintegral_mono hinner
    _ = ENNReal.ofReal (∫ t, f t ∂ν) := by simp


/-- On actual observed samples the ordinary predictable death energy retains
inverse risk; integrating that factor yields the benchmark parametric rate. -/
-- @node: positiveRetention_observed_deathEnergy_zero_le_inv_sampleSize
lemma positiveRetention_observed_deathEnergy_zero_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0) 1
        (observedDeathSample a s) ∂sampleLaw P n) ≤
      (2 * (c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let B := (c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _)
    (c.dMin_pos.le.trans c.dMin_lt.le)
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ => invRisk a p.1 p.2)
      ((sampleLaw P n).prod ν) := by
    apply Integrable.of_bound (measurable_recurrenceInvRisk_joint a).aestronglyMeasurable 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (recurrence_invRisk_mem_Icc a p.1 p.2).1]
    exact (recurrence_invRisk_mem_Icc a p.1 p.2).2
  have hpoint (s : Fin n → ObsHistory) :
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a 0) 1
        (observedDeathSample a s) ≤ B * ∫ t, invRisk a s t ∂ν := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
    rw [integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    have hsI : Integrable (fun t => invRisk a s t) ν := by
      apply Integrable.of_bound
        ((measurable_recurrenceInvRisk_joint a).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      filter_upwards [] with t
      change ‖invRisk a s t‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
      exact (recurrence_invRisk_mem_Icc a s t).2
    apply integral_mono_of_nonneg _ (hsI.const_mul B)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [referenceDeathHazard_eq P a ⟨ht.1.le, ht.2⟩]
      calc
        _ ≤ deathTargetWeight c P a 0 t ^ 2 * P.hazard a t *
            Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t
              (observedDeathSample a s) :=
          DeathCP.energyDensity_le_target_mul_inverseRisk c P a 0 t _
            (c.dMin_pos.le.trans (hDeathBounds a t ⟨ht.1.le, ht.2⟩).1)
        _ ≤ B * invRisk a s t := by
          rw [observedDeathSample_inverseRisk a s ht.1]
          apply mul_le_mul_of_nonneg_right _ (recurrence_invRisk_mem_Icc a s t).1
          apply mul_le_mul _ (hDeathBounds a t ⟨ht.1.le, ht.2⟩).2
            (c.dMin_pos.le.trans (hDeathBounds a t ⟨ht.1.le, ht.2⟩).1) (sq_nonneg _)
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
            (mul_nonneg (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
              (Real.exp_pos _).le)).2
            (positiveRetention_deathTargetWeight_zero_abs_le c P hRecurBounds hDeathBounds a t)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [referenceDeathHazard_eq P a ⟨ht.1.le, ht.2⟩]
      exact mul_nonneg (mul_nonneg (sq_nonneg _)
        (c.dMin_pos.le.trans (hDeathBounds a t ⟨ht.1.le, ht.2⟩).1))
        (Finset.sum_nonneg (fun i _ => by
          unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
          split_ifs <;> norm_num))
  calc
    _ ≤ ∫ s : Fin n → ObsHistory, B * ∫ t, invRisk a s t ∂ν ∂sampleLaw P n :=
      integral_mono_of_nonneg (by
        filter_upwards [] with s
        unfold Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [referenceDeathHazard_eq P a ht]
        exact mul_nonneg (mul_nonneg (sq_nonneg _)
          (c.dMin_pos.le.trans (hDeathBounds a t ht).1))
          (Finset.sum_nonneg (fun i _ => by
            unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
            split_ifs <;> norm_num)))
        (hi.integral_prod_left.const_mul B) (Filter.Eventually.of_forall hpoint)
    _ = B * ∫ t in Ioo (0 : ℝ) 1, ∫ s : Fin n → ObsHistory,
        invRisk a s t ∂sampleLaw P n := by
      rw [integral_const_mul, integral_integral_swap hi]
      dsimp only [ν]
      rw [integral_Ioc_eq_integral_Ioo]
    _ ≤ B * (2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor))) :=
      mul_le_mul_of_nonneg_left
        (positiveRetention_integral_expected_invRisk_le c P hRandom hAssignment
          hOverlap hDeath hCensor hDeathBounds hHorizon a hn) hB
    _ = _ := by dsimp [B]; ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
