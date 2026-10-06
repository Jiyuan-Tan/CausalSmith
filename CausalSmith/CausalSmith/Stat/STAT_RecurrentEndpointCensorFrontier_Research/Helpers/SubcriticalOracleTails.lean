module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoefficientEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance

/-!
# Subcritical oracle tail energies

The endpoint retention assumption gives integrable recurrence and death oracle
energies separately. Their terminal integrals vanish as the localization horizon
approaches one, even though the oracle weights need not be bounded there.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A continuous study-window coefficient times inverse retention is integrable
under the subcritical endpoint assumption. -/
-- @node: subcritical_continuous_invRetention_intervalIntegrable
lemma subcritical_continuous_invRetention_intervalIntegrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun t => f t / retention P a t) volume 0 1 := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hi := inv_retention_intervalIntegrable_subcritical c P hP hk a
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    at hi ⊢
  change Integrable (fun t => f t / retention P a t) (volume.restrict (Icc (0 : ℝ) 1))
  simpa only [div_eq_mul_inv] using hi.bdd_mul
    (hf.aestronglyMeasurable measurableSet_Icc)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hB t ht)

/-- The recurrence oracle energy is integrable without a separate inverse-weight
moment assumption. -/
-- @node: subcritical_recurrence_energy_intervalIntegrable
lemma subcritical_recurrence_energy_intervalIntegrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    IntervalIntegrable (fun t => survival P a t * P.lam a t / retention P a t)
      volume 0 1 := by
  apply subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
  exact (modelClass_survival_continuousOn c P hP a).mul
    (hP.recurrenceHolder a).1.continuousOn

/-- The death oracle energy is integrable through the endpoint, using the
continuous remaining-target coefficient and strictly positive survival. -/
-- @node: subcritical_death_energy_intervalIntegrable
lemma subcritical_death_energy_intervalIntegrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    IntervalIntegrable (fun t => (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
      (survival P a t * retention P a t)) volume 0 1 := by
  have hc : ContinuousOn (fun t =>
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t / survival P a t)
      (Icc (0 : ℝ) 1) :=
    (((continuousOn_remainingTarget_zero c P hP a).pow 2).mul
      (hP.deathHolder a).1.continuousOn).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')
  simpa only [div_div] using
    subcritical_continuous_invRetention_intervalIntegrable c P hP hk a _ hc

/-- Integrability on the full study window suffices for vanishing terminal
energy; no boundedness of the integrand at time one is required. -/
-- @node: studyWindow_integral_tail_tendsto_zero
lemma studyWindow_integral_tail_tendsto_zero (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 1) :
    Tendsto (fun T : ℝ => ∫ t in T..1, f t)
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) (nhds 0) := by
  have hi : IntegrableOn f (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hf
  have hc := intervalIntegral.continuousOn_primitive_interval_left hi
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), intervalIntegral.integral_same]
    using (hc 1 (by simp)).tendsto

/-- The recurrence oracle's exact terminal energy vanishes when removing the
localization horizon. -/
-- @node: subcritical_recurrence_oracle_tail_tendsto_zero
lemma subcritical_recurrence_oracle_tail_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun T : ℝ => (P.p a)⁻¹ *
      ∫ t in T..1, survival P a t * P.lam a t / retention P a t)
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) (nhds 0) := by
  simpa only [mul_zero] using
    (studyWindow_integral_tail_tendsto_zero _
      (subcritical_recurrence_energy_intervalIntegrable c P hP hk a)).const_mul (P.p a)⁻¹

/-- The death oracle's exact terminal energy vanishes, with its deterministic
remaining target rather than a future-mark plug-in in the stochastic integrand. -/
-- @node: subcritical_death_oracle_tail_tendsto_zero
lemma subcritical_death_oracle_tail_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun T : ℝ => (P.p a)⁻¹ *
      ∫ t in T..1, (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t))
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) (nhds 0) := by
  simpa only [mul_zero] using
    (studyWindow_integral_tail_tendsto_zero _
      (subcritical_death_energy_intervalIntegrable c P hP hk a)).const_mul (P.p a)⁻¹

/-- The inverse-retention terminal envelope vanishes in the subcritical regime. -/
-- @node: subcritical_invRetention_tail_tendsto_zero
lemma subcritical_invRetention_tail_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun T : ℝ => ∫ t in T..1, (retention P a t)⁻¹)
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) (nhds 0) := by
  exact studyWindow_integral_tail_tendsto_zero _
    (inv_retention_intervalIntegrable_subcritical c P hP hk a)

/-- The mean dependent coefficient energy is integrable over the full horizon,
by its inverse-retention envelope, without an independence assumption. -/
-- @node: subcritical_mean_coefficient_energy_intervalIntegrable
lemma subcritical_mean_coefficient_energy_intervalIntegrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    IntervalIntegrable (fun t => ∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) volume 0 1 := by
  have hi := (inv_retention_intervalIntegrable_subcritical c P hP hk a).const_mul
    ((4 * Real.exp c.dMax + 2) / c.pMin)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    at hi ⊢
  apply hi.mono'
    (DeathCP.measurable_observed_KM_oracle_coefficient_energy P a n).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun s => by positivity))]
  exact DeathCP.observed_KM_oracle_coefficient_energy_le_invRetention c P hP a hn ht.1 ht.2

/-- Every sample size has the same vanishing inverse-retention envelope for
its dependent mean coefficient tail energy. -/
-- @node: subcritical_mean_coefficient_tail_energy_le
lemma subcritical_mean_coefficient_tail_energy_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ t in T..1, ∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) ≤
      ((4 * Real.exp c.dMax + 2) / c.pMin) *
        ∫ t in T..1, (retention P a t)⁻¹ := by
  have hsub : uIcc T 1 ⊆ uIcc (0 : ℝ) 1 := by
    simp only [uIcc_of_le hT1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hT0 le_rfl
  have hi := (subcritical_mean_coefficient_energy_intervalIntegrable c P hP hk a hn).mono_set hsub
  have hg := (inv_retention_intervalIntegrable_subcritical c P hP hk a).mono_set hsub
  calc
    _ ≤ ∫ t in T..1, ((4 * Real.exp c.dMax + 2) / c.pMin) *
        (retention P a t)⁻¹ :=
      intervalIntegral.integral_mono_on_of_le_Ioo hT1 hi (hg.const_mul _) (fun t ht =>
        DeathCP.observed_KM_oracle_coefficient_energy_le_invRetention c P hP a hn
          (hT0.trans_lt ht.1) ht.2)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Removing the localization horizon makes mean coefficient tail energy
arbitrarily small uniformly over all positive sample sizes. -/
-- @node: subcritical_mean_coefficient_tail_energy_uniform_small
lemma subcritical_mean_coefficient_tail_energy_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (∫ t in T..1, ∫ s : Fin n → ObsHistory,
        ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) < ε := by
  have hlim := (subcritical_invRetention_tail_tendsto_zero c P hP hk a).const_mul
    ((4 * Real.exp c.dMax + 2) / c.pMin)
  have hsmall := hlim.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [self_mem_nhdsWithin, hsmall] with T hT hTsmall
  intro n hn
  exact (subcritical_mean_coefficient_tail_energy_le c P hP hk a hn hT.1 hT.2).trans_lt hTsmall

/-- A bounded continuous deterministic coefficient preserves the
sample-size-uniform vanishing coefficient tail envelope. -/
-- @node: subcritical_weighted_mean_coefficient_tail_energy_uniform_small
lemma subcritical_weighted_mean_coefficient_tail_energy_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (∫ t in T..1, f t * (∫ s : Fin n → ObsHistory,
        ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n)) < ε := by
  have hlim := (subcritical_invRetention_tail_tendsto_zero c P hP hk a).const_mul
    (K * ((4 * Real.exp c.dMax + 2) / c.pMin))
  have hsmall := hlim.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [self_mem_nhdsWithin, hsmall] with T hT hTsmall
  intro n hn
  have hsub : uIcc T 1 ⊆ uIcc (0 : ℝ) 1 := by
    simp only [uIcc_of_le hT.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hT.1 le_rfl
  have hi := (subcritical_mean_coefficient_energy_intervalIntegrable c P hP hk a hn).mono_set hsub
  have hfT : ContinuousOn f (uIcc T 1) := by
    apply hf.mono
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hsub
  have hfi : IntervalIntegrable (fun t => f t * (∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n)) volume T 1 := by
    simpa only [mul_comm] using hi.mul_continuousOn hfT
  calc
    _ ≤ ∫ t in T..1, K * (∫ s : Fin n → ObsHistory,
        ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hT.2 hfi (hi.const_mul K)
        (fun t ht => mul_le_mul_of_nonneg_right
          (hb t ⟨hT.1.trans ht.1.le, ht.2.le⟩)
          (integral_nonneg (fun s => by positivity)))
    _ = K * (∫ t in T..1, ∫ s : Fin n → ObsHistory,
        ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ K * (((4 * Real.exp c.dMax + 2) / c.pMin) *
        ∫ t in T..1, (retention P a t)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (subcritical_mean_coefficient_tail_energy_le c P hP hk a hn hT.1 hT.2) hK
    _ < ε := by simpa only [mul_assoc] using hTsmall

/-- Recurrence intensity weighting preserves the uniform vanishing of the
KM/oracle coefficient tail energy. -/
-- @node: subcritical_recurrence_coefficient_tail_energy_uniform_small
lemma subcritical_recurrence_coefficient_tail_energy_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (∫ t in T..1, P.lam a t * (∫ s : Fin n → ObsHistory,
        ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n)) < ε := by
  exact subcritical_weighted_mean_coefficient_tail_energy_uniform_small c P hP hk a
    (P.lam a) (hP.recurrenceHolder a).1.continuousOn
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
    (fun t ht => (hP.recurrenceBounds a t ht).2) hε

/-- The deterministic death coefficient also has uniformly vanishing tail
energy; its compact continuous envelope is derived from the model class. -/
-- @node: subcritical_death_coefficient_tail_energy_uniform_small
lemma subcritical_death_coefficient_tail_energy_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (∫ t in T..1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
          (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
              1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n)) < ε := by
  have hf : ContinuousOn (fun t =>
      (remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) :=
    (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply subcritical_weighted_mean_coefficient_tail_energy_uniform_small c P hP hk a
    _ hf (le_max_right K 0) _ hε
  intro t ht
  have hb : |(remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK t ht
  exact (le_abs_self _).trans (hb.trans (le_max_left K 0))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
