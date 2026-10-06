module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoefficientEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathOracleMoments

/-! # Energy of the root-n death oracle replacement

Roadmap (18)--(19): normalize the actual KM death coefficient and subtract
its deterministic endpoint oracle. Its quadratic density is exactly the
weighted risk-fraction coefficient energy, retaining all KM/risk dependence.
Subcritical overlap supplies product integrability and vanishing expected
energy even though the oracle coefficient can be unbounded at the horizon.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The root-n empirical death coefficient minus its normalized oracle. -/
-- @node: observedDeathOracleDifferenceWeight
noncomputable def observedDeathOracleDifferenceWeight (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  Real.sqrt n * deathTargetWeight c P a 0 t * deathKMLeft a s t * invRisk a s t -
    subcriticalDeathOracleWeight c P a t / Real.sqrt n

/-- The death difference coefficient is jointly measurable, including the
unbounded deterministic endpoint oracle. -/
-- @node: measurable_observedDeathOracleDifferenceWeight
@[fun_prop]
lemma measurable_observedDeathOracleDifferenceWeight
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      observedDeathOracleDifferenceWeight c P a p.1 p.2) := by
  unfold observedDeathOracleDifferenceWeight
  have hw : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      deathTargetWeight c P a 0 p.2) := (measurable_deathTargetWeight c P hP a
    (h := 0) (by norm_num) (by norm_num)).comp measurable_snd
  have ho : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      subcriticalDeathOracleWeight c P a p.2) :=
    (measurable_subcriticalDeathOracleWeight c P hP a).comp measurable_snd
  fun_prop

/-- Root-n normalization cancels exactly to the risk-fraction energy; no
factorization of the dependent KM and risk-set terms is involved. -/
-- @node: observedDeathOracleDifferenceWeight_energyDensity_eq
lemma observedDeathOracleDifferenceWeight_energyDensity_eq
    (c : ClassConstants) (P : SubjectLaw) (a : Arm) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
        (riskSet a s t : ℝ) =
      ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
        (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2) := by
  have hr : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hr2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have he : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
    apply (div_eq_iff hr).2
    nlinarith [hr2]
  have hd : observedDeathOracleDifferenceWeight c P a s t =
      (remainingTarget c P a 0 t / survival P a t) *
        (((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) / Real.sqrt n) := by
    simp only [observedDeathOracleDifferenceWeight, subcriticalDeathOracleWeight,
      deathTargetWeight, sub_zero, if_pos ht]
    simp only [div_eq_mul_inv] at he ⊢
    linear_combination -(remainingTarget c P a 0 t / survival P a t) *
      deathKMLeft a s t * invRisk a s t * he
  rw [hd, mul_pow]
  simp only [div_pow, hr2]
  ring

/-- Subcritical overlap makes the actual normalized death difference density
integrable on sample-by-time space. This is the finiteness input to the
unbounded predictable-integral isometry. -/
-- @node: observedDeathOracleDifferenceWeight_energy_integrable_prod
lemma observedDeathOracleDifferenceWeight_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      observedDeathOracleDifferenceWeight c P a p.1 p.2 ^ 2 * P.hazard a p.2 *
        (riskSet a p.1 p.2 : ℝ))
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  let f : ℝ → ℝ := fun t =>
    (remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  have hi := DeathCP.observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
    c P hP a hk hn g hg (le_max_right K 0) (fun t ht => by
      simpa only [g, Set.piecewise, if_pos (Ioo_subset_Icc_self ht), Real.norm_eq_abs]
        using (hK t (Ioo_subset_Icc_self ht)).trans (le_max_left K 0))
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply hi.congr
  have ht : ∀ᵐ p ∂(sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1)),
      p.2 ∈ Ioo (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [ht] with p hp
  rw [observedDeathOracleDifferenceWeight_energyDensity_eq c P a hn p.1
    (Ioo_subset_Icc_self hp)]
  simp only [g, Set.piecewise, if_pos (Ioo_subset_Icc_self hp), f]

/-- The genuine root-n death replacement has vanishing full-horizon expected
quadratic energy, with the exact deterministic remaining-target multiplier. -/
-- @node: observedDeathOracleDifferenceWeight_expected_energy_tendsto_zero
lemma observedDeathOracleDifferenceWeight_expected_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1,
        observedDeathOracleDifferenceWeight c P a s t ^ 2 * P.hazard a t *
          (riskSet a s t : ℝ)) ∂sampleLaw P n) atTop (nhds 0) := by
  apply (DeathCP.observed_KM_oracle_subcritical_death_time_energy_tendsto_zero
    c P hP hk a).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (observedDeathOracleDifferenceWeight_energyDensity_eq c P a
    (by omega : 0 < n) s ht).symm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
