module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleTimeEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceFiniteRisk

/-!
# Full-horizon subcritical coefficient energy

A binomial first moment and reciprocal-count bound give an integrable
inverse-retention envelope for the dependent KM/oracle coefficient error.
This removes the strict horizon from coefficient energy convergence.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The observed risk fraction has its exact marginal expectation. -/
-- @node: observed_integral_riskFraction_eq
lemma observed_integral_riskFraction_eq
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory, (riskSet a s t : ℝ) / n ∂sampleLaw P n) =
      P.p a * survival P a t * retention P a t := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  have heq := integral_eventCount_eq_binomial (observedLaw P) A hA n
    (fun k => (k : ℝ) / n)
  have hr : (∫ s : Fin n → ObsHistory, (riskSet a s t : ℝ) / n ∂sampleLaw P n) =
      (∑ k ∈ Finset.range (n + 1), binomialWeight n ((observedLaw P).real A) k *
        ((k : ℝ) / n)) := by
    simpa only [sampleLaw, riskSet, A, Set.mem_setOf_eq] using heq
  rw [hr]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, binomial_first_moment]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [mul_div_cancel_left₀ _ hnR]
  exact observed_arm_risk_probability P hP a ht

/-- A pathwise coefficient bound uses only the unit range of KM and exact
zero-risk cancellation. -/
-- @node: observed_KM_oracle_coefficient_sq_le_reciprocal
lemma observed_KM_oracle_coefficient_sq_le_reciprocal
    (P : SubjectLaw) (a : Arm) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) (t : ℝ) :
    ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2 ≤
      2 * ((n : ℝ) * invRisk a s t) +
        2 * ((riskSet a s t : ℝ) / n) * (1 / (P.p a * retention P a t)) ^ 2 := by
  have hk := deathKMLeft_mem_Icc a s t
  have hk2 : deathKMLeft a s t ^ 2 ≤ 1 := by nlinarith [hk.1, hk.2]
  have hx := scaledInvRisk_mem_Icc a s t
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hid : ((riskSet a s t : ℝ) / n) * ((n : ℝ) * invRisk a s t) ^ 2 =
      (n : ℝ) * invRisk a s t := by
    by_cases hz : riskSet a s t = 0
    · simp [invRisk, hz]
    · have hr : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
      simp only [invRisk, hz, ↓reduceIte]
      field_simp
  have hsq : ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
      1 / (P.p a * retention P a t)) ^ 2 ≤
      2 * ((n : ℝ) * invRisk a s t) ^ 2 * deathKMLeft a s t ^ 2 +
        2 * (1 / (P.p a * retention P a t)) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) * deathKMLeft a s t * invRisk a s t +
      1 / (P.p a * retention P a t))]
  calc
    _ ≤ ((riskSet a s t : ℝ) / n) *
        (2 * ((n : ℝ) * invRisk a s t) ^ 2 * deathKMLeft a s t ^ 2 +
          2 * (1 / (P.p a * retention P a t)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * ((n : ℝ) * invRisk a s t) * deathKMLeft a s t ^ 2 +
        2 * ((riskSet a s t : ℝ) / n) * (1 / (P.p a * retention P a t)) ^ 2 := by
      linear_combination 2 * deathKMLeft a s t ^ 2 * hid
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hk2 hx.1]

/-- The full expected coefficient error has an inverse-retention envelope,
uniform in sample size. No independent factorization is used. -/
-- @node: observed_KM_oracle_coefficient_energy_le_invRetention
lemma observed_KM_oracle_coefficient_energy_le_invRetention
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) ≤
      ((4 * Real.exp c.dMax + 2) / c.pMin) * (retention P a t)⁻¹ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi : Integrable (fun s : Fin n → ObsHistory => (n : ℝ) * invRisk a s t)
      (sampleLaw P n) := by
    apply Integrable.of_bound (by fun_prop) n
    filter_upwards [] with s
    simpa only [Real.norm_eq_abs, abs_of_nonneg (scaledInvRisk_mem_Icc a s t).1]
      using (scaledInvRisk_mem_Icc a s t).2
  have hr : Integrable (fun s : Fin n → ObsHistory => (riskSet a s t : ℝ) / n)
      (sampleLaw P n) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).2
    exact_mod_cast (show riskSet a s t ≤ n from by
      simpa [riskSet] using Finset.card_filter_le (Finset.univ : Finset (Fin n))
        (fun i => (s i).treatment = a ∧ t ≤ (s i).exit))
  have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hg := retention_pos_of_modelClass c P hP a t ht0.le ht1
  have hs : 0 < survival P a t := Real.exp_pos _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0.le, ht1.le⟩
  have hinv : (∫ s : Fin n → ObsHistory, (n : ℝ) * invRisk a s t ∂sampleLaw P n) ≤
      2 / (P.p a * retention P a t * survival P a t) := by
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left
      (recurrence_integral_invRisk_le_arm_tail c P hP a hn ht0 ht1) hnR.le
    exact h.trans_eq (by field_simp)
  calc
    _ ≤ ∫ s : Fin n → ObsHistory, 2 * ((n : ℝ) * invRisk a s t) +
        2 * ((riskSet a s t : ℝ) / n) * (1 / (P.p a * retention P a t)) ^ 2
        ∂sampleLaw P n := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun s => by positivity))
      ((hi.const_mul 2).add ((hr.const_mul 2).mul_const _))
      (Filter.Eventually.of_forall (fun s =>
        observed_KM_oracle_coefficient_sq_le_reciprocal P a hn s t))
    _ = 2 * (∫ s : Fin n → ObsHistory, (n : ℝ) * invRisk a s t ∂sampleLaw P n) +
        2 * (P.p a * survival P a t * retention P a t) *
          (1 / (P.p a * retention P a t)) ^ 2 := by
      rw [integral_add (hi.const_mul 2) ((hr.const_mul 2).mul_const _),
        integral_const_mul, integral_mul_const, integral_const_mul, integral_const_mul,
        observed_integral_riskFraction_eq c P hP a hn ⟨ht0.le, ht1.le⟩]
    _ ≤ 4 / (P.p a * retention P a t * survival P a t) +
        2 * survival P a t / (P.p a * retention P a t) := by
      have heq : 2 * (P.p a * survival P a t * retention P a t) *
          (1 / (P.p a * retention P a t)) ^ 2 =
          2 * survival P a t / (P.p a * retention P a t) := by field_simp
      rw [heq]
      have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
      simp only [div_eq_mul_inv] at h ⊢
      linarith
    _ ≤ (4 * Real.exp c.dMax + 2) / (P.p a * retention P a t) := by
      have hsInv : (survival P a t)⁻¹ ≤ Real.exp c.dMax := by
        have h := inv_le_inv₀ hs (Real.exp_pos (-c.dMax)) |>.2 hS.1
        simpa only [Real.exp_neg, inv_inv] using h
      have hfirst : 4 / (P.p a * retention P a t * survival P a t) ≤
          4 * Real.exp c.dMax / (P.p a * retention P a t) := by
        simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
          using mul_le_mul_of_nonneg_left hsInv (by positivity :
            0 ≤ 4 / (P.p a * retention P a t))
      have hsecond := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS.2 (by norm_num : (0 : ℝ) ≤ 2))
        (mul_pos hp hg).le
      calc
        _ ≤ 4 * Real.exp c.dMax / (P.p a * retention P a t) +
            2 / (P.p a * retention P a t) := add_le_add hfirst (by simpa using hsecond)
        _ = _ := by ring
    _ ≤ _ := by
      rw [show (4 * Real.exp c.dMax + 2) / c.pMin * (retention P a t)⁻¹ =
          (4 * Real.exp c.dMax + 2) / (c.pMin * retention P a t) by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos c.pMin_pos hg) (mul_le_mul_of_nonneg_right (hP.treatmentOverlap a) hg.le)

/-- Subcritical inverse retention dominates the coefficient energy on the
entire horizon, so bounded measurable deterministic weights admit dominated
convergence even though the oracle inverse retention is unbounded. -/
-- @node: observed_KM_oracle_subcritical_weighted_time_energy_tendsto_zero
lemma observed_KM_oracle_subcritical_weighted_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ K) :
    Filter.Tendsto (fun n : ℕ => ∫ t in Icc (0 : ℝ) 1,
      f t * (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n))
      Filter.atTop (nhds 0) := by
  let B := (4 * Real.exp c.dMax + 2) / c.pMin
  have hi := inv_retention_intervalIntegrable_subcritical c P hP hk a
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  simp_rw [integral_Icc_eq_integral_Ioo]
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun _ : ℝ => (0 : ℝ))
    (fun t : ℝ => K * B * (retention P a t)⁻¹)
    (Filter.Eventually.of_forall (fun n =>
      (hf.mul (measurable_observed_KM_oracle_coefficient_energy P a n)).aestronglyMeasurable))
    (Filter.eventually_atTop.2 ⟨1, fun n hn => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (integral_nonneg (fun s => by positivity))]
      simpa only [mul_assoc] using mul_le_mul (hb t ⟨ht.1.le, ht.2.le⟩)
        (observed_KM_oracle_coefficient_energy_le_invRetention c P hP a
          (by omega) ht.1 ht.2) (integral_nonneg (fun s => by positivity)) hK⟩)
    (hi.const_mul (K * B)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      simpa only [mul_zero, Pi.mul_apply] using
        (observed_KM_oracle_coefficient_energy_tendsto_zero c P hP a ht.1.le ht.2).const_mul (f t))
  simpa only [integral_zero, Pi.mul_apply] using h

/-- Continuous study-window weights need no globally smooth extension in
the full-horizon coefficient energy limit. -/
-- @node: observed_KM_oracle_subcritical_continuous_time_energy_tendsto_zero
lemma observed_KM_oracle_subcritical_continuous_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Filter.Tendsto (fun n : ℕ => ∫ t in Icc (0 : ℝ) 1,
      f t * (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n))
      Filter.atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  have h := observed_KM_oracle_subcritical_weighted_time_energy_tendsto_zero
    c P hP hk a g hg (le_max_right K 0) (fun t ht => by
      simpa only [g, Set.piecewise, if_pos ht, Real.norm_eq_abs] using
        (hK t ht).trans (le_max_left K 0))
  convert h using 1
  funext n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [g, Set.piecewise, if_pos ht]

/-- Bounded deterministic weights make the dependent squared KM/oracle
coefficient error integrable on the sample-by-time product space. -/
-- @node: observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
lemma observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (hk : c.kappa < 1) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, |f t| ≤ K) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ => f p.2 *
      (((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2 -
          1 / (P.p a * retention P a p.2)) ^ 2))
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := fun (s : Fin n → ObsHistory) (t : ℝ) => ((riskSet a s t : ℝ) / n) *
    ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
      1 / (P.p a * retention P a t)) ^ 2
  let B := (4 * Real.exp c.dMax + 2) / c.pMin
  have hiG := inv_retention_intervalIntegrable_subcritical c P hP hk a
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hiG
  have hE0 (s : Fin n → ObsHistory) (t : ℝ) : 0 ≤ E s t := by dsimp [E]; positivity
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ => f p.2 * E p.1 p.2) := by
    have hr : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    dsimp [E]
    fun_prop
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ => f p.2 * E p.1 p.2)
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      apply Integrable.const_mul
      dsimp [E]
      apply integrable_observed_risk_weighted_sq P a t
        (fun s => (n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) (by fun_prop)
        (by positivity : 0 ≤ (n : ℝ) + |1 / (P.p a * retention P a t)|)
      intro s
      have hx := scaledInvRisk_mem_Icc a s t
      have hk := deathKMLeft_mem_Icc a s t
      have hz : 0 ≤ (n : ℝ) * deathKMLeft a s t * invRisk a s t := by
        calc
          _ = deathKMLeft a s t * ((n : ℝ) * invRisk a s t) := by ring
          _ ≥ 0 := mul_nonneg hk.1 hx.1
      have hzle : (n : ℝ) * deathKMLeft a s t * invRisk a s t ≤ n := by
        calc
          _ = deathKMLeft a s t * ((n : ℝ) * invRisk a s t) := by ring
          _ ≤ 1 * ((n : ℝ) * invRisk a s t) := mul_le_mul_of_nonneg_right hk.2 hx.1
          _ ≤ n := by simpa using hx.2
      exact (abs_sub _ _).trans (add_le_add
        (by rwa [abs_of_nonneg hz]) (le_refl _))
    · apply Integrable.mono' (hiG.const_mul (K * B))
        hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have heq : (∫ s : Fin n → ObsHistory, ‖f t * E s t‖ ∂sampleLaw P n) =
          |f t| * (∫ s : Fin n → ObsHistory, E s t ∂sampleLaw P n) := by
        simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hE0 _ _)]
        rw [integral_const_mul]
      rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [E, B, mul_assoc] using mul_le_mul (hbound t ht)
        (observed_KM_oracle_coefficient_energy_le_invRetention c P hP a hn ht.1 ht.2)
        (integral_nonneg (fun s => hE0 s t)) hK
  exact hi

/-- Fubini applies to the genuinely dependent squared coefficient error;
the uniform expected-energy bound supplies product integrability. -/
-- @node: observed_KM_oracle_subcritical_weighted_time_energy_integral_swap
lemma observed_KM_oracle_subcritical_weighted_time_energy_integral_swap
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (hk : c.kappa < 1) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, |f t| ≤ K) :
    (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
      f t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
    ∫ t in Ioo (0 : ℝ) 1,
      f t * (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := fun (s : Fin n → ObsHistory) (t : ℝ) => ((riskSet a s t : ℝ) / n) *
    ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
      1 / (P.p a * retention P a t)) ^ 2
  have hi := observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
    c P hP a hk hn f hf hK hbound
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, ∫ s : Fin n → ObsHistory,
        f t * E s t ∂sampleLaw P n := integral_integral_swap hi
    _ = _ := by simp_rw [integral_const_mul]; rfl


/-- The expected integrated coefficient error vanishes on the full horizon;
Fubini is justified by the subcritical inverse-retention envelope. -/
-- @node: observed_KM_oracle_subcritical_expected_time_energy_tendsto_zero
lemma observed_KM_oracle_subcritical_expected_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ K) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
        f t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  apply (observed_KM_oracle_subcritical_weighted_time_energy_tendsto_zero
    c P hP hk a f hf hK hb).congr'
  refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
  simp_rw [integral_Icc_eq_integral_Ioo]
  exact (observed_KM_oracle_subcritical_weighted_time_energy_integral_swap
    c P hP a hk (by omega) f hf hK (fun t ht => hb t ⟨ht.1.le, ht.2.le⟩)).symm

/-- A zero extension lets continuous study-window weights pass through the
full-horizon expectation/time exchange. -/
-- @node: observed_KM_oracle_subcritical_expected_continuous_time_energy_tendsto_zero
lemma observed_KM_oracle_subcritical_expected_continuous_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
        f t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  have h := observed_KM_oracle_subcritical_expected_time_energy_tendsto_zero
    c P hP hk a g hg (le_max_right K 0) (fun t ht => by
      simpa only [g, Set.piecewise, if_pos ht, Real.norm_eq_abs] using
        (hK t ht).trans (le_max_left K 0))
  convert h using 1
  funext n
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [g, Set.piecewise, if_pos ht]

/-- The recurrence coefficient's full-horizon expected energy vanishes in
the subcritical regime, including the zero-retention endpoint. -/
-- @node: observed_KM_oracle_subcritical_recurrence_time_energy_tendsto_zero
lemma observed_KM_oracle_subcritical_recurrence_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
        P.lam a t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  exact observed_KM_oracle_subcritical_expected_continuous_time_energy_tendsto_zero
    c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn

/-- The deterministic death coefficient's full-horizon expected energy
vanishes; the future-mark estimator is not used as a predictable weight. -/
-- @node: observed_KM_oracle_subcritical_death_time_energy_tendsto_zero
lemma observed_KM_oracle_subcritical_death_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
          (((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
              1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  apply observed_KM_oracle_subcritical_expected_continuous_time_energy_tendsto_zero
    c P hP hk a
  exact (((continuousOn_remainingTarget_zero c P hP a).div
    (modelClass_survival_continuousOn c P hP a)
    (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
      (hP.deathHolder a).1.continuousOn

/-- Continuous nonnegative deterministic weights turn the full-horizon
expected coefficient-energy limit into convergence in probability. The
Markov step uses product integrability, rather than factoring dependent terms. -/
-- @node: observed_KM_oracle_subcritical_time_energy_probability_tendsto_zero
lemma observed_KM_oracle_subcritical_time_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Icc (0 : ℝ) 1,
        f t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)})
      Filter.atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) => ∫ t in Icc (0 : ℝ) 1,
    f t * (((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2)
  have hF0 (n : ℕ) (s : Fin n → ObsHistory) : 0 ≤ F n s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (hf0 t ht) (by positivity)
  have hFi (n : ℕ) (hn : 0 < n) : Integrable (F n) (sampleLaw P n) := by
    letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
    have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
    have hi := observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
      c P hP a hk hn g hg (le_max_right K 0) (fun t ht => by
        simpa only [g, Set.piecewise, if_pos (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩), Real.norm_eq_abs]
          using (hK t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left K 0))
    convert hi.integral_prod_left using 1
    funext s
    dsimp only [F]
    rw [integral_Icc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [g, Set.piecewise, if_pos (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)]
  have hlim := (observed_KM_oracle_subcritical_expected_continuous_time_energy_tendsto_zero
    c P hP hk a f hf).div_const ε
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => measureReal_nonneg)) _
    (by simpa only [zero_div] using hlim)
  refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  change (sampleLaw P n).real {s | ε < F n s} ≤
    (∫ s, F n s ∂sampleLaw P n) / ε
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (hF0 n)) (hFi n (by omega)) ε
  have hsub : (sampleLaw P n).real {s | ε < F n s} ≤
      (sampleLaw P n).real {s | ε ≤ F n s} :=
    measureReal_mono (fun s (hs : ε < F n s) => (show ε ≤ F n s from hs.le))
      (by finiteness)
  apply (le_div_iff₀ hε).2
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hsub hε.le).trans hm

/-- Recurrence intensity supplies a nonnegative continuous coefficient, so
its integrated KM/oracle error energy vanishes in probability. -/
-- @node: observed_KM_oracle_subcritical_recurrence_time_energy_probability_tendsto_zero
lemma observed_KM_oracle_subcritical_recurrence_time_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Icc (0 : ℝ) 1,
        P.lam a t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)})
      Filter.atTop (nhds 0) := by
  exact observed_KM_oracle_subcritical_time_energy_probability_tendsto_zero
    c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn
    (fun t ht => c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1) hε

/-- The deterministic death weight supplies a nonnegative continuous
coefficient. No predictability claim about the future-mark plug-in is used. -/
-- @node: observed_KM_oracle_subcritical_death_time_energy_probability_tendsto_zero
lemma observed_KM_oracle_subcritical_death_time_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Icc (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
          (((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
              1 / (P.p a * retention P a t)) ^ 2)})
      Filter.atTop (nhds 0) := by
  apply observed_KM_oracle_subcritical_time_energy_probability_tendsto_zero
    c P hP hk a
  · exact (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  · intro t ht
    exact mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)
  · exact hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
