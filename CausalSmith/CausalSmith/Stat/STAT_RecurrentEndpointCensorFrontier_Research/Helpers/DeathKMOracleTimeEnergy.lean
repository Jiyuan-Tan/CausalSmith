module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleIntegratedEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fixed-horizon oracle coefficient energy convergence

Uniform deterministic envelopes permit time integration of the dependent
KM and inverse-risk coefficient errors on every strict study horizon.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- Young's inequality gives an n-independent envelope for the dependent
weighted KM error, using its unit-range bound rather than independence. -/
-- @node: observed_integral_scaledInvRisk_KM_error_sq_le_envelope
lemma observed_integral_scaledInvRisk_KM_error_sq_le_envelope
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} {t δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hδ : 0 < δ) :
    (∫ s : Fin n → ObsHistory, ((n : ℝ) * invRisk a s t) *
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) ≤
      δ * (6 / (P.p a * survival P a t * retention P a t) ^ 2) + 1 / δ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let X := fun s : Fin n → ObsHistory => (n : ℝ) * invRisk a s t
  let E := fun s : Fin n → ObsHistory => deathKMLeft a s t - survival P a t
  have hX : Measurable X := by
    dsimp [X]
    exact measurable_const.mul ((measurable_recurrenceInvRisk_joint a).comp
      (measurable_id.prodMk measurable_const))
  have hE : Measurable E := by
    dsimp [E]
    exact ((measurable_recurrenceDeathKMLeft_joint a).comp
      (measurable_id.prodMk measurable_const)).sub measurable_const
  have hEbound (s : Fin n → ObsHistory) : E s ^ 2 ≤ 1 := by
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩
    have hs0 := Real.exp_pos (-c.dMax)
    dsimp [E]
    have he : |deathKMLeft a s t - survival P a t| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hk.1, hk.2, hs.1, hs.2],
        by linarith [hk.1, hk.2, hs.1, hs.2]⟩
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 he
  have hEi : Integrable (fun s => E s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hE.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E s))] using hEbound s
  have hXi : Integrable (fun s => X s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable ((n : ℝ) ^ 2)
    filter_upwards [] with s
    have hi : 0 ≤ invRisk a s t ∧ invRisk a s t ≤ 1 := by
      unfold invRisk
      split_ifs with hz
      · norm_num
      · have hr : (1 : ℝ) ≤ riskSet a s t := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        exact ⟨inv_nonneg.mpr (by positivity), inv_le_one_of_one_le₀ hr⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X s))]
    dsimp [X]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hi.2 hn0, mul_nonneg hn0 hi.1]
  calc
    _ ≤ ∫ s, δ * X s ^ 2 + E s ^ 2 / δ ∂sampleLaw P n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => by
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by
          unfold invRisk; split_ifs <;> positivity)) (sq_nonneg _)))
        ((hXi.const_mul δ).add (hEi.div_const δ))
        (Filter.Eventually.of_forall (fun s => by
          simpa [X, E, mul_comm] using km_error_weight_young (hEbound s) hδ))
    _ = δ * (∫ s, X s ^ 2 ∂sampleLaw P n) +
        (∫ s, E s ^ 2 ∂sampleLaw P n) / δ := by
      rw [integral_add (hXi.const_mul δ) (hEi.div_const δ),
        integral_const_mul, integral_div]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (observed_integral_scaledInvRisk_sq_le P hP a ht1 ⟨ht0, le_rfl⟩) hδ.le)
      (div_le_div_of_nonneg_right
        (by
          calc
            (∫ s, E s ^ 2 ∂sampleLaw P n) ≤ ∫ _s : Fin n → ObsHistory, (1 : ℝ) ∂sampleLaw P n :=
              integral_mono hEi (integrable_const 1) hEbound
            _ = 1 := by simp) hδ.le)


/-- The full coefficient energy has a deterministic envelope uniform over
sample sizes and times in a strict horizon. -/
-- @node: observed_KM_oracle_coefficient_energy_le_uniform
lemma observed_KM_oracle_coefficient_energy_le_uniform
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T t : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) ≤
      22 / (c.pMin * Real.exp (-c.dMax) * retention P a T) ^ 2 + 2 := by
  let q := P.p a * survival P a t * retention P a t
  let b := c.pMin * Real.exp (-c.dMax) * retention P a T
  have hb : 0 < b := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _))
    (retention_pos_of_modelClass c P hP a T hT0 hT1)
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a
    ⟨ht.1, ht.2.trans hT1.le⟩
  have hst : 0 ≤ survival P a t := (Real.exp_pos _).le
  have hq : b ≤ q := by
    dsimp [b, q]
    exact mul_le_mul
      (mul_le_mul (hP.treatmentOverlap a) hs.1 (Real.exp_pos _).le
        (c.pMin_pos.trans_le (hP.treatmentOverlap a)).le)
      (retention_antitone P a ht.2)
      (retention_pos_of_modelClass c P hP a T hT0 hT1).le
      (mul_nonneg (c.pMin_pos.trans_le (hP.treatmentOverlap a)).le hst)
  have hqpos : 0 < q := hb.trans_le hq
  have hsq : b ^ 2 ≤ q ^ 2 := (sq_le_sq₀ hb.le hqpos.le).2 hq
  have h6 : 6 / q ^ 2 ≤ 6 / b ^ 2 := div_le_div_of_nonneg_left (by norm_num)
    (sq_pos_of_pos hb) hsq
  have h5 : 5 / (((n + 1 : ℕ) : ℝ) * q ^ 2) ≤ 5 / b ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hb)
    exact hsq.trans (le_mul_of_one_le_left (sq_nonneg q) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))
  have hS : survival P a t ^ 2 ≤ 1 := by nlinarith [hs.2]
  have hc : 2 * survival P a t ^ 2 *
      (5 / (((n + 1 : ℕ) : ℝ) * q ^ 2)) ≤ 2 * (5 / b ^ 2) := by
    calc
      _ ≤ 2 * (5 / (((n + 1 : ℕ) : ℝ) * q ^ 2)) := by
        gcongr
        linarith [hS]
      _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by norm_num)
  have hm := observed_integral_scaledInvRisk_KM_error_sq_le_envelope c P hP a
    ht.1 (ht.2.trans_lt hT1) (by norm_num : (0 : ℝ) < 1) (n := n)
  have he := observed_KM_oracle_coefficient_energy_le c P hP a hn ht.1
    (ht.2.trans_lt hT1)
  dsimp [q] at h6 hc
  simp only [one_mul, div_one] at hm
  dsimp [b] at h6 hc
  simp only [div_eq_mul_inv] at h6 hc hm he ⊢
  linarith

/-- The expected oracle coefficient energy is measurable in deterministic time. -/
-- @node: measurable_observed_KM_oracle_coefficient_energy
@[fun_prop]
lemma measurable_observed_KM_oracle_coefficient_energy
    (P : SubjectLaw) (a : Arm) (n : ℕ) :
    Measurable (fun t : ℝ =>
      ∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      ((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2 -
          1 / (P.p a * retention P a p.2)) ^ 2) := by
    have hr : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

/-- Dominated convergence integrates the fixed-time coefficient energy on
every strict horizon, with no KM/risk-set independence assumption. -/
-- @node: observed_KM_oracle_coefficient_time_energy_tendsto_zero
lemma observed_KM_oracle_coefficient_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Filter.Tendsto (fun n : ℕ => ∫ t in Icc (0 : ℝ) T,
      (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n))
      Filter.atTop (nhds 0) := by
  let B := 22 / (c.pMin * Real.exp (-c.dMax) * retention P a T) ^ 2 + 2
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) T)) (f := fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => B)
    (Filter.Eventually.of_forall (fun n =>
      (measurable_observed_KM_oracle_coefficient_energy P a n).aestronglyMeasurable))
    (Filter.eventually_atTop.2 ⟨1, fun n hn => by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun s => by positivity))]
      exact observed_KM_oracle_coefficient_energy_le_uniform c P hP a
        (by omega) hT0 hT1 ht⟩)
    (integrable_const B) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact observed_KM_oracle_coefficient_energy_tendsto_zero c P hP a ht.1
        (ht.2.trans_lt hT1))
  simpa only [integral_zero, Pi.mul_apply] using h

/-- Bounded measurable deterministic weights preserve fixed-horizon
coefficient energy convergence. -/
-- @node: observed_KM_oracle_weighted_time_energy_tendsto_zero
lemma observed_KM_oracle_weighted_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (f : ℝ → ℝ)
    (hf : Measurable f) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, |f t| ≤ K) :
    Filter.Tendsto (fun n : ℕ => ∫ t in Icc (0 : ℝ) T,
      f t * (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n))
      Filter.atTop (nhds 0) := by
  let B := 22 / (c.pMin * Real.exp (-c.dMax) * retention P a T) ^ 2 + 2
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) T)) (f := fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => K * B)
    (Filter.Eventually.of_forall (fun n =>
      (hf.mul (measurable_observed_KM_oracle_coefficient_energy P a n)).aestronglyMeasurable))
    (Filter.eventually_atTop.2 ⟨1, fun n hn => by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (integral_nonneg (fun s => by positivity))]
      exact mul_le_mul (hbound t ht)
        (observed_KM_oracle_coefficient_energy_le_uniform c P hP a
          (by omega) hT0 hT1 ht) (integral_nonneg (fun s => by positivity)) hK⟩)
    (integrable_const (K * B)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [mul_zero, Pi.mul_apply] using
        (observed_KM_oracle_coefficient_energy_tendsto_zero c P hP a ht.1
          (ht.2.trans_lt hT1)).const_mul (f t))
  simpa only [integral_zero, Pi.mul_apply] using h

/-- Fubini applies to the genuinely dependent squared coefficient error;
the uniform expected-energy bound supplies product integrability. -/
-- @node: observed_KM_oracle_weighted_time_energy_integral_swap
lemma observed_KM_oracle_weighted_time_energy_integral_swap
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (f : ℝ → ℝ) (hf : Measurable f) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, |f t| ≤ K) :
    (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) T,
      f t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
    ∫ t in Icc (0 : ℝ) T,
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
  let B := 22 / (c.pMin * Real.exp (-c.dMax) * retention P a T) ^ 2 + 2
  have hE0 (s : Fin n → ObsHistory) (t : ℝ) : 0 ≤ E s t := by dsimp [E]; positivity
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ => f p.2 * E p.1 p.2) := by
    have hr : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    dsimp [E]
    fun_prop
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ => f p.2 * E p.1 p.2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) T))) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
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
    · apply Integrable.mono' (integrable_const (K * B))
        hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have heq : (∫ s : Fin n → ObsHistory, ‖f t * E s t‖ ∂sampleLaw P n) =
          |f t| * (∫ s : Fin n → ObsHistory, E s t ∂sampleLaw P n) := by
        simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hE0 _ _)]
        rw [integral_const_mul]
      rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (hbound t ht)
        (observed_KM_oracle_coefficient_energy_le_uniform c P hP a hn hT0 hT1 ht)
        (integral_nonneg (fun s => hE0 s t)) hK
  calc
    _ = ∫ t in Icc (0 : ℝ) T, ∫ s : Fin n → ObsHistory,
        f t * E s t ∂sampleLaw P n := integral_integral_swap hi
    _ = _ := by simp_rw [integral_const_mul]; rfl

/-- Expected weighted, integrated coefficient error vanishes on each fixed
horizon after the justified time/sample exchange. -/
-- @node: observed_KM_oracle_expected_weighted_time_energy_tendsto_zero
lemma observed_KM_oracle_expected_weighted_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (f : ℝ → ℝ)
    (hf : Measurable f) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, |f t| ≤ K) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) T,
        f t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  apply (observed_KM_oracle_weighted_time_energy_tendsto_zero c P hP a
    hT0 hT1 f hf hK hbound).congr'
  exact Filter.eventually_atTop.2 ⟨1, fun n hn =>
    (observed_KM_oracle_weighted_time_energy_integral_swap c P hP a
      (by omega) hT0 hT1 f hf hK hbound).symm⟩

/-- Only continuity on the study window is needed for deterministic
weights; zero extension supplies measurability without global regularity. -/
-- @node: observed_KM_oracle_expected_continuous_time_energy_tendsto_zero
lemma observed_KM_oracle_expected_continuous_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) T,
        f t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let g := (Icc (0 : ℝ) T).piecewise f (fun _ => 0)
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  have h := observed_KM_oracle_expected_weighted_time_energy_tendsto_zero
    c P hP a hT0 hT1 g hg (le_max_right K 0) (fun t ht => by
      simpa only [g, Set.piecewise, if_pos ht, Real.norm_eq_abs] using
        (hK t ht).trans (le_max_left K 0))
  convert h using 1
  funext n
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [g, Set.piecewise, if_pos ht]

/-- The recurrence intensity weighted coefficient error has vanishing
expected energy on every strict horizon. -/
-- @node: observed_KM_oracle_recurrence_time_energy_tendsto_zero
lemma observed_KM_oracle_recurrence_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) T,
        P.lam a t * (((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
            1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  exact observed_KM_oracle_expected_continuous_time_energy_tendsto_zero
    c P hP a hT0 hT1 (P.lam a) ((hP.recurrenceHolder a).1.continuousOn.mono
      (fun _ ht => ⟨ht.1, ht.2.trans hT1.le⟩))

/-- The deterministic remaining-target/death weight has vanishing expected
coefficient energy on each strict horizon. No future-mark plug-in is treated
as predictable in this result. -/
-- @node: observed_KM_oracle_death_time_energy_tendsto_zero
lemma observed_KM_oracle_death_time_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) T,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
          (((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
              1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  apply observed_KM_oracle_expected_continuous_time_energy_tendsto_zero c P hP a hT0 hT1
  have hc := (((continuousOn_remainingTarget_zero c P hP a).div
    (modelClass_survival_continuousOn c P hP a) (fun _ _ => (Real.exp_pos _).ne')).pow 2).mul
      (hP.deathHolder a).1.continuousOn
  convert hc.mono (fun (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) => ⟨ht.1, ht.2.trans hT1.le⟩) using 1
  funext t
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
