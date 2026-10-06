module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleCompensator

/-!
# Empirical subcritical compensator limits

The full-horizon squared-coefficient comparison transfers the oracle
compensator LLN to the empirical KM/inverse-risk compensator in mean and
probability. This proves
the drift limits in roadmap (31)--(32) and (39), without factorizing dependent
coefficients or imposing bounded endpoint oracle weights. Optional martingale
remainders and the future-mark death plug-in are separate obligations.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The empirical squared-coefficient density is product-integrable on the
full subcritical horizon. Young's bound uses the actual dependent coefficient
error and the oracle energy. -/
-- @node: subcritical_empirical_compensator_integrable_prod
lemma subcritical_empirical_compensator_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : ∀ t, 0 ≤ f t) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      f p.2 * ((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let μ := (sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))
  let W := fun p : (Fin n → ObsHistory) × ℝ => f p.2 * ((riskSet a p.1 p.2 : ℝ) / n)
  let A := fun p : (Fin n → ObsHistory) × ℝ =>
    (n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2
  let B := fun p : (Fin n → ObsHistory) × ℝ => 1 / (P.p a * retention P a p.2)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have he : Integrable (fun p => W p * (A p - B p) ^ 2) μ := by
    simpa only [W, A, B, μ, mul_assoc] using
      DeathCP.observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
        c P hP a hk hn f hf (le_max_right K 0) (fun t ht => by
          simpa only [Real.norm_eq_abs] using
            (hK t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left K 0))
  have hb : Integrable (fun p => W p * B p ^ 2) μ := by
    simpa only [W, B, μ, mul_assoc] using
      subcritical_oracle_energy_integrable_prod c P hP hk a hn f hf hc
  have hm : Measurable (fun p => W p * A p ^ 2) := by
    dsimp [W, A]
    fun_prop
  apply ((he.const_mul 2).add (hb.const_mul 2)).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  have hw : 0 ≤ W p := mul_nonneg (hf0 _) (by positivity)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  nlinarith [mul_nonneg hw (sq_nonneg (A p - 2 * B p))]

/-- The absolute empirical/oracle compensator difference is controlled by
the integrated squared-coefficient difference, almost surely. -/
-- @node: subcritical_empirical_oracle_compensator_abs_le_ae
lemma subcritical_empirical_oracle_compensator_abs_le_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : ∀ t, 0 ≤ f t) :
    ∀ᵐ s ∂sampleLaw P n,
      |(∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (∫ t in Ioo (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
          (1 / (P.p a * retention P a t)) ^ 2))| ≤
      ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2| := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have he := subcritical_empirical_compensator_integrable_prod c P hP hk a hn f hf hc hf0
  have hb := subcritical_oracle_energy_integrable_prod c P hP hk a hn f hf hc
  filter_upwards [he.prod_right_ae, hb.prod_right_ae] with s hs ht
  rw [← integral_sub hs ht]
  calc
    _ ≤ ∫ t in Ioo (0 : ℝ) 1,
        |f t * ((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          f t * (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2)| := abs_integral_le_integral_abs
    _ = _ := by
      congr 1
      funext t
      have heq : f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
        f t * (((riskSet a s t : ℝ) / n) *
          (1 / (P.p a * retention P a t)) ^ 2) =
        (f t * ((riskSet a s t : ℝ) / n)) *
          (((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
            (1 / (P.p a * retention P a t)) ^ 2) := by ring
      rw [heq, abs_mul, abs_of_nonneg (mul_nonneg (hf0 _) (by positivity))]

/-- The empirical compensator converges in mean to its population variance
contribution, retaining the full endpoint and the dependent squared coefficient. -/
-- @node: subcritical_empirical_compensator_mean_abs_tendsto_zero
lemma subcritical_empirical_compensator_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : ∀ t, 0 ≤ f t) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t| ∂sampleLaw P n)
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let A := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2
  let B := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    ∫ t in Ioo (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
      (1 / (P.p a * retention P a t)) ^ 2)
  let D := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
      |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
        (1 / (P.p a * retention P a t)) ^ 2|
  let V := (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
    survival P a t * f t / retention P a t
  have hlim := (subcritical_squared_coefficient_mean_tendsto_zero
    c P hP hk a f hf hc hf0).add
      (subcritical_oracle_compensator_mean_abs_tendsto_zero c P hP hk a f hf hc)
  apply squeeze_zero' (Eventually.of_forall (fun _ =>
    integral_nonneg (fun _ => abs_nonneg _))) _
      (by simpa only [add_zero] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := by omega
  have he := subcritical_empirical_compensator_integrable_prod c P hP hk a hn0 f hf hc hf0
  have hb := subcritical_oracle_energy_integrable_prod c P hP hk a hn0 f hf hc
  have hd : Integrable (D n) (sampleLaw P n) := by
    have hdiff := (he.sub hb).norm
    simp only [Real.norm_eq_abs, Pi.sub_apply] at hdiff
    have heq : (fun p : (Fin n → ObsHistory) × ℝ =>
        |f p.2 * ((riskSet a p.1 p.2 : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2) ^ 2 -
          f p.2 * (((riskSet a p.1 p.2 : ℝ) / n) *
            (1 / (P.p a * retention P a p.2)) ^ 2)|) =
      (fun p : (Fin n → ObsHistory) × ℝ =>
        f p.2 * ((riskSet a p.1 p.2 : ℝ) / n) *
          |((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2) ^ 2 -
            (1 / (P.p a * retention P a p.2)) ^ 2|) := by
      funext p
      have hx : f p.2 * ((riskSet a p.1 p.2 : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2) ^ 2 -
        f p.2 * (((riskSet a p.1 p.2 : ℝ) / n) *
          (1 / (P.p a * retention P a p.2)) ^ 2) =
        (f p.2 * ((riskSet a p.1 p.2 : ℝ) / n)) *
          (((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2) ^ 2 -
            (1 / (P.p a * retention P a p.2)) ^ 2) := by ring
      rw [hx, abs_mul, abs_of_nonneg (mul_nonneg (hf0 _) (by positivity))]
    rw [heq] at hdiff
    exact hdiff.integral_prod_left
  have hbi : Integrable (fun s => |B n s - V|) (sampleLaw P n) :=
    (hb.integral_prod_left.sub (integrable_const V)).abs
  change (∫ s, |A n s - V| ∂sampleLaw P n) ≤
    (∫ s, D n s ∂sampleLaw P n) + (∫ s, |B n s - V| ∂sampleLaw P n)
  rw [← integral_add hd hbi]
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) (hd.add hbi)
  filter_upwards [subcritical_empirical_oracle_compensator_abs_le_ae
    c P hP hk a hn0 f hf hc hf0] with s hs
  exact (abs_sub_le (A n s) (B n s) V).trans (add_le_add hs le_rfl)

/-- The empirical compensator converges to its population variance integral
on the entire horizon. Markov's inequality applies to its derived mean
absolute error; no independence between risk and KM factors is asserted. -/
-- @node: subcritical_empirical_compensator_probability_tendsto_zero
lemma subcritical_empirical_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : ∀ t, 0 ≤ f t)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    |(∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
      (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
        survival P a t * f t / retention P a t|
  have hlim := (subcritical_empirical_compensator_mean_abs_tendsto_zero
    c P hP hk a f hf hc hf0).div_const ε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := (subcritical_empirical_compensator_integrable_prod c P hP hk a
    (show 0 < n by omega) f hf hc hf0).integral_prod_left
  have hFi : Integrable (F n) (sampleLaw P n) :=
    (hi.sub (integrable_const _)).abs
  have hm := mul_meas_ge_le_integral_of_nonneg
    (f := F n) (Eventually.of_forall (fun _ => abs_nonneg _)) hFi ε
  have hsub : (sampleLaw P n).real {s | ε < F n s} ≤
      (sampleLaw P n).real {s | ε ≤ F n s} :=
    measureReal_mono (fun s (hs : ε < F n s) => hs.le) (by finiteness)
  change (sampleLaw P n).real {s | ε < F n s} ≤ (∫ s, F n s ∂sampleLaw P n) / ε
  apply (le_div_iff₀ hε).2
  exact (mul_le_mul_of_nonneg_right hsub hε.le).trans (by rw [mul_comm]; exact hm)

/-- Study-window continuity and nonnegativity suffice for the empirical
compensator limit; hazards need no globally regular extension. -/
-- @node: subcritical_empirical_compensator_probability_tendsto_zero_of_continuousOn
lemma subcritical_empirical_compensator_probability_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t|}) atTop (nhds 0) := by
  classical
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t :=
    piecewise_eq_of_mem _ _ _ ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hc.congr he
  have hg0 (t : ℝ) : 0 ≤ g t := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [he t ht]; exact hf0 t ht
    · simp only [g, Set.piecewise, if_neg ht, le_refl]
  have hleft (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1, g t * ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) =
      ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  have hright : (∫ t in Ioo (0 : ℝ) 1, survival P a t * g t / retention P a t) =
      ∫ t in Ioo (0 : ℝ) 1, survival P a t * f t / retention P a t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  simpa only [hleft, hright] using
    subcritical_empirical_compensator_probability_tendsto_zero c P hP hk a g hg hgc hg0 hε

/-- The actual recurrence drift in roadmap (31) converges to the recurrence
part of the subcritical variance. -/
-- @node: subcritical_recurrence_empirical_compensator_probability_tendsto_zero
lemma subcritical_recurrence_empirical_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1, P.lam a t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          survival P a t * P.lam a t / retention P a t|}) atTop (nhds 0) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  exact subcritical_empirical_compensator_probability_tendsto_zero_of_continuousOn
    c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn
    (fun t ht => c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1) hε

/-- The deterministic-target death drift in roadmap (39) converges to the
death part of the subcritical variance. This does not insert future marks
into a predictable stochastic integrand. -/
-- @node: subcritical_death_empirical_compensator_probability_tendsto_zero
lemma subcritical_death_empirical_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1,
          ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
          ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)|}) atTop (nhds 0) := by
  have hc : ContinuousOn (fun t =>
      (remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) :=
    (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  have he : (∫ t in (0 : ℝ)..1, remainingTarget c P a 0 t ^ 2 * P.hazard a t /
      (survival P a t * retention P a t)) =
      ∫ t in Ioo (0 : ℝ) 1, survival P a t *
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) /
          retention P a t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [] with t
    have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [he]
  exact subcritical_empirical_compensator_probability_tendsto_zero_of_continuousOn
    c P hP hk a _ hc
    (fun t ht => mul_nonneg (sq_nonneg _)
      (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)) hε

/-- The risk-weighted normalized square equals the actual inverse-risk
compensator density, including the totalized zero-risk case. -/
-- @node: empirical_compensator_density_eq
lemma empirical_compensator_density_eq {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (f : ℝ) :
    f * ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 =
    (n : ℝ) * (deathKMLeft a s t) ^ 2 * invRisk a s t * f := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hr : riskSet a s t = 0
  · simp [invRisk, hr]
  have hr' : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  simp only [invRisk, if_neg hr]
  field_simp

/-- The recurrence drift is written in the exact normalization of the
observable recurrence variation in (31). -/
-- @node: subcritical_recurrence_actual_compensator_probability_tendsto_zero
lemma subcritical_recurrence_actual_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
          (deathKMLeft a s t) ^ 2 * invRisk a s t * P.lam a t) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          survival P a t * P.lam a t / retention P a t|}) atTop (nhds 0) := by
  have he (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1, P.lam a t * ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) =
      (n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        (deathKMLeft a s t) ^ 2 * invRisk a s t * P.lam a t) := by
    simp_rw [empirical_compensator_density_eq, mul_assoc]
    rw [integral_const_mul]
  simpa only [he] using
    subcritical_recurrence_empirical_compensator_probability_tendsto_zero c P hP hk a hε

/-- The deterministic death drift is written in the exact normalization of
(39), before the pathwise replacement by the future-mark plug-in. -/
-- @node: subcritical_death_actual_compensator_probability_tendsto_zero
lemma subcritical_death_actual_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
          (deathKMLeft a s t) ^ 2 * invRisk a s t *
            ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)|}) atTop (nhds 0) := by
  have he (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
        ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) =
      (n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        (deathKMLeft a s t) ^ 2 * invRisk a s t *
          ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)) := by
    simp_rw [empirical_compensator_density_eq, mul_assoc]
    rw [integral_const_mul]
  simpa only [he] using
    subcritical_death_empirical_compensator_probability_tendsto_zero c P hP hk a hε

/-- Continuity and nonnegativity on the study window suffice for the mean
limit; the hazards need no regular extension outside that window. -/
-- @node: subcritical_empirical_compensator_mean_abs_tendsto_zero_of_continuousOn
lemma subcritical_empirical_compensator_mean_abs_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t| ∂sampleLaw P n)
      atTop (nhds 0) := by
  classical
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hc.congr he
  have hg0 (t : ℝ) : 0 ≤ g t := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [he t ht]; exact hf0 t ht
    · simp only [g, Set.piecewise, if_neg ht, le_refl]
  have hA (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1, g t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) =
      ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
          ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  have hV : (∫ t in Ioo (0 : ℝ) 1, survival P a t * g t / retention P a t) =
      ∫ t in Ioo (0 : ℝ) 1, survival P a t * f t / retention P a t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  simpa only [hA, hV] using
    subcritical_empirical_compensator_mean_abs_tendsto_zero c P hP hk a g hg hgc hg0

/-- The recurrence drift in the observable optional variation converges in
mean on the full subcritical horizon. -/
-- @node: subcritical_recurrence_actual_compensator_mean_abs_tendsto_zero
lemma subcritical_recurrence_actual_compensator_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
          (deathKMLeft a s t) ^ 2 * invRisk a s t * P.lam a t) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          survival P a t * P.lam a t / retention P a t| ∂sampleLaw P n)
      atTop (nhds 0) := by
  have he (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1, P.lam a t * ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) =
      (n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        (deathKMLeft a s t) ^ 2 * invRisk a s t * P.lam a t) := by
    simp_rw [empirical_compensator_density_eq, mul_assoc]
    rw [integral_const_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  simpa only [he] using
    subcritical_empirical_compensator_mean_abs_tendsto_zero_of_continuousOn
      c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn
      (fun t ht => c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)

/-- The deterministic remaining-target death drift converges in mean.
No predictability of the future-mark estimator enters this compensator limit. -/
-- @node: subcritical_death_actual_compensator_mean_abs_tendsto_zero
lemma subcritical_death_actual_compensator_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
          (deathKMLeft a s t) ^ 2 * invRisk a s t *
            ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)| ∂sampleLaw P n)
      atTop (nhds 0) := by
  have hc : ContinuousOn (fun t =>
      (remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) :=
    (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  have hV : (∫ t in (0 : ℝ)..1, remainingTarget c P a 0 t ^ 2 * P.hazard a t /
      (survival P a t * retention P a t)) =
      ∫ t in Ioo (0 : ℝ) 1, survival P a t *
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) /
          retention P a t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [] with t
    have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  have he (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
        ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2) =
      (n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        (deathKMLeft a s t) ^ 2 * invRisk a s t *
          ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)) := by
    simp_rw [empirical_compensator_density_eq, mul_assoc]
    rw [integral_const_mul]
  rw [hV]
  simpa only [he] using
    subcritical_empirical_compensator_mean_abs_tendsto_zero_of_continuousOn c P hP hk a _ hc
      (fun t ht => mul_nonneg (sq_nonneg _)
        (c.dMin_pos.le.trans (hP.deathBounds a t ht).1))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
