module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.InverseRiskCompensator

/-!
# Integrated inverse-risk death compensator

Roadmap (39): transfer the full-horizon marginal inverse-risk error to the
actual time integral by Fubini and the integral triangle inequality. The
integrable endpoint envelope comes from subcritical retention.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: subcritical_inverseRisk_compensator_integrable_prod
lemma subcritical_inverseRisk_compensator_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      f p.2 * ((n : ℝ) * invRisk a p.1 p.2))
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply Integrable.of_bound (by fun_prop) (max K 0 * n)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem measurableSet_Ioo)] with p hp
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (DeathCP.scaledInvRisk_mem_Icc a p.1 p.2).1]
  have hb : |f p.2| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK p.2 ⟨hp.1.le, hp.2.le⟩
  exact mul_le_mul
    (hb.trans (le_max_left K 0))
    (DeathCP.scaledInvRisk_mem_Icc a p.1 p.2).2
    (DeathCP.scaledInvRisk_mem_Icc a p.1 p.2).1 (le_max_right K 0)

-- @node: subcritical_inverseRisk_centered_density_integrable_prod
lemma subcritical_inverseRisk_centered_density_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) (f : ℝ → ℝ)
    (hf : Measurable f) (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      f p.2 * ((n : ℝ) * invRisk a p.1 p.2 -
        1 / (P.p a * survival P a p.2 * retention P a p.2)))
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => f t / survival P a t)
    (hc.div (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne'))).const_mul (P.p a)⁻¹
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have he := (subcritical_inverseRisk_compensator_integrable_prod c P hP a n f hf hc).sub
    (hi.comp_snd (sampleLaw P n))
  convert he using 1
  funext p
  simp only [Pi.sub_apply, div_eq_mul_inv, mul_inv_rev]
  ring

-- @node: subcritical_inverseRisk_integrated_density_mean_tendsto_zero
lemma subcritical_inverseRisk_integrated_density_mean_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Ioo (0 : ℝ) 1,
        |f t * ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t))|) ∂sampleLaw P n)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply (subcritical_inverseRisk_density_mean_abs_tendsto_zero c P hP hk a f hf hc).congr'
  apply Eventually.of_forall
  intro n
  have hi := (subcritical_inverseRisk_centered_density_integrable_prod
    c P hP hk a n f hf hc).norm
  simp only [Real.norm_eq_abs] at hi
  dsimp only
  rw [integral_integral_swap hi]
  simp_rw [abs_mul, integral_const_mul]

-- @node: subcritical_inverseRisk_compensator_mean_abs_tendsto_zero
lemma subcritical_inverseRisk_compensator_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(∫ t in Ioo (0 : ℝ) 1, f t * ((n : ℝ) * invRisk a s t)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          (f t / survival P a t) / retention P a t| ∂sampleLaw P n)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _
    (subcritical_inverseRisk_integrated_density_mean_tendsto_zero c P hP hk a f hf hc)
  intro n
  have he := subcritical_inverseRisk_compensator_integrable_prod c P hP a n f hf hc
  have hd := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => f t / survival P a t)
    (hc.div (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne'))).const_mul (P.p a)⁻¹
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hd
  have hi := (subcritical_inverseRisk_centered_density_integrable_prod
    c P hP hk a n f hf hc).norm.integral_prod_left
  simp only [Real.norm_eq_abs] at hi
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) hi
  filter_upwards [he.prod_right_ae] with s hs
  rw [← integral_const_mul, ← integral_sub hs hd]
  calc
    _ = |∫ t in Ioo (0 : ℝ) 1, f t * ((n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t))| := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := abs_integral_le_integral_abs


-- @node: subcritical_inverseRisk_compensator_probability_tendsto_zero
lemma subcritical_inverseRisk_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1, f t * ((n : ℝ) * invRisk a s t)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          (f t / survival P a t) / retention P a t|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    |(∫ t in Ioo (0 : ℝ) 1, f t * ((n : ℝ) * invRisk a s t)) -
      (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1, (f t / survival P a t) / retention P a t|
  have ht := (subcritical_inverseRisk_compensator_mean_abs_tendsto_zero
    c P hP hk a f hf hc).div_const ε
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [zero_div] using ht)
  intro n
  have hi := (subcritical_inverseRisk_compensator_integrable_prod c P hP a n f hf hc).integral_prod_left
  have hFi : Integrable (F n) (sampleLaw P n) := (hi.sub (integrable_const _)).abs
  have hb := mul_meas_ge_le_integral_of_nonneg
    (f := F n) (Eventually.of_forall (fun _ => abs_nonneg _)) hFi ε
  have hsub : (sampleLaw P n).real {s | ε < F n s} ≤
      (sampleLaw P n).real {s | ε ≤ F n s} :=
    measureReal_mono (fun s (hs : ε < F n s) => hs.le) (by finiteness)
  change (sampleLaw P n).real {s | ε < F n s} ≤ (∫ s, F n s ∂sampleLaw P n) / ε
  apply (le_div_iff₀ hε).2
  exact (mul_le_mul_of_nonneg_right hsub hε.le).trans (by rw [mul_comm]; exact hb)

/-- Only study-window continuity is required for a deterministic death weight. -/
-- @node: subcritical_inverseRisk_compensator_probability_tendsto_zero_of_continuousOn
lemma subcritical_inverseRisk_compensator_probability_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1, f t * ((n : ℝ) * invRisk a s t)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          (f t / survival P a t) / retention P a t|}) atTop (nhds 0) := by
  classical
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  have hi (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1, g t * ((n : ℝ) * invRisk a s t)) =
        ∫ t in Ioo (0 : ℝ) 1, f t * ((n : ℝ) * invRisk a s t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  have hj : (∫ t in Ioo (0 : ℝ) 1, (g t / survival P a t) / retention P a t) =
      ∫ t in Ioo (0 : ℝ) 1, (f t / survival P a t) / retention P a t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  simpa only [hi, hj] using
    subcritical_inverseRisk_compensator_probability_tendsto_zero c P hP hk a g hg
      (hc.congr he) hε

/-- The exact full-horizon drift of the deterministic remaining-target death
optional variation converges to the death term in the stated variance. -/
-- @node: subcritical_death_variation_compensator_probability_tendsto_limit
lemma subcritical_death_variation_compensator_probability_tendsto_limit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
          remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)|}) atTop (nhds 0) := by
  have hc : ContinuousOn (fun t => remainingTarget c P a 0 t ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) :=
    ((continuousOn_remainingTarget_zero c P hP a).pow 2).mul
      (hP.deathHolder a).1.continuousOn
  have hi (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1,
        (remainingTarget c P a 0 t ^ 2 * P.hazard a t) * ((n : ℝ) * invRisk a s t)) =
      (n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hj : (∫ t in Ioo (0 : ℝ) 1,
      ((remainingTarget c P a 0 t ^ 2 * P.hazard a t) / survival P a t) / retention P a t) =
      ∫ t in (0 : ℝ)..1,
        remainingTarget c P a 0 t ^ 2 * P.hazard a t / (survival P a t * retention P a t) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [div_mul_eq_div_div]
  simpa only [hi, hj] using
    subcritical_inverseRisk_compensator_probability_tendsto_zero_of_continuousOn
      c P hP hk a _ hc hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
