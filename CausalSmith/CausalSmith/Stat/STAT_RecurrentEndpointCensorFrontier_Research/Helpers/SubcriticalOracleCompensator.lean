module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalSquaredCoefficient
public import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Consistency of subcritical oracle compensators

Roadmap (31)--(32) and (39): the iid risk marginal converges in mean.
An inverse-retention envelope then integrates the oracle density error over
the entire horizon, including the unbounded endpoint weights.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed risk fraction converges in mean to its exact marginal. -/
-- @node: observed_riskFraction_mean_abs_tendsto_zero
lemma observed_riskFraction_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(riskSet a s t : ℝ) / n - P.p a * survival P a t * retention P a t|
      ∂sampleLaw P n) atTop (nhds 0) := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  let ξ : ObsHistory → ℝ := A.indicator (fun _ => 1)
  have hm : Measurable ξ := measurable_const.indicator hA
  have hξ : MemLp ξ 2 (observedLaw P) := by
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with o
    simp only [ξ, Set.indicator_apply]
    split_ifs <;> norm_num
  have hint : (∫ o, ξ o ∂observedLaw P) =
      P.p a * survival P a t * retention P a t := by
    rw [show ξ = A.indicator (fun _ => (1 : ℝ)) from rfl, integral_indicator hA]
    simpa [A] using observed_arm_risk_probability P hP a ht
  have hsum (n : ℕ) (s : Fin n → ObsHistory) :
      (∑ i, ξ (s i)) = (riskSet a s t : ℝ) := by
    simp [ξ, A, riskSet, Set.indicator_apply, Finset.sum_boole]
  have hlim : Tendsto (fun n : ℕ =>
      Real.sqrt ((∫ o, ξ o ^ 2 ∂observedLaw P) / n)) atTop (nhds 0) := by
    have h := ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul
      (∫ o, ξ o ^ 2 ∂observedLaw P)).sqrt
    simpa [div_eq_mul_inv] using h
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun s => abs_nonneg _)))
    _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := Causalean.Mathlib.Probability.iid_mean_abs_le (observedLaw P)
    (show 0 < n by omega) ξ hξ
  simpa only [hsum, hint, sampleLaw, div_eq_mul_inv, mul_comm] using h

/-- Nonnegativity and the exact risk marginal give a first-moment envelope
for its centered absolute deviation. -/
-- @node: observed_riskFraction_mean_abs_le_twice_marginal
lemma observed_riskFraction_mean_abs_le_twice_marginal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory,
      |(riskSet a s t : ℝ) / n - P.p a * survival P a t * retention P a t|
      ∂sampleLaw P n) ≤ 2 * (P.p a * survival P a t * retention P a t) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi : Integrable (fun s : Fin n → ObsHistory => (riskSet a s t : ℝ) / n)
      (sampleLaw P n) := by
    simpa only [one_pow, mul_one] using
      DeathCP.integrable_observed_risk_weighted_sq P a t (fun _ => 1)
        measurable_const (B := 1) (by norm_num) (fun _ => by norm_num)
  have hq : 0 ≤ P.p a * survival P a t * retention P a t := by
    rw [← DeathCP.observed_integral_riskFraction_eq c P hP a hn ht]
    exact integral_nonneg (fun _ => by positivity)
  calc
    _ ≤ ∫ s : Fin n → ObsHistory,
        (riskSet a s t : ℝ) / n + P.p a * survival P a t * retention P a t
        ∂sampleLaw P n := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => abs_nonneg _)) (hi.add (integrable_const _))
      (Eventually.of_forall (fun s => by
        simpa only [abs_of_nonneg (show 0 ≤ (riskSet a s t : ℝ) / n by positivity),
          abs_of_nonneg hq] using abs_sub ((riskSet a s t : ℝ) / n)
            (P.p a * survival P a t * retention P a t)))
    _ = _ := by rw [integral_add hi (integrable_const _),
      DeathCP.observed_integral_riskFraction_eq c P hP a hn ht]; simp; ring

/-- The centered oracle density has vanishing integrated absolute error in
mean on the full horizon. The envelope cancels one inverse-retention factor. -/
-- @node: subcritical_oracle_density_mean_abs_tendsto_zero
lemma subcritical_oracle_density_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1,
      |f t| * (1 / (P.p a * retention P a t)) ^ 2 *
        (∫ s : Fin n → ObsHistory,
          |(riskSet a s t : ℝ) / n -
            P.p a * survival P a t * retention P a t| ∂sampleLaw P n))
      atTop (nhds 0) := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let S : ℝ → ℝ := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hS : Measurable S := (modelClass_survival_continuousOn c P hP a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hSeq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : S t = survival P a t :=
    piecewise_eq_of_mem _ _ _ ⟨ht.1.le, ht.2.le⟩
  let E := fun (n : ℕ) (t : ℝ) =>
    |f t| * (1 / (P.p a * retention P a t)) ^ 2 *
      (∫ s : Fin n → ObsHistory,
        |(riskSet a s t : ℝ) / n - P.p a * S t * retention P a t| ∂sampleLaw P n)
  have hm (n : ℕ) : Measurable (E n) := by
    have hg : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    have hs : Measurable (fun p : (Fin n → ObsHistory) × ℝ => S p.2) :=
      hS.comp measurable_snd
    have hh : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
        |(riskSet a p.1 p.2 : ℝ) / n - P.p a * S p.2 * retention P a p.2|) := by
      fun_prop
    exact ((hf.abs.mul ((measurable_const.div
      (measurable_const.mul (measurable_retention P a))).pow_const 2)).mul
        hh.stronglyMeasurable.integral_prod_left'.measurable)
  have hi := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => survival P a t * |f t|)
    ((modelClass_survival_continuousOn c P hP a).mul hc.abs)).const_mul (2 / P.p a)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖E n t‖ ≤ (2 / P.p a) * (survival P a t * |f t| / retention P a t) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
    have hg := retention_pos_of_modelClass c P hP a t ht.1.le ht.2
    dsimp [E]
    rw [hSeq t ht, abs_of_nonneg (by positivity)]
    calc
      _ ≤ |f t| * (1 / (P.p a * retention P a t)) ^ 2 *
          (2 * (P.p a * survival P a t * retention P a t)) :=
        mul_le_mul_of_nonneg_left
          (observed_riskFraction_mean_abs_le_twice_marginal c P hP a
            (by omega) ⟨ht.1.le, ht.2.le⟩) (by positivity)
      _ = _ := by field_simp
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun n => E n t) atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [E, hSeq t ht, mul_zero] using
      (observed_riskFraction_mean_abs_tendsto_zero c P hP a ⟨ht.1.le, ht.2.le⟩).const_mul
        (|f t| * (1 / (P.p a * retention P a t)) ^ 2)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun t => (2 / P.p a) * (survival P a t * |f t| / retention P a t))
    (Eventually.of_forall (fun n => (hm n).aestronglyMeasurable)) hbound hi hpoint
  simp only [integral_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [E, hSeq t ht]

/-- The centered full-horizon oracle density is product-integrable. This
justifies exchanging sample expectation and time for its absolute error. -/
-- @node: subcritical_oracle_centered_density_integrable_prod
lemma subcritical_oracle_centered_density_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      f p.2 * (1 / (P.p a * retention P a p.2)) ^ 2 *
        ((riskSet a p.1 p.2 : ℝ) / n -
          P.p a * survival P a p.2 * retention P a p.2))
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => survival P a t * f t)
    ((modelClass_survival_continuousOn c P hP a).mul hc)).const_mul (P.p a)⁻¹
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have hj := (subcritical_oracle_energy_integrable_prod c P hP hk a hn f hf hc).sub
    (hi.comp_snd (sampleLaw P n))
  apply hj.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem measurableSet_Ioo)] with p hp
  have hpa : P.p a ≠ 0 := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).ne'
  have hg : retention P a p.2 ≠ 0 :=
    (retention_pos_of_modelClass c P hP a p.2 hp.1.le hp.2).ne'
  simp only [Pi.sub_apply]
  field_simp

/-- Fubini transfers the integrated marginal oracle density convergence to
mean convergence of the sample's integrated absolute density error. -/
-- @node: subcritical_oracle_integrated_density_mean_tendsto_zero
lemma subcritical_oracle_integrated_density_mean_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Ioo (0 : ℝ) 1,
        |f t * (1 / (P.p a * retention P a t)) ^ 2 *
          ((riskSet a s t : ℝ) / n -
            P.p a * survival P a t * retention P a t)|) ∂sampleLaw P n)
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply (subcritical_oracle_density_mean_abs_tendsto_zero c P hP hk a f hf hc).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := (subcritical_oracle_centered_density_integrable_prod c P hP hk a
    (show 0 < n by omega) f hf hc).norm
  simp only [Real.norm_eq_abs] at hi
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with t
  simp_rw [abs_mul, abs_of_nonneg (sq_nonneg (1 / (P.p a * retention P a t)))]
  rw [integral_const_mul]

/-- The full oracle compensator converges in mean to its population variance
integral. Only a first moment of the endpoint-weighted density is used. -/
-- @node: subcritical_oracle_compensator_mean_abs_tendsto_zero
lemma subcritical_oracle_compensator_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(∫ t in Ioo (0 : ℝ) 1,
          f t * (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t| ∂sampleLaw P n)
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    _ (subcritical_oracle_integrated_density_mean_tendsto_zero c P hP hk a f hf hc)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ho := subcritical_oracle_energy_integrable_prod c P hP hk a (show 0 < n by omega) f hf hc
  have he := subcritical_oracle_centered_density_integrable_prod c P hP hk a
    (show 0 < n by omega) f hf hc
  have hd := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => survival P a t * f t)
    ((modelClass_survival_continuousOn c P hP a).mul hc)).const_mul (P.p a)⁻¹
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hd
  have habs := he.norm.integral_prod_left
  simp only [Real.norm_eq_abs] at habs
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) habs
  filter_upwards [ho.prod_right_ae] with s hs
  rw [← integral_const_mul, ← integral_sub hs hd]
  calc
    _ = |∫ t in Ioo (0 : ℝ) 1,
        f t * (1 / (P.p a * retention P a t)) ^ 2 *
          ((riskSet a s t : ℝ) / n - P.p a * survival P a t * retention P a t)| := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).ne'
      have hg : retention P a t ≠ 0 :=
        (retention_pos_of_modelClass c P hP a t ht.1.le ht.2).ne'
      field_simp
        _ ≤ _ := abs_integral_le_integral_abs

/-- The full-horizon oracle compensator converges in probability. -/
-- @node: subcritical_oracle_compensator_probability_tendsto_zero
lemma subcritical_oracle_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1,
          f t * (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    |(∫ t in Ioo (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
      (1 / (P.p a * retention P a t)) ^ 2)) -
      (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1, survival P a t * f t / retention P a t|
  have hlim :=
    (subcritical_oracle_compensator_mean_abs_tendsto_zero c P hP hk a f hf hc).div_const ε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := (subcritical_oracle_energy_integrable_prod c P hP hk a
    (show 0 < n by omega) f hf hc).integral_prod_left
  have hFi : Integrable (F n) (sampleLaw P n) := by
    simpa only [F, Real.norm_eq_abs, Pi.sub_apply] using (hi.sub (integrable_const _)).norm
  have hb := mul_meas_ge_le_integral_of_nonneg
    (f := F n) (Eventually.of_forall (fun s => abs_nonneg _)) hFi ε
  have hsub : (sampleLaw P n).real {s | ε < F n s} ≤
      (sampleLaw P n).real {s | ε ≤ F n s} :=
    measureReal_mono (fun s (hs : ε < F n s) => hs.le) (by finiteness)
  change (sampleLaw P n).real {s | ε < F n s} ≤ (∫ s, F n s ∂sampleLaw P n) / ε
  apply (le_div_iff₀ hε).2
  exact (mul_le_mul_of_nonneg_right hsub hε.le).trans (by rw [mul_comm]; exact hb)

/-- Window-only continuity suffices for oracle compensator consistency;
no global measurability premise on the hazards is imposed. -/
-- @node: subcritical_oracle_compensator_probability_tendsto_zero_of_continuousOn
lemma subcritical_oracle_compensator_probability_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1,
          f t * (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
          survival P a t * f t / retention P a t|}) atTop (nhds 0) := by
  classical
  let g : ℝ → ℝ := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hc.congr he
  have hleft (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) 1, g t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2)) =
      ∫ t in Ioo (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  have hright : (∫ t in Ioo (0 : ℝ) 1, survival P a t * g t / retention P a t) =
      ∫ t in Ioo (0 : ℝ) 1, survival P a t * f t / retention P a t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  simpa only [hleft, hright] using
    subcritical_oracle_compensator_probability_tendsto_zero c P hP hk a g hg hgc hε

/-- The recurrence oracle compensator converges to the stated recurrence
variance contribution on the entire subcritical horizon. -/
-- @node: subcritical_recurrence_oracle_compensator_probability_tendsto_zero
lemma subcritical_recurrence_oracle_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1,
          P.lam a t * (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2)) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          survival P a t * P.lam a t / retention P a t|}) atTop (nhds 0) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  exact subcritical_oracle_compensator_probability_tendsto_zero_of_continuousOn
    c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn hε

/-- The deterministic death oracle compensator converges to the stated death
variance contribution; future recurrence marks are not treated as predictable. -/
-- @node: subcritical_death_oracle_compensator_probability_tendsto_zero
lemma subcritical_death_oracle_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) 1,
          ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
            (((riskSet a s t : ℝ) / n) * (1 / (P.p a * retention P a t)) ^ 2)) -
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
  exact subcritical_oracle_compensator_probability_tendsto_zero_of_continuousOn c P hP hk a _ hc hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
