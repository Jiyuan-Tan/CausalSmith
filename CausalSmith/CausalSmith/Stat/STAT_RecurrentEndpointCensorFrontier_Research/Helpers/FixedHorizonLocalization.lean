module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPluginConvergence
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleCompensator

/-!
# Actual positive-risk localization on a strict horizon

Roadmap (9)--(10), (12), and (38): the observed iid risk marginal gives a
positive lower risk fraction with probability tending to one. Antitonicity
extends that event to every earlier time, controlling inverse-risk death
variation without independence. The future-mark plug-in comparison therefore
needs only its remaining pointwise-consistency input.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The actual observed risk fraction converges in probability to its exact
assignment, survival, and retention marginal. -/
-- @node: observed_riskFraction_probability_tendsto_zero
lemma observed_riskFraction_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(riskSet a s t : ℝ) / n -
        P.p a * survival P a t * retention P a t|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hlim := (observed_riskFraction_mean_abs_tendsto_zero c P hP a ht).div_const ε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi : Integrable (fun s : Fin n → ObsHistory => (riskSet a s t : ℝ) / n)
      (sampleLaw P n) := by
    simpa only [one_pow, mul_one] using
      DeathCP.integrable_observed_risk_weighted_sq P a t (fun _ => 1)
        measurable_const (B := 1) (by norm_num) (fun _ => by norm_num)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory =>
      abs_nonneg ((riskSet a s t : ℝ) / n -
        P.p a * survival P a t * retention P a t)))
    ((hi.sub (integrable_const _)).abs) ε
  have hsub : {s : Fin n → ObsHistory |
      ε < |(riskSet a s t : ℝ) / n - P.p a * survival P a t * retention P a t|} ⊆
      {s | ε ≤ |(riskSet a s t : ℝ) / n -
        P.p a * survival P a t * retention P a t|} := fun _ hs => (show ε < _ from hs).le
  apply (le_div_iff₀ hε).2
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness)) hε.le).trans hm

/-- Any fixed fraction strictly below the true horizon risk is eventually
exceeded by the empirical risk, in probability. -/
-- @node: observed_horizonRisk_lower_probability_tendsto_zero
lemma observed_horizonRisk_lower_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T q : ℝ} (hT : T ∈ Icc (0 : ℝ) 1)
    (hq : q < P.p a * survival P a T * retention P a T) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | (riskSet a s T : ℝ) < (n : ℝ) * q}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hε : 0 < P.p a * survival P a T * retention P a T - q := sub_pos.mpr hq
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (observed_riskFraction_probability_tendsto_zero c P hP a hT hε)
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  intro s hs
  change (riskSet a s T : ℝ) < (n : ℝ) * q at hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hy : (riskSet a s T : ℝ) / n < q :=
    (div_lt_iff₀ hnR).2 (by simpa only [mul_comm] using hs)
  change P.p a * survival P a T * retention P a T - q <
    |(riskSet a s T : ℝ) / n - P.p a * survival P a T * retention P a T|
  rw [abs_of_neg (sub_neg.mpr (hy.trans hq))]
  linarith

/-- Half of the true strict-horizon risk supplies a positive localization
constant, with failure probability tending to zero. -/
-- @node: exists_observed_horizonRisk_localization
lemma exists_observed_horizonRisk_localization
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ q : ℝ, 0 < q ∧ Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | (riskSet a s T : ℝ) < (n : ℝ) * q}) atTop (nhds 0) := by
  have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hg := retention_pos_of_modelClass c P hP a T hT0 hT1
  have hQ : 0 < P.p a * survival P a T * retention P a T :=
    mul_pos (mul_pos hp (Real.exp_pos _)) hg
  refine ⟨(P.p a * survival P a T * retention P a T) / 2, half_pos hQ, ?_⟩
  exact observed_horizonRisk_lower_probability_tendsto_zero c P hP a
    ⟨hT0, hT1.le⟩ (half_lt_self hQ)

/-- Horizon risk localization controls scaled inverse risk at every earlier
time, including the estimator's zero-risk convention. -/
-- @node: observed_uniform_scaledInvRisk_probability_tendsto_zero
lemma observed_uniform_scaledInvRisk_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ q : ℝ, 0 < q ∧ Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ∃ t ≤ T, q⁻¹ < (n : ℝ) * invRisk a s t}) atTop (nhds 0) := by
  obtain ⟨q, hq, hlim⟩ := exists_observed_horizonRisk_localization c P hP a hT0 hT1
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  refine ⟨q, hq, squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlim⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  rintro s ⟨t, ht, herr⟩
  by_contra hbad
  have hr : (n : ℝ) * q ≤ riskSet a s t :=
    (le_of_not_gt hbad).trans (by exact_mod_cast riskSet_antitone a s ht)
  exact (not_lt_of_ge (scaledInvRisk_le_of_riskFraction_lower (by omega) a s hq hr)) herr

/-- The localized inverse-risk squared death variation is bounded by a fixed
constant with probability tending to one, using actual horizon risk. -/
-- @node: observed_localizedDeathVariation_one_probability_tendsto_zero
lemma observed_localizedDeathVariation_one_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ q : ℝ, 0 < q ∧ Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | q⁻¹ ^ 2 < localizedDeathVariation a s T (fun _ => 1)}) atTop (nhds 0) := by
  obtain ⟨q, hq, hlim⟩ := exists_observed_horizonRisk_localization c P hP a hT0 hT1
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  refine ⟨q, hq, squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlim⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  intro s hs
  by_contra hbad
  have hr : (n : ℝ) * q ≤ riskSet a s T := le_of_not_gt hbad
  have hb := localizedDeathVariation_one_le a (by omega : 0 < n) s hq
    (fun i _ _ hi => hr.trans (by exact_mod_cast riskSet_antitone a s hi))
  exact (not_lt_of_ge hb) hs

/-- The actual model discharges the horizon-risk input of the future-mark
plug-in comparison. Only pointwise remaining-mean consistency remains. -/
-- @node: localizedDeathVariation_plugin_probability_tendsto_of_pointwise_modelClass
lemma localizedDeathVariation_plugin_probability_tendsto_of_pointwise_modelClass
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (hpoint : ∀ u ∈ Icc (0 : ℝ) T, ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (sampleLaw P n).real {s |
        η < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
        atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|}) atTop (nhds 0) := by
  obtain ⟨q, hq, hlim⟩ := exists_observed_horizonRisk_localization c P hP a hT0 hT1
  exact localizedDeathVariation_plugin_probability_tendsto_of_pointwise
    c P hP a hT0 hT1.le hq hlim hpoint

/-- The genuine dependent KM/risk coefficient converges to its oracle at
any strict-horizon time. Positive empirical risk converts the already proved
risk-weighted second moment into an ordinary probability bound. -/
-- @node: observed_KM_oracle_coefficient_probability_tendsto_zero
lemma observed_KM_oracle_coefficient_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)|}) atTop (nhds 0) := by
  obtain ⟨q, hq, hlim⟩ := exists_observed_horizonRisk_localization c P hP a ht0 ht1
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let C := 1 / (P.p a * retention P a t)
  let X := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    (n : ℝ) * deathKMLeft a s t * invRisk a s t - C
  let E := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    ((riskSet a s t : ℝ) / n) * X n s ^ 2
  have hEi (n : ℕ) : Integrable (E n) (sampleLaw P n) := by
    apply DeathCP.integrable_observed_risk_weighted_sq P a t (X n)
    · dsimp [X]
      fun_prop
    · exact add_nonneg (Nat.cast_nonneg n) (abs_nonneg C)
    · intro s
      have hk := deathKMLeft_mem_Icc a s t
      have hi := recurrence_invRisk_mem_Icc a s t
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hb : (n : ℝ) * deathKMLeft a s t * invRisk a s t ≤ n := by
        calc
          _ ≤ (n : ℝ) * 1 * 1 := by
            gcongr
            · exact hi.1
            · exact hk.2
            · exact hi.2
          _ = _ := by ring
      have h0 : 0 ≤ (n : ℝ) * deathKMLeft a s t * invRisk a s t :=
        mul_nonneg (mul_nonneg hnR hk.1) hi.1
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg h0]; linarith)
  have hE0 (n : ℕ) (s : Fin n → ObsHistory) : 0 ≤ E n s := by
    dsimp [E]; positivity
  have henergy := (DeathCP.observed_KM_oracle_coefficient_energy_tendsto_zero
    c P hP a ht0 ht1).div_const (q * ε ^ 2)
  have hsum : Tendsto (fun n => (sampleLaw P n).real
      {s | (riskSet a s t : ℝ) < (n : ℝ) * q} +
      (∫ s, E n s ∂sampleLaw P n) / (q * ε ^ 2)) atTop (nhds 0) := by
    simpa only [zero_div, add_zero, E, X, C] using hlim.add henergy
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : {s : Fin n → ObsHistory | ε < |X n s|} ⊆
      {s | (riskSet a s t : ℝ) < (n : ℝ) * q} ∪ {s | q * ε ^ 2 ≤ E n s} := by
    intro s hs
    by_cases hr : (riskSet a s t : ℝ) < (n : ℝ) * q
    · exact Or.inl hr
    · apply Or.inr
      have hy : q ≤ (riskSet a s t : ℝ) / n :=
        (le_div_iff₀ hnR).2 (by simpa only [mul_comm] using le_of_not_gt hr)
      have hx : ε ^ 2 ≤ X n s ^ 2 := by
        have h := (show ε < |X n s| from hs)
        nlinarith [sq_abs (X n s)]
      exact mul_le_mul hy hx (sq_nonneg ε) (div_nonneg (Nat.cast_nonneg _) hnR.le)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (hE0 n)) (hEi n) (q * ε ^ 2)
  have hmarkov : (sampleLaw P n).real {s | q * ε ^ 2 ≤ E n s} ≤
      (∫ s, E n s ∂sampleLaw P n) / (q * ε ^ 2) := by
    apply (le_div_iff₀ (mul_pos hq (sq_pos_of_pos hε))).2
    simpa only [mul_comm] using hm
  exact ((measureReal_mono hsub (by finiteness)).trans
    (measureReal_union_le _ _)).trans (add_le_add le_rfl hmarkov)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
