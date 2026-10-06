module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRiskSet
public import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Full-horizon risk localization under positive retention

Roadmap (17)--(18) and (23)--(24): the empirical risk fraction converges
under the benchmark assumptions, including at time one. Terminal risk
then controls the inverse risk coefficient simultaneously at all earlier times.
No endpoint power law or hazard smoothness is imposed.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed risk fraction converges in mean to its exact marginal. -/
-- @node: positiveRetention_riskFraction_mean_abs_tendsto_zero
lemma positiveRetention_riskFraction_mean_abs_tendsto_zero
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (a : Arm)
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
    simpa [A] using positiveRetention_observed_arm_risk_probability
      P hRandom hAssignment hDeath hCensor a ht
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

/-- The actual observed risk fraction converges in probability to its exact
assignment, survival, and retention marginal. -/
-- @node: positiveRetention_riskFraction_probability_tendsto_zero
lemma positiveRetention_riskFraction_probability_tendsto_zero
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (a : Arm)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(riskSet a s t : ℝ) / n -
        P.p a * survival P a t * retention P a t|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hlim := (positiveRetention_riskFraction_mean_abs_tendsto_zero
    P hRandom hAssignment hDeath hCensor a ht).div_const ε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi : Integrable (fun s : Fin n → ObsHistory => (riskSet a s t : ℝ) / n)
      (sampleLaw P n) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_one (by exact_mod_cast (show 0 < n by omega))).2
    exact_mod_cast (show riskSet a s t ≤ n from
      (Finset.card_filter_le _ _).trans (by simp))
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
-- @node: positiveRetention_horizonRisk_lower_probability_tendsto_zero
lemma positiveRetention_horizonRisk_lower_probability_tendsto_zero
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (a : Arm)
    {T q : ℝ} (hT : T ∈ Icc (0 : ℝ) 1)
    (hq : q < P.p a * survival P a T * retention P a T) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | (riskSet a s T : ℝ) < (n : ℝ) * q}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hε : 0 < P.p a * survival P a T * retention P a T - q := sub_pos.mpr hq
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (positiveRetention_riskFraction_probability_tendsto_zero
      P hRandom hAssignment hDeath hCensor a hT hε)
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

/-- Half the uniform population-risk lower bound localizes empirical terminal
risk, including the study endpoint. -/
-- @node: positiveRetention_terminalRisk_localization
lemma positiveRetention_terminalRisk_localization
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    0 < c.pMin * Real.exp (-c.dMax) * c.Ghor / 2 ∧
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | (riskSet a s 1 : ℝ) <
        (n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor / 2)})
      atTop (nhds 0) := by
  have hq : 0 < c.pMin * Real.exp (-c.dMax) * c.Ghor :=
    mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  refine ⟨half_pos hq, ?_⟩
  apply positiveRetention_horizonRisk_lower_probability_tendsto_zero
    P hRandom hAssignment hDeath hCensor a (by norm_num)
  exact (half_lt_self hq).trans_le
    (positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds
      hHorizon a (by norm_num))

/-- Terminal risk localizes scaled inverse risk simultaneously over the full
study horizon. This supplies the denominator control in roadmap (23)--(24). -/
-- @node: positiveRetention_uniform_scaledInvRisk_probability_tendsto_zero
lemma positiveRetention_uniform_scaledInvRisk_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ∃ t ≤ (1 : ℝ),
        (c.pMin * Real.exp (-c.dMax) * c.Ghor / 2)⁻¹ <
          (n : ℝ) * invRisk a s t}) atTop (nhds 0) := by
  obtain ⟨hq, hlim⟩ := positiveRetention_terminalRisk_localization c P hRandom
    hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  rintro s ⟨t, ht, herr⟩
  by_contra hbad
  let q := c.pMin * Real.exp (-c.dMax) * c.Ghor / 2
  have hmono : riskSet a s 1 ≤ riskSet a s t := by
    classical
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, ht.trans hi.2⟩
  have hq0 : q ≠ 0 := hq.ne'
  have hr : (n : ℝ) * q ≤ riskSet a s t :=
    (le_of_not_gt hbad).trans (by exact_mod_cast hmono)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrR : (0 : ℝ) < riskSet a s t := (mul_pos hnR hq).trans_le hr
  have hrN : riskSet a s t ≠ 0 := by exact_mod_cast hrR.ne'
  have hb : (n : ℝ) * invRisk a s t ≤ q⁻¹ := by
    simp only [invRisk, hrN, if_false, ← div_eq_mul_inv]
    apply (div_le_iff₀ hrR).2
    calc
      (n : ℝ) = q⁻¹ * ((n : ℝ) * q) := by field_simp [hq0]
      _ ≤ q⁻¹ * (riskSet a s t : ℝ) :=
        mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hq.le)
  exact (not_lt_of_ge hb) herr

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
