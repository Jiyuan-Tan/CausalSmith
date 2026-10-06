module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleIntegratedEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMTimeConsistency

/-!
# Centered inverse-risk energy under positive horizon retention

Roadmap (23)--(27): the binomial centered coefficient estimate holds through
time one, without endpoint smoothness. It supplies the denominator part of
observable martingale oracle replacement.
-/

public section

open MeasureTheory Set Filter
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The centered inverse-risk coefficient bound holds directly for the
observed at-risk count. -/
-- @node: positiveRetention_integral_riskFraction_scaledInvRisk_center_sq_le
lemma positiveRetention_integral_riskFraction_scaledInvRisk_center_sq_le
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        (((n : ℝ) * invRisk a s t) -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2
      ∂sampleLaw P n) ≤
      5 / (((n + 1 : ℕ) : ℝ) *
        (P.p a * survival P a t * retention P a t) ^ 2) := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  let q : ℝ := P.p a * survival P a t * retention P a t
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  have hq : 0 < q :=
    (mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos).trans_le
      (positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds hHorizon a ht)
  have hmass : (observedLaw P).real A = q := by
    simpa [A, q] using positiveRetention_observed_arm_risk_probability
      P hRandom hAssignment hDeath hCensor a ht
  let F : ℕ → ℝ := fun k ↦ ((k : ℝ) / n) *
    ((if 0 < k then (n : ℝ) / k else 0) - 1 / q) ^ 2
  have hpath (s : Fin n → ObsHistory) :
      ((riskSet a s t : ℝ) / n) *
          (((n : ℝ) * invRisk a s t) - 1 / q) ^ 2 =
        F (Finset.univ.filter fun i ↦ s i ∈ A).card := by
    unfold invRisk riskSet
    dsimp [F, A]
    by_cases hz : (Finset.univ.filter fun i : Fin n ↦
        (s i).treatment = a ∧ t ≤ (s i).exit).card = 0
    · simp [hz]
    · simp [hz, Nat.pos_of_ne_zero hz, div_eq_mul_inv]
  simp_rw [show P.p a * survival P a t * retention P a t = q by rfl, hpath]
  have heq := integral_eventCount_eq_binomial (observedLaw P) A hA n F
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n ((observedLaw P).real A) k * F k := by
      change (∫ z : Fin n → ObsHistory,
        F (Finset.univ.filter fun i ↦ z i ∈ A).card
        ∂Measure.pi fun _ : Fin n ↦ observedLaw P) = _
      simpa only [A] using heq
    _ = ∑ k ∈ Finset.range (n + 1), binomialWeight n q k * F k := by
      rw [hmass]
    _ ≤ 5 / (((n + 1 : ℕ) : ℝ) * q ^ 2) := by
      dsimp [F]
      simpa [mul_assoc] using
        (binomial_weighted_scaledInverse_center_sq_le n q hn hq
          (by rw [← hmass]; exact measureReal_le_one))


/-- The centered denominator energy has a common bound over the full horizon. -/
-- @node: positiveRetention_centeredInvRisk_energy_le_uniformRate
lemma positiveRetention_centeredInvRisk_energy_le_uniformRate
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2 ∂sampleLaw P n) ≤
      5 / (((n + 1 : ℕ) : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2) := by
  apply (positiveRetention_integral_riskFraction_scaledInvRisk_center_sq_le
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a hn ht).trans
  have hq0 : 0 < c.pMin * Real.exp (-c.dMax) * c.Ghor :=
    mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by positivity) (sq_pos_of_pos hq0))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ hq0.le
    (positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds hHorizon a ht) 2

/-- Centered inverse-risk energy vanishes at every time, including time one. -/
-- @node: positiveRetention_centeredInvRisk_energy_tendsto_zero
lemma positiveRetention_centeredInvRisk_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2 ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    integral_nonneg (fun s => by positivity)))
    (by filter_upwards [eventually_ge_atTop 1] with n hn
        exact positiveRetention_centeredInvRisk_energy_le_uniformRate
          c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
          (by omega) ht)
  have hi := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
  convert hi.const_mul (5 / (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2)
    using 1 <;> try simp only [mul_zero]
  funext n
  simp only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The centered denominator energy is jointly integrable in sample and time. -/
-- @node: positiveRetention_centeredInvRisk_energy_integrable_prod
lemma positiveRetention_centeredInvRisk_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      ((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * invRisk a p.1 p.2 -
          1 / (P.p a * survival P a p.2 * retention P a p.2)) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let q0 := c.pMin * Real.exp (-c.dMax) * c.Ghor
  have hq0 : 0 < q0 := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (positiveRetention_survival_continuousOn P hDeath a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  let f := fun p : (Fin n → ObsHistory) × ℝ =>
    ((riskSet a p.1 p.2 : ℝ) / n) *
      ((n : ℝ) * invRisk a p.1 p.2 - 1 / (P.p a * g p.2 * retention P a p.2)) ^ 2
  have hm : Measurable f := by
    have hr : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    have hgp : Measurable (fun p : (Fin n → ObsHistory) × ℝ => g p.2) :=
      hg.comp measurable_snd
    dsimp [f]
    fun_prop
  have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1)), p.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  have heq : f =ᵐ[(sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))]
      (fun p => ((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * invRisk a p.1 p.2 -
          1 / (P.p a * survival P a p.2 * retention P a p.2)) ^ 2) := by
    filter_upwards [htprod] with p hp
    simp [f, g, hp]
  apply Integrable.congr _ heq
  apply Integrable.of_bound hm.aestronglyMeasurable (((n : ℝ) + 1 / q0) ^ 2)
  filter_upwards [htprod] with p hp
  have hq := positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds hHorizon a hp
  have hqpos : 0 < P.p a * survival P a p.2 * retention P a p.2 := hq0.trans_le hq
  have hb : 1 / (P.p a * survival P a p.2 * retention P a p.2) ≤ 1 / q0 :=
    one_div_le_one_div_of_le hq0 hq
  have hx := scaledInvRisk_mem_Icc a p.1 p.2
  have hw : (riskSet a p.1 p.2 : ℝ) / n ≤ 1 := by
    by_cases hn : n = 0
    · simp [hn]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).2
      exact_mod_cast (show riskSet a p.1 p.2 ≤ n from
        (Finset.card_filter_le _ _).trans (by simp))
  have he : |(n : ℝ) * invRisk a p.1 p.2 -
      1 / (P.p a * survival P a p.2 * retention P a p.2)| ≤ (n : ℝ) + 1 / q0 := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hx.1, abs_of_nonneg (one_div_nonneg.mpr hqpos.le)]
    exact add_le_add hx.2 hb
  simp only [f, g, Set.piecewise, if_pos hp, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
  have hsq : ((n : ℝ) * invRisk a p.1 p.2 -
      1 / (P.p a * survival P a p.2 * retention P a p.2)) ^ 2 ≤
      ((n : ℝ) + 1 / q0) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 he
  exact (mul_le_of_le_one_left (sq_nonneg _) hw).trans hsq

/-- Fubini transfers the binomial bound to full-horizon expected centered energy. -/
-- @node: positiveRetention_centeredInvRisk_integrated_energy_le_uniformRate
lemma positiveRetention_centeredInvRisk_integrated_energy_le_uniformRate
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2) ∂sampleLaw P n) ≤
      5 / (((n + 1 : ℕ) : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := positiveRetention_centeredInvRisk_energy_integrable_prod
    c P hOverlap hDeath hDeathBounds hHorizon a n
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _t in Icc (0 : ℝ) 1,
        5 / (((n + 1 : ℕ) : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2) := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact positiveRetention_centeredInvRisk_energy_le_uniformRate
        c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a hn ht
    _ = _ := by simp [Real.volume_Icc]

/-- Full-horizon centered inverse-risk energy tends to zero in mean. -/
-- @node: positiveRetention_centeredInvRisk_integrated_energy_tendsto_zero
lemma positiveRetention_centeredInvRisk_integrated_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2) ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    integral_nonneg (fun s => integral_nonneg (fun t => by positivity))))
    (by filter_upwards [eventually_ge_atTop 1] with n hn
        exact positiveRetention_centeredInvRisk_integrated_energy_le_uniformRate
          c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a (by omega))
  have hi := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
  convert hi.const_mul (5 / (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2)
    using 1 <;> try simp only [mul_zero]
  funext n
  simp only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Markov's inequality gives vanishing centered denominator energy in probability. -/
-- @node: positiveRetention_centeredInvRisk_integrated_energy_probability_tendsto_zero
lemma positiveRetention_centeredInvRisk_integrated_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hlim := (positiveRetention_centeredInvRisk_integrated_energy_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).div_const ε
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [zero_div] using hlim)
  intro n
  have hi := (positiveRetention_centeredInvRisk_energy_integrable_prod
    c P hOverlap hDeath hDeathBounds hHorizon a n).integral_prod_left
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory =>
      integral_nonneg (fun t => by positivity))) hi ε
  apply (le_div_iff₀ hε).2
  have hsub : {s : Fin n → ObsHistory | ε < ∫ t in Icc (0 : ℝ) 1,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2} ⊆ {s | ε ≤ ∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2} :=
    fun s hs => (show ε < _ from hs).le
  exact (mul_le_mul_of_nonneg_right (measureReal_mono hsub (by finiteness))
    hε.le).trans (by simpa only [mul_comm] using hm)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
