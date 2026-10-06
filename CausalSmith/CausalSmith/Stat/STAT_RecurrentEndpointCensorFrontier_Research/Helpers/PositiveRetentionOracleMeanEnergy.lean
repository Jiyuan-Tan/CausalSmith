module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleCoefficient

/-!
# Full-horizon oracle energy in mean

Roadmap (23)--(26) of the positive-retention benchmark: second reciprocal
binomial moments and Young's inequality control the dependent KM coefficient
in mean. No independence between the KM and inverse-risk errors is used.
-/

public section

open MeasureTheory Set Filter
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The scaled inverse-risk second moment includes the study endpoint under
positive horizon retention and needs no endpoint smoothness assumptions. -/
-- @node: positiveRetention_integral_scaledInvRisk_sq_le
lemma positiveRetention_integral_scaledInvRisk_sq_le
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ}
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory, ((n : ℝ) * invRisk a s t) ^ 2
      ∂sampleLaw P n) ≤
      6 / (P.p a * survival P a t * retention P a t) ^ 2 := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  let q : ℝ := P.p a * survival P a t * retention P a t
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos (mul_pos (c.pMin_pos.trans_le (hOverlap a))
      (Real.exp_pos _)) (c.Ghor_pos.trans_le (hHorizon a t ht))
  have hmass : (observedLaw P).real A = q := by
    simpa [A, q] using positiveRetention_observed_arm_risk_probability P hRandom hAssignment hDeath hCensor a ht
  let F : ℕ → ℝ := fun k ↦ (if 0 < k then (n : ℝ) / k else 0) ^ 2
  have hpath (s : Fin n → ObsHistory) :
      ((n : ℝ) * invRisk a s t) ^ 2 =
        F (Finset.univ.filter fun i ↦ s i ∈ A).card := by
    unfold invRisk riskSet
    dsimp [F, A]
    by_cases hz : (Finset.univ.filter fun i : Fin n ↦
        (s i).treatment = a ∧ t ≤ (s i).exit).card = 0
    · simp [hz]
    · simp [hz, Nat.pos_of_ne_zero hz, div_eq_mul_inv]
  simp_rw [hpath]
  have heq := integral_eventCount_eq_binomial (observedLaw P) A hA n F
  have hs := binomial_totalized_inverse_count_sq_le n q hq (by
    rw [← hmass]
    exact measureReal_le_one)
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n ((observedLaw P).real A) k * F k := by
      change (∫ z : Fin n → ObsHistory,
        F (Finset.univ.filter fun i ↦ z i ∈ A).card
        ∂Measure.pi fun _ : Fin n ↦ observedLaw P) = _
      simpa only [A] using heq
    _ = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n q k * (if 0 < k then (k : ℝ)⁻¹ ^ 2 else 0) *
          (n : ℝ) ^ 2 := by
      rw [hmass]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : 0 < k <;> simp [F, hk0]
      field_simp
    _ ≤ (6 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * q ^ 2)) *
        (n : ℝ) ^ 2 := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ ≤ 6 / q ^ 2 := by
      have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
      have hnle : (n : ℝ) ^ 2 ≤
          ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      have hden : 0 < ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by positivity
      calc
        _ = ((n : ℝ) ^ 2 /
            (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) *
              (6 / q ^ 2) := by field_simp
        _ ≤ 1 * (6 / q ^ 2) := mul_le_mul_of_nonneg_right
          ((div_le_one hden).2 hnle) (div_nonneg (by norm_num) hq2.le)
        _ = _ := one_mul _
    _ = _ := rfl


/-- The scaled inverse-risk square is integrable jointly in sample and time. -/
-- @node: positiveRetention_scaledInvRisk_sq_integrable_prod
lemma positiveRetention_scaledInvRisk_sq_integrable_prod
    (P : SubjectLaw) (a : Arm) (n : ℕ) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      ((n : ℝ) * invRisk a p.1 p.2) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply Integrable.of_bound (by fun_prop) ((n : ℝ) ^ 2)
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (scaledInvRisk_mem_Icc a p.1 p.2).1
    (scaledInvRisk_mem_Icc a p.1 p.2).2 2

/-- Fubini and the binomial second moment give a sample-size independent
bound for the integrated scaled inverse-risk square. -/
-- @node: positiveRetention_integrated_scaledInvRisk_sq_le
lemma positiveRetention_integrated_scaledInvRisk_sq_le
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ) :
    (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      ((n : ℝ) * invRisk a s t) ^ 2) ∂sampleLaw P n) ≤
      6 / (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2 := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let q0 := c.pMin * Real.exp (-c.dMax) * c.Ghor
  have hq0 : 0 < q0 := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  have hi := positiveRetention_scaledInvRisk_sq_integrable_prod P a n
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _t in Icc (0 : ℝ) 1, (6 / q0 ^ 2) := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hq := positiveRetention_arm_risk_probability_lower c P hOverlap
        hDeathBounds hHorizon a ht
      apply (positiveRetention_integral_scaledInvRisk_sq_le c P hRandom
        hAssignment hOverlap hDeath hCensor hHorizon a ht).trans
      exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hq0)
        (pow_le_pow_left₀ hq0.le hq 2)
    _ = _ := by simp [q0, Measure.real, Real.volume_Icc]

/-- The dependent KM/inverse-risk product is jointly integrable. -/
-- @node: positiveRetention_scaledInvRisk_KM_error_integrable_prod
lemma positiveRetention_scaledInvRisk_KM_error_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) (n : ℕ) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      ((n : ℝ) * invRisk a p.1 p.2) *
        (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  apply (positiveRetention_deathKMLeft_error_sq_integrable_prod
    c P hDeath hDeathBounds a n).bdd_mul (by fun_prop)
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (scaledInvRisk_mem_Icc a p.1 p.2).1] using
    (scaledInvRisk_mem_Icc a p.1 p.2).2

/-- Young's inequality bounds the expected dependent KM coefficient energy
by a uniformly bounded reciprocal second moment and the KM second mean. -/
-- @node: positiveRetention_integrated_scaledInvRisk_KM_error_le_young
lemma positiveRetention_integrated_scaledInvRisk_KM_error_le_young
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2) ∂sampleLaw P n) ≤
      δ * (6 / (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2) +
        (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
          (deathKMLeft a s t - survival P a t) ^ 2) ∂sampleLaw P n) / δ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let Q := (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))
  have hX := positiveRetention_scaledInvRisk_sq_integrable_prod P a n
  have hE := positiveRetention_deathKMLeft_error_sq_integrable_prod c P hDeath hDeathBounds a n
  have hW := positiveRetention_scaledInvRisk_KM_error_integrable_prod c P hDeath hDeathBounds a n
  rw [← integral_prod _ hW]
  calc
    _ ≤ ∫ p, δ * ((n : ℝ) * invRisk a p.1 p.2) ^ 2 +
        (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2 / δ ∂Q := by
      apply integral_mono_ae hW ((hX.const_mul δ).add (hE.div_const δ))
      have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂Q,
          p.2 ∈ Icc (0 : ℝ) 1 :=
        (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
          (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
      filter_upwards [htprod] with p hp
      have hk := deathKMLeft_mem_Icc a p.1 p.2
      have hs := survival_bounds_of_deathBounds c P hDeathBounds a hp
      have he : (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2 ≤ 1 := by
        nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
      simpa only [Pi.add_apply, mul_comm] using km_error_weight_young
        (X := (n : ℝ) * invRisk a p.1 p.2) he hδ
    _ = δ * (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
        ((n : ℝ) * invRisk a s t) ^ 2) ∂sampleLaw P n) +
        (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
          (deathKMLeft a s t - survival P a t) ^ 2) ∂sampleLaw P n) / δ := by
      rw [integral_add (hX.const_mul δ) (hE.div_const δ),
        integral_const_mul, integral_div, integral_prod _ hX, integral_prod _ hE]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (positiveRetention_integrated_scaledInvRisk_sq_le c P hRandom hAssignment
        hOverlap hDeath hCensor hDeathBounds hHorizon a n) hδ.le) le_rfl

/-- The dependent KM coefficient vanishes in mean on the entire closed horizon. -/
-- @node: positiveRetention_integrated_scaledInvRisk_KM_error_tendsto_zero
lemma positiveRetention_integrated_scaledInvRisk_KM_error_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2) ∂sampleLaw P n)
      atTop (nhds 0) := by
  let B := 6 / (c.pMin * Real.exp (-c.dMax) * c.Ghor) ^ 2
  have hB : 0 < B := by
    dsimp [B]
    exact div_pos (by norm_num) (sq_pos_of_pos
      (mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos))
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / (4 * B)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hlim := positiveRetention_deathKMLeft_integrated_error_secondMoment_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε * δ / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have he := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (integral_nonneg (fun s => integral_nonneg (fun t => sq_nonneg _)))] at he
  have hb := positiveRetention_integrated_scaledInvRisk_KM_error_le_young c P
    hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a n hδ
  have hδB : δ * B = ε / 4 := by dsimp [δ]; field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (integral_nonneg (fun s => integral_nonneg (fun t =>
      mul_nonneg (scaledInvRisk_mem_Icc a s t).1 (sq_nonneg _))))]
  change _ ≤ δ * B + _ at hb
  have hsmall' : (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      (deathKMLeft a s t - survival P a t) ^ 2) ∂sampleLaw P n) / δ < ε / 2 := by
    apply (div_lt_iff₀ hδ).2
    nlinarith [he]
  linarith

/-- The full oracle coefficient energy is jointly integrable, with its KM
and centered denominator contributions treated on the same sample. -/
-- @node: positiveRetention_oracleCoefficient_energy_integrable_prod
lemma positiveRetention_oracleCoefficient_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      ((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2 -
          1 / (P.p a * retention P a p.2)) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := positiveRetention_scaledInvRisk_KM_error_integrable_prod c P hDeath hDeathBounds a n
  have hj := positiveRetention_centeredInvRisk_energy_integrable_prod c P hOverlap
    hDeath hDeathBounds hHorizon a n
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      ((riskSet a p.1 p.2 : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2 -
          1 / (P.p a * retention P a p.2)) ^ 2) := by
    have hr := measurable_retention P a
    fun_prop
  apply ((hi.const_mul 2).add (hj.const_mul 2)).mono' hm.aestronglyMeasurable
  have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1)),
      p.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  filter_upwards [htprod] with p hp
  rw [Real.norm_of_nonneg (by positivity)]
  exact positiveRetention_oracleCoefficient_energy_split c P hDeathBounds a hn p.1 hp

/-- The complete full-horizon oracle coefficient energy tends to zero in
mean, supplying the expectation input to the conditional Poisson isometry. -/
-- @node: positiveRetention_oracleCoefficient_integrated_energy_tendsto_zero
lemma positiveRetention_oracleCoefficient_integrated_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2) ∂sampleLaw P n)
      atTop (nhds 0) := by
  have hlim := ((positiveRetention_integrated_scaledInvRisk_KM_error_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).const_mul 2).add
    ((positiveRetention_centeredInvRisk_integrated_energy_tendsto_zero
      c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).const_mul 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ =>
    integral_nonneg (fun s => integral_nonneg (fun t => by positivity)))) _
    (by simpa only [mul_zero, add_zero] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := (positiveRetention_scaledInvRisk_KM_error_integrable_prod
    c P hDeath hDeathBounds a n).integral_prod_left
  have hj := (positiveRetention_centeredInvRisk_energy_integrable_prod
    c P hOverlap hDeath hDeathBounds hHorizon a n).integral_prod_left
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.const_mul 2) (hj.const_mul 2)]
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun s => integral_nonneg (fun t => by positivity)))
    ((hi.const_mul 2).add (hj.const_mul 2))
  exact Eventually.of_forall (fun s => positiveRetention_oracleCoefficient_integrated_energy_le
    c P hOverlap hDeath hDeathBounds hHorizon a (by omega) s)

/-- A bounded nonnegative hazard multiplier preserves convergence in mean
of the full oracle coefficient energy. -/
-- @node: positiveRetention_weightedOracleCoefficient_energy_tendsto_zero
lemma positiveRetention_weightedOracleCoefficient_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (f : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ B) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun s =>
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_nonneg (hf t ht).1 (by positivity))))) _
    (by simpa only [mul_zero] using
      (positiveRetention_oracleCoefficient_integrated_energy_tendsto_zero c P
        hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a).const_mul B)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := (positiveRetention_oracleCoefficient_energy_integrable_prod
    c P hOverlap hDeath hDeathBounds hHorizon a (by omega : 0 < n)).integral_prod_left
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hi.const_mul B) ?_
  · filter_upwards [] with s
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (hf t ht).1 (by positivity)
  · filter_upwards [] with s
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_
      ((positiveRetention_oracleCoefficient_energy_integrable_time
        c P hOverlap hDeath hDeathBounds hHorizon a (by omega) s).const_mul B) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_nonneg (hf t ht).1 (by positivity)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_le_mul_of_nonneg_right (hf t ht).2 (by positivity)

/-- The recurrence replacement's intensity-weighted energy vanishes in mean. -/
-- @node: positiveRetention_recurrenceOracleCoefficient_energy_tendsto_zero
lemma positiveRetention_recurrenceOracleCoefficient_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1, P.lam a t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply positiveRetention_weightedOracleCoefficient_energy_tendsto_zero c P
    hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a (P.lam a)
    (c.lambdaMin_pos.trans c.lambdaMin_lt).le
  intro t ht
  exact ⟨c.lambdaMin_pos.le.trans (hRecurBounds a t ht).1, (hRecurBounds a t ht).2⟩

/-- The death replacement's bounded remaining-target hazard energy also
vanishes in mean, without a separate denominator or smoothness premise. -/
-- @node: positiveRetention_deathOracleCoefficient_energy_tendsto_zero
lemma positiveRetention_deathOracleCoefficient_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1,
        (deathTargetWeight c P a 0 t ^ 2 * P.hazard a t) *
          (((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
              1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n)
      atTop (nhds 0) := by
  have hL : 0 < c.lambdaMax * Real.exp c.dMax :=
    mul_pos (c.lambdaMin_pos.trans c.lambdaMin_lt) (Real.exp_pos _)
  apply positiveRetention_weightedOracleCoefficient_energy_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
    (fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t)
    (mul_pos (sq_pos_of_pos hL) (c.dMin_pos.trans c.dMin_lt)).le
  intro t ht
  have hh := hDeathBounds a t ht
  have hw := positiveRetention_deathTargetWeight_zero_abs_le c P hRecurBounds
    hDeathBounds a t
  have hw2 : deathTargetWeight c P a 0 t ^ 2 ≤
      (c.lambdaMax * Real.exp c.dMax) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL.le).2 hw
  exact ⟨mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans hh.1),
    mul_le_mul hw2 hh.2 (c.dMin_pos.le.trans hh.1) (sq_nonneg _)⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
