module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionCenteredEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathRegularity

/-!
# Full-horizon observable oracle coefficient energy

Roadmap (23)--(27) of the positive-retention benchmark: combine the dependent
Kaplan--Meier error with the centered inverse-risk error before integrating.
The complete recurrence oracle coefficient has vanishing quadratic energy
in probability, with no endpoint smoothness assumptions.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The dependent KM part of the coefficient energy is integrable in time. -/
-- @node: positiveRetention_deathKMLeft_scaledInvRisk_error_integrable_time
lemma positiveRetention_deathKMLeft_scaledInvRisk_error_integrable_time
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) :
    IntegrableOn (fun t => ((n : ℝ) * invRisk a s t) *
      (deathKMLeft a s t - survival P a t) ^ 2) (Icc (0 : ℝ) 1) := by
  apply (positiveRetention_deathKMLeft_error_sq_integrable_time
    c P hDeath hDeathBounds a s).bdd_mul (by fun_prop)
  · filter_upwards [] with t
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (scaledInvRisk_mem_Icc a s t).1] using
      (scaledInvRisk_mem_Icc a s t).2

/-- The centered denominator energy is integrable in time for every observed sample. -/
-- @node: positiveRetention_centeredInvRisk_energy_integrable_time
lemma positiveRetention_centeredInvRisk_energy_integrable_time
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) :
    Integrable (fun t : ℝ =>
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  let q0 := c.pMin * Real.exp (-c.dMax) * c.Ghor
  have hq0 : 0 < q0 := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g :=
    (positiveRetention_survival_continuousOn P hDeath a).measurable_piecewise
      continuousOn_const measurableSet_Icc
  let f := fun t : ℝ =>
    ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * invRisk a s t - 1 / (P.p a * g t * retention P a t)) ^ 2
  have hm : Measurable f := by
    have hr := measurable_retention P a
    dsimp [f]
    fun_prop
  have heq : f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun t => ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [f, g, ht]
  apply Integrable.congr _ heq
  apply Integrable.of_bound hm.aestronglyMeasurable (((n : ℝ) + 1 / q0) ^ 2)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t hp
  have hq := positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds hHorizon a hp
  have hqpos : 0 < P.p a * survival P a t * retention P a t := hq0.trans_le hq
  have hb : 1 / (P.p a * survival P a t * retention P a t) ≤ 1 / q0 :=
    one_div_le_one_div_of_le hq0 hq
  have hx := scaledInvRisk_mem_Icc a s t
  have hw : (riskSet a s t : ℝ) / n ≤ 1 := by
    by_cases hn : n = 0
    · simp [hn]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).2
      exact_mod_cast (show riskSet a s t ≤ n from
        (Finset.card_filter_le _ _).trans (by simp))
  have he : |(n : ℝ) * invRisk a s t -
      1 / (P.p a * survival P a t * retention P a t)| ≤ (n : ℝ) + 1 / q0 := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hx.1, abs_of_nonneg (one_div_nonneg.mpr hqpos.le)]
    exact add_le_add hx.2 hb
  simp only [f, g, Set.piecewise, if_pos hp, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
  have hsq : ((n : ℝ) * invRisk a s t -
      1 / (P.p a * survival P a t * retention P a t)) ^ 2 ≤
      ((n : ℝ) + 1 / q0) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 he
  exact (mul_le_of_le_one_left (sq_nonneg _) hw).trans hsq


/-- The pathwise oracle energy split applies at time one and needs only
benchmark hazard bounds to remove the survival multiplier. -/
-- @node: positiveRetention_oracleCoefficient_energy_split
lemma positiveRetention_oracleCoefficient_energy_split
    (c : ClassConstants) (P : SubjectLaw) (hDeathBounds : DeathBounds c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2 ≤
      2 * (((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2) +
      2 * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2) := by
  have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
  have hs0 : 0 ≤ survival P a t := (Real.exp_pos _).le
  have hs2 : survival P a t ^ 2 ≤ 1 := by nlinarith [hs.2]
  apply (observed_KM_oracle_coefficient_energy_split P a hn s t).trans
  have hw : 0 ≤ ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t)) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hs2 hw]

/-- The complete recurrence coefficient energy is controlled by the two
already established dependent-error energies, throughout the closed horizon. -/
-- @node: positiveRetention_oracleCoefficient_integrated_energy_le
lemma positiveRetention_oracleCoefficient_integrated_energy_le
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ}
    (hn : 0 < n) (s : Fin n → ObsHistory) :
    (∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2) ≤
      2 * (∫ t in Icc (0 : ℝ) 1, ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2) +
      2 * (∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2) := by
  have hi := positiveRetention_deathKMLeft_scaledInvRisk_error_integrable_time
    c P hDeath hDeathBounds a s
  have hj := positiveRetention_centeredInvRisk_energy_integrable_time
    c P hOverlap hDeath hDeathBounds hHorizon a s
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.const_mul 2) (hj.const_mul 2)]
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun t => by positivity))
    ((hi.const_mul 2).add (hj.const_mul 2))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact positiveRetention_oracleCoefficient_energy_split c P hDeathBounds a hn s ht

/-- The full coefficient energy is integrable at every finite sample size. -/
-- @node: positiveRetention_oracleCoefficient_energy_integrable_time
lemma positiveRetention_oracleCoefficient_energy_integrable_time
    (c : ClassConstants) (P : SubjectLaw) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ}
    (hn : 0 < n) (s : Fin n → ObsHistory) :
    IntegrableOn (fun t => ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2) (Icc (0 : ℝ) 1) := by
  have hi := positiveRetention_deathKMLeft_scaledInvRisk_error_integrable_time
    c P hDeath hDeathBounds a s
  have hj := positiveRetention_centeredInvRisk_energy_integrable_time
    c P hOverlap hDeath hDeathBounds hHorizon a s
  have hm : Measurable (fun t => ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2) := by
    have hr := measurable_retention P a
    fun_prop
  apply ((hi.const_mul 2).add (hj.const_mul 2)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact positiveRetention_oracleCoefficient_energy_split c P hDeathBounds a hn s ht

/-- The full observable recurrence coefficient has vanishing quadratic
energy in probability, without treating the KM and denominator errors as
independent. This is the energy input for the oracle replacement in (26). -/
-- @node: positiveRetention_oracleCoefficient_integrated_energy_probability_tendsto_zero
lemma positiveRetention_oracleCoefficient_integrated_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hlim := (positiveRetention_deathKMLeft_scaledInvRisk_error_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
    (by linarith : 0 < ε / 4)).add
    (positiveRetention_centeredInvRisk_integrated_energy_probability_tendsto_zero
      c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
      (by linarith : 0 < ε / 4))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  let A : Set (Fin n → ObsHistory) := {s | ε / 4 <
    ∫ t in Icc (0 : ℝ) 1, ((n : ℝ) * invRisk a s t) *
      (deathKMLeft a s t - survival P a t) ^ 2}
  let B : Set (Fin n → ObsHistory) := {s | ε / 4 <
    ∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t)) ^ 2}
  apply (measureReal_mono (s₂ := A ∪ B) ?_ (by finiteness)).trans
    (measureReal_union_le A B)
  intro s hs
  by_cases ha : s ∈ A
  · exact Or.inl ha
  · right
    by_contra hb
    change ¬ ε / 4 < _ at ha hb
    have ha' := le_of_not_gt ha
    have hb' := le_of_not_gt hb
    have he := positiveRetention_oracleCoefficient_integrated_energy_le
      c P hOverlap hDeath hDeathBounds hHorizon a (by omega) s
    change ε < _ at hs
    change _ ≤ ε / 4 at ha' hb'
    linarith

/-- A bounded nonnegative intensity multiplier preserves the vanishing
oracle energy. The bound is on a deterministic multiplier, not on the error. -/
-- @node: positiveRetention_weightedOracleCoefficient_energy_probability_tendsto_zero
lemma positiveRetention_weightedOracleCoefficient_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (f : ℝ → ℝ) {B : ℝ} (hB : 0 < B)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (positiveRetention_oracleCoefficient_integrated_energy_probability_tendsto_zero
      c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
      (div_pos hε hB))
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  intro s hs
  have hi := positiveRetention_oracleCoefficient_energy_integrable_time
    c P hOverlap hDeath hDeathBounds hHorizon a (by omega) s
  have he : (∫ t in Icc (0 : ℝ) 1, f t * (((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2)) ≤
      B * (∫ t in Icc (0 : ℝ) 1, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg _ (hi.const_mul B) _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_nonneg (hf t ht).1 (by positivity)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_le_mul_of_nonneg_right (hf t ht).2 (by positivity)
  change ε / B < _
  exact (div_lt_iff₀ hB).2 (by simpa only [mul_comm] using hs.trans_le he)

/-- The recurrence replacement's actual intensity-weighted energy vanishes. -/
-- @node: positiveRetention_recurrenceOracleCoefficient_energy_probability_tendsto_zero
lemma positiveRetention_recurrenceOracleCoefficient_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1, P.lam a t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)}) atTop (nhds 0) := by
  apply positiveRetention_weightedOracleCoefficient_energy_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
    (P.lam a) (c.lambdaMin_pos.trans c.lambdaMin_lt) _ hε
  intro t ht
  exact ⟨c.lambdaMin_pos.le.trans (hRecurBounds a t ht).1, (hRecurBounds a t ht).2⟩

/-- The death replacement has the same coefficient difference multiplied
by the bounded remaining-target weight. Its actual hazard energy vanishes. -/
-- @node: positiveRetention_deathOracleCoefficient_energy_probability_tendsto_zero
lemma positiveRetention_deathOracleCoefficient_energy_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < ∫ t in Icc (0 : ℝ) 1,
        (deathTargetWeight c P a 0 t ^ 2 * P.hazard a t) *
          (((riskSet a s t : ℝ) / n) *
            ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
              1 / (P.p a * retention P a t)) ^ 2)}) atTop (nhds 0) := by
  have hL : 0 < c.lambdaMax * Real.exp c.dMax :=
    mul_pos (c.lambdaMin_pos.trans c.lambdaMin_lt) (Real.exp_pos _)
  apply positiveRetention_weightedOracleCoefficient_energy_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a
    (fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t)
    (mul_pos (sq_pos_of_pos hL) (c.dMin_pos.trans c.dMin_lt)) _ hε
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
