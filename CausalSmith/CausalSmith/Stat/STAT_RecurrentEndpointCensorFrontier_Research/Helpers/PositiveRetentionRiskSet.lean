module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

/-!
# Positive-horizon risk-set bounds

Steps (1), (2), (4), and (10) of the positive-retention roadmap use only
randomization, the death law, censor independence, and horizon retention.
These estimates deliberately do not require endpoint smoothness or a power tail.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: positiveRetention_observed_arm_risk_probability
lemma positiveRetention_observed_arm_risk_probability (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P)
    (a : Arm) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (observedLaw P).real {o | o.treatment = a ∧ t ≤ o.exit} =
      P.p a * survival P a t * retention P a t := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hind : IndepFun LatentSubject.treatment
      (fun z : LatentSubject => min (z.death a) (censorHorizon z a)) P.latent := by
    have hi := hRandom.comp measurable_id
      (show Measurable (fun r : (Arm → RecurConfig) ×
        ((Arm → ℝ) × (Arm → ENNReal)) =>
          min (r.2.1 a) (censorHorizonValue (r.2.2 a))) by fun_prop)
    simpa only [Function.comp_def, id_eq, censorHorizon_eq_value] using hi
  have hm : MeasurableSet {o : ObsHistory | o.treatment = a ∧ t ≤ o.exit} :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurable_obsHistory_exit measurableSet_Ici)
  have he : observe ⁻¹' {o : ObsHistory | o.treatment = a ∧ t ≤ o.exit} =
      LatentSubject.treatment ⁻¹' ({a} : Set Arm) ∩
      (fun z : LatentSubject => min (z.death a) (censorHorizon z a)) ⁻¹' Ici t := by
    ext z
    change (z.treatment = a ∧ t ≤ min (z.death z.treatment)
      (censorHorizon z z.treatment)) ↔ _
    by_cases ha : z.treatment = a <;> simp [ha]
  rw [observedLaw, measureReal_def, Measure.map_apply measurable_observe hm, he,
    hind.measure_inter_preimage_eq_mul ({a} : Set Arm) (Ici t)
      (MeasurableSet.singleton a) measurableSet_Ici, ENNReal.toReal_mul]
  change P.latent.real {z | z.treatment = a} *
    P.latent.real {z | t ≤ min (z.death a) (censorHorizon z a)} = _
  rw [hAssignment a,
    exitTail_eq_survival_mul_retention P hDeath hCensor a t ht]
  ring

-- @node: positiveRetention_riskSet_zero_probability
lemma positiveRetention_riskSet_zero_probability (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P)
    (a : Arm) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (sampleLaw P n).real {s | riskSet a s t = 0} =
      (1 - P.p a * survival P a t * retention P a t) ^ n := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let E : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  have hm : MeasurableSet E :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurable_obsHistory_exit measurableSet_Ici)
  have he : {s : Fin n → ObsHistory | riskSet a s t = 0} =
      Set.pi Set.univ (fun _ => Eᶜ) := by
    ext s
    simp [riskSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff, E, Set.mem_pi]
  rw [he, sampleLaw, measureReal_def, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rw [← measureReal_def, probReal_compl_eq_one_sub hm]
  rw [positiveRetention_observed_arm_risk_probability P hRandom hAssignment hDeath hCensor a ht]

/-- Horizon retention gives a uniform positive one-subject risk probability. -/
-- @node: positiveRetention_arm_risk_probability_lower
lemma positiveRetention_arm_risk_probability_lower (c : ClassConstants) (P : SubjectLaw)
    (hOverlap : TreatmentOverlap c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    c.pMin * Real.exp (-c.dMax) * c.Ghor ≤
      P.p a * survival P a t * retention P a t := by
  have hs := (survival_bounds_of_deathBounds c P hDeathBounds a ht).1
  have hp := hOverlap a
  have hr := hHorizon a t ht
  exact mul_le_mul (mul_le_mul hp hs (Real.exp_pos _).le
    (c.pMin_pos.le.trans hp)) hr c.Ghor_pos.le
      (mul_nonneg (c.pMin_pos.le.trans hp) (Real.exp_pos _).le)

/-- Empty risk through the study horizon is exponentially unlikely, uniformly
under the proposition's assumptions rather than the endpoint model class. -/
-- @node: positiveRetention_riskSet_zero_probability_le_exp
lemma positiveRetention_riskSet_zero_probability_le_exp
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (sampleLaw P n).real {s | riskSet a s t = 0} ≤
      Real.exp (-(n * (c.pMin * Real.exp (-c.dMax) * c.Ghor))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hq : P.p a * survival P a t * retention P a t ≤ 1 := by
    rw [← positiveRetention_observed_arm_risk_probability P hRandom hAssignment hDeath hCensor a ht]
    exact measureReal_le_one
  rw [positiveRetention_riskSet_zero_probability P hRandom hAssignment hDeath hCensor a n ht]
  calc
    _ ≤ (Real.exp (-(P.p a * survival P a t * retention P a t))) ^ n :=
      pow_le_pow_left₀ (by linarith)
        (by linarith [Real.add_one_le_exp (-(P.p a * survival P a t * retention P a t))]) n
    _ = Real.exp (-(n * (P.p a * survival P a t * retention P a t))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hb := mul_le_mul_of_nonneg_left
        (positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds hHorizon a ht)
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith)

/-- The binomial reciprocal-count inequality controls observed inverse risk
uniformly at every time, including the terminal horizon. -/
-- @node: positiveRetention_integral_invRisk_le
lemma positiveRetention_integral_invRisk_le
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n) ≤
      2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor)) := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let R : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  have hm : MeasurableSet R :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurable_obsHistory_exit measurableSet_Ici)
  let q := c.pMin * Real.exp (-c.dMax) * c.Ghor
  have hq : 0 < q := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  have hprob : q * ((observedLaw P) Set.univ).toReal ≤ ((observedLaw P) R).toReal := by
    rw [measure_univ, ENNReal.toReal_one, mul_one]
    change q ≤ (observedLaw P).real R
    rw [positiveRetention_observed_arm_risk_probability P hRandom hAssignment hDeath hCensor a ht]
    exact positiveRetention_arm_risk_probability_lower c P hOverlap hDeathBounds hHorizon a ht
  have hraw :=
    Causalean.Stat.FiniteStratumMarkedRatioMse.integral_nested_count_sq_mul_totalized_inverse_le
      (m := n) (observedLaw P) Set.univ R MeasurableSet.univ hm
      (Set.subset_univ R) q hq hprob
  have heq (s : Fin n → ObsHistory) :
      ((Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet s Set.univ).card : ℝ) ^ 2 *
        (if 0 < (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet s R).card then
          ((Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet s R).card : ℝ)⁻¹
        else 0) = (n : ℝ) ^ 2 * invRisk a s t := by
    have hc : (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet s Set.univ).card = n := by
      simp [Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet]
    have hr : (Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet s R).card =
        riskSet a s t := by
      simp [Causalean.Stat.FiniteStratumMarkedRatioMse.sampleIndexSet, riskSet, R, and_comm]
    rw [hc, hr]
    unfold invRisk
    by_cases hz : riskSet a s t = 0
    · simp [hz]
    · simp [hz, Nat.pos_of_ne_zero hz, one_div]
  simp_rw [heq] at hraw
  rw [integral_const_mul, measure_univ, ENNReal.toReal_one, mul_one] at hraw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n) ≤ 2 / ((n : ℝ) * q)
  calc
    _ ≤ (2 * (n : ℝ) / q) / (n : ℝ) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hnR)).2 (by simpa [sampleLaw, mul_comm] using hraw)
    _ = _ := by field_simp

/-- Integrating the reciprocal-risk bound over the full study horizon retains
its C/n order without an endpoint-tail assumption. -/
-- @node: positiveRetention_integral_expected_invRisk_le
lemma positiveRetention_integral_expected_invRisk_le
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ t in Ioo (0 : ℝ) 1, ∫ s : Fin n → ObsHistory,
      invRisk a s t ∂sampleLaw P n) ≤
      2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor)) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let r := fun t => ∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n
  have hm : Measurable r :=
    (measurable_recurrenceInvRisk_joint a).stronglyMeasurable.integral_prod_left'.measurable
  have hi : Integrable r (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs]
    apply abs_integral_le_integral_abs.trans
    have his : Integrable (fun s : Fin n → ObsHistory => |invRisk a s t|) (sampleLaw P n) := by
      apply Integrable.of_bound
        ((measurable_recurrenceInvRisk_joint a).comp
          (measurable_id.prodMk measurable_const)).abs.aestronglyMeasurable 1
      filter_upwards [] with s
      simpa [Real.norm_eq_abs, abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1] using
        (recurrence_invRisk_mem_Icc a s t).2
    simpa using integral_mono his (integrable_const 1) (fun s => by
      rw [abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
      exact (recurrence_invRisk_mem_Icc a s t).2)
  calc
    _ ≤ ∫ _t in Ioo (0 : ℝ) 1,
        2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor)) := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact positiveRetention_integral_invRisk_le c P hRandom hAssignment hOverlap
        hDeath hCensor hDeathBounds hHorizon a hn ⟨ht.1.le, ht.2.le⟩
    _ = _ := by simp

/-- In particular, empty terminal risk vanishes in probability. -/
-- @node: positiveRetention_terminal_emptyRisk_probability_tendsto_zero
lemma positiveRetention_terminal_emptyRisk_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s | riskSet a s 1 = 0})
      atTop (nhds 0) := by
  have hq : 0 < c.pMin * Real.exp (-c.dMax) * c.Ghor :=
    mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  have hlim : Tendsto (fun n : ℕ =>
      Real.exp (-(n * (c.pMin * Real.exp (-c.dMax) * c.Ghor)))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hq))
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  exact positiveRetention_riskSet_zero_probability_le_exp c P hRandom hAssignment
    hOverlap hDeath hCensor hDeathBounds hHorizon a n (by norm_num)

/-- The zero-cutoff error decomposition needs no endpoint smoothness or tail
conditions, so it is available under the positive-retention proposition. -/
-- @node: positiveRetention_ordinaryMuTilde_error_decomposition_ae
lemma positiveRetention_ordinaryMuTilde_error_decomposition_ae
    (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hDeathBounds : DeathBounds c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) :
    (fun s : Fin n → ObsHistory => ordinaryMuTilde a s - armMean P a) =ᵐ[sampleLaw P n]
      (fun s => recurrenceError c P a s 0 - deathError c P a s 0 -
        extinctionError c P a s 0) := by
  have he := (exact_error_decomposition c P hIid hRandom hPoisson hDeath
    hRecurDeath hCensor hDeathBounds hAssignment).1 n hn
  filter_upwards [he] with s hs
  have h := hs a 0 (by norm_num) (div_nonneg c.x0_pos.le (by norm_num))
  simpa [ordinaryMuTilde, muTildeAt, truncatedMean, armMean, continuationWeight] using h

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
