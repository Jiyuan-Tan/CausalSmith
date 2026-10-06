module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathIsometry
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRecurrence
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly

/-!
# Ordinary arm risk at positive horizon retention

Assemble the exact zero-bandwidth decomposition with recurrence and death
isometries, exponential extinction control, and contraction of projection.
This proves the finite-sample risk part of roadmap (12)--(14).
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The benchmark arm target belongs to the declared projection interval. -/
-- @node: positiveRetention_armMean_mem_projectionRange
lemma positiveRetention_armMean_mem_projectionRange (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (a : Arm) : armMean P a ∈ Icc (0 : ℝ) c.lambdaMax := by
  have hf : IntervalIntegrable (fun t => survival P a t * P.lam a t) volume 0 1 := by
    simpa [continuationWeight] using weightedTarget_intervalIntegrable c P hPoisson
      hDeath hDeathBounds a (h := 0) (by norm_num) (by norm_num) (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ survival P a t * P.lam a t ∧ survival P a t * P.lam a t ≤ c.lambdaMax := by
    have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
    have hb := hRecurBounds a t ht
    have hlam : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hb.1
    exact ⟨mul_nonneg (Real.exp_pos _).le hlam,
      (mul_le_mul_of_nonneg_right hs.2 hlam).trans (by simpa using hb.2)⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun t ht => (hp t ht).1)
  · have hi := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (by norm_num) hf (intervalIntegrable_const) (fun t ht => (hp t ht).2)
    simpa [armMean] using hi

/-- The ordinary raw arm estimator has a common parametric squared-risk
bound under precisely the positive-retention benchmark assumptions. -/
-- @node: positiveRetention_ordinaryMuTilde_sqRisk_le
lemma positiveRetention_ordinaryMuTilde_sqRisk_le (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → ∀ a : Arm,
      Integrable (fun s => (ordinaryMuTilde a s - armMean P a) ^ 2) (sampleLaw P n) ∧
      Causalean.Stat.sqRisk (sampleLaw P n) (ordinaryMuTilde a) (armMean P a) ≤ C / n := by
  let q := c.pMin * Real.exp (-c.dMax) * c.Ghor
  let R := 2 * c.lambdaMax / q
  let D := 2 * (c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax / q
  let B := (Real.exp c.dMax * c.lambdaMax) ^ 2
  let E := B * Real.exp (-1) / q
  have hq : 0 < q := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  have hlam : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  have hdmax : 0 < c.dMax := c.dMin_pos.trans c.dMin_lt
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hE0 : 0 ≤ E := by dsimp [E, B]; positivity
  refine ⟨3 * (R + D + E) + 1, by positivity, ?_⟩
  intro n hn a
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let Z := {s : Fin n → ObsHistory | riskSet a s 1 = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun
    ((measurable_recurrenceRiskSet_joint a).comp
      (measurable_id.prodMk measurable_const)) measurable_const
  let I := Z.indicator (fun _ => B)
  have hI : Integrable I (sampleLaw P n) := (integrable_const B).indicator hZ
  have hRI := positiveRetention_recurrenceError_zero_sq_integrable c P hPoisson
    hRecurBounds hRandom hRecurDeath hCensor a n
  have hDI := DeathCP.positiveRetention_deathError_zero_sq_integrable c P hRandom
    hPoisson hDeath hCensor hRecurBounds hDeathBounds a n
  have hrec : (∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n) ≤ R / n :=
    positiveRetention_recurrenceError_zero_secondMoment_le_inv_sampleSize c P hPoisson
      hRecurBounds hRandom hAssignment hOverlap hRecurDeath hCensor hDeath
      hDeathBounds hHorizon a hn0
  have hdeath : (∫ s : Fin n → ObsHistory, deathError c P a s 0 ^ 2 ∂sampleLaw P n) ≤ D / n :=
    DeathCP.positiveRetention_deathError_zero_secondMoment_le_inv_sampleSize c P
      hRandom hAssignment hOverlap hPoisson hDeath hCensor hRecurBounds
      hDeathBounds hHorizon a hn0
  have hiBound : (∫ s, I s ∂sampleLaw P n) ≤ E / n := by
    have he : Real.exp (-(n * q)) ≤ Real.exp (-1) / (n * q) :=
      (le_div_iff₀ (mul_pos hnR hq)).2
        (by simpa [mul_comm] using Real.mul_exp_neg_le_exp_neg_one ((n : ℝ) * q))
    calc
      _ = (sampleLaw P n).real Z * B := by rw [integral_indicator_const B hZ]; rfl
      _ ≤ Real.exp (-(n * q)) * B := mul_le_mul_of_nonneg_right
        (positiveRetention_riskSet_zero_probability_le_exp c P hRandom hAssignment
          hOverlap hDeath hCensor hDeathBounds hHorizon a n (by norm_num)) (sq_nonneg _)
      _ ≤ (Real.exp (-1) / (n * q)) * B := mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = E / n := by dsimp [E]; ring
  have hpoint : ∀ᵐ s ∂sampleLaw P n,
      (ordinaryMuTilde a s - armMean P a) ^ 2 ≤
        3 * (recurrenceError c P a s 0 ^ 2 + deathError c P a s 0 ^ 2 + I s) := by
    filter_upwards [positiveRetention_ordinaryMuTilde_error_decomposition_ae c P
      hIid hRandom hAssignment hPoisson hDeath hRecurDeath hCensor hDeathBounds a hn,
      positiveRetention_extinctionError_zero_sq_le_indicator_ae c P hDeath
        hRecurBounds hDeathBounds a n] with s hs hext
    change extinctionError c P a s 0 ^ 2 ≤ I s at hext
    rw [hs]
    nlinarith [sq_nonneg (recurrenceError c P a s 0 + deathError c P a s 0),
      sq_nonneg (recurrenceError c P a s 0 + extinctionError c P a s 0),
      sq_nonneg (deathError c P a s 0 - extinctionError c P a s 0)]
  have hrawMeas : AEStronglyMeasurable
      (fun s : Fin n → ObsHistory => (ordinaryMuTilde a s - armMean P a) ^ 2)
      (sampleLaw P n) := by
    have hm := ((measurable_recurrenceMuTildeAt c 0 a n).sub
      (measurable_const (a := armMean P a))).pow_const 2
    simpa [muTildeAt, ordinaryMuTilde, continuationWeight] using hm.aestronglyMeasurable
  have hrawInt := (((hRI.add hDI).add hI).const_mul 3).mono' hrawMeas
    (by
      filter_upwards [hpoint] with s hs
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ordinaryMuTilde a s - armMean P a)), Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] using hs)
  refine ⟨hrawInt, ?_⟩
  have hb := integral_mono_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory => sq_nonneg (ordinaryMuTilde a s - armMean P a)))
    (((hRI.add hDI).add hI).const_mul 3) hpoint
  have hlin : (∫ s : Fin n → ObsHistory,
      3 * (recurrenceError c P a s 0 ^ 2 + deathError c P a s 0 ^ 2 + I s) ∂sampleLaw P n) =
      3 * ((∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n) +
        (∫ s : Fin n → ObsHistory, deathError c P a s 0 ^ 2 ∂sampleLaw P n) +
        ∫ s, I s ∂sampleLaw P n) := by
    integral_linearity
  simp only [Pi.add_apply] at hb
  rw [hlin] at hb
  change Causalean.Stat.sqRisk (sampleLaw P n) (ordinaryMuTilde a) (armMean P a) ≤ _ at hb
  have hsum : 3 * ((∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n) +
      (∫ s : Fin n → ObsHistory, deathError c P a s 0 ^ 2 ∂sampleLaw P n) + ∫ s, I s ∂sampleLaw P n) ≤
      3 * (R + D + E) / n := by
    calc
      _ ≤ 3 * (R / n + D / n + E / n) := by linarith
      _ = _ := by ring
  exact hb.trans (hsum.trans (div_le_div_of_nonneg_right (by linarith) hnR.le))

/-- The ordinary projected arm estimator has a common parametric squared-risk
bound under precisely the positive-retention benchmark assumptions. -/
-- @node: positiveRetention_ordinaryMuHat_sqRisk_le
lemma positiveRetention_ordinaryMuHat_sqRisk_le (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → ∀ a : Arm,
      Causalean.Stat.sqRisk (sampleLaw P n) (ordinaryMuHat c a) (armMean P a) ≤ C / n := by
  obtain ⟨C, hC, hb⟩ := positiveRetention_ordinaryMuTilde_sqRisk_le c P hIid
    hRandom hAssignment hOverlap hPoisson hDeath hRecurDeath hCensor
    hRecurBounds hDeathBounds hHorizon
  refine ⟨C, hC, ?_⟩
  intro n hn a
  apply le_trans (integral_mono_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (ordinaryMuHat c a s - armMean P a)))
    (hb n hn a).1 (Eventually.of_forall (fun s => ?_))) (hb n hn a).2
  exact projectArm_sq_error_le c (ordinaryMuTilde a s) (armMean P a)
    (positiveRetention_armMean_mem_projectionRange c P hPoisson hDeath
      hRecurBounds hDeathBounds a)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
