module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerRateBounds
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathRegularity

/-!
# Nondegenerate benchmark variance without endpoint smoothness

Roadmap (28)--(29): positive horizon retention and the measurable hazard
bounds give integrable oracle variance densities, explicit finite upper
bounds, and a strictly positive recurrence-energy floor. These are the
variance prerequisites for the ordinary estimator's fixed-law CLT.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The inverse retention multiplier is bounded throughout the benchmark horizon. -/
-- @node: positiveRetention_inv_retention_le
lemma positiveRetention_inv_retention_le (c : ClassConstants) (P : SubjectLaw)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (retention P a t)⁻¹ ≤ c.Ghor⁻¹ := by
  exact (inv_le_inv₀ (c.Ghor_pos.trans_le (hHorizon a t ht)) c.Ghor_pos).2
    (hHorizon a t ht)

/-- Both oracle variance terms have finite horizon integrals under the benchmark
assumptions, including merely measurable recurrence and death hazards. -/
-- @node: positiveRetention_variance_density_intervalIntegrable
lemma positiveRetention_variance_density_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    IntervalIntegrable (fun t =>
      survival P a t * P.lam a t / retention P a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t)) volume 0 1 := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  have htarget : Integrable (fun t => survival P a t * P.lam a t) ν := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa [continuationWeight] using weightedTarget_intervalIntegrable c P hPoisson
      hDeath hDeathBounds a (h := 0) (by norm_num) (by norm_num) (by norm_num)
  have hinv : AEStronglyMeasurable (fun t => (retention P a t)⁻¹) ν := by
    exact (measurable_retention P a).inv.aestronglyMeasurable
  have hinvBound : ∀ᵐ t ∂ν, ‖(retention P a t)⁻¹‖ ≤ c.Ghor⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (c.Ghor_pos.le.trans (hHorizon a t ht)))]
    exact positiveRetention_inv_retention_le c P hHorizon a ht
  have hrec := htarget.bdd_mul hinv hinvBound
  have henergy : Integrable (fun t => deathTargetWeight c P a 0 t ^ 2 * P.hazard a t) ν :=
    positiveRetention_deathTargetWeight_zero_sq_hazard_integrableOn c P hPoisson
      hDeath hRecurBounds hDeathBounds a
  have hs : AEStronglyMeasurable (survival P a) ν :=
    (positiveRetention_survival_continuousOn P hDeath a).aestronglyMeasurable measurableSet_Icc
  have hsBound : ∀ᵐ t ∂ν, ‖survival P a t‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa [Real.norm_eq_abs, abs_of_pos (show 0 < survival P a t from Real.exp_pos _)]
      using (survival_bounds_of_deathBounds c P hDeathBounds a ht).2
  have hd := (henergy.bdd_mul hs hsBound).bdd_mul hinv hinvBound
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (hrec.add hd).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hs0 : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  have hg0 : retention P a t ≠ 0 := (c.Ghor_pos.trans_le (hHorizon a t ht)).ne'
  simp only [Pi.add_apply]
  rw [deathTargetWeight, if_pos (by simpa using ht)]
  field_simp

/-- The benchmark density has a deterministic integrable envelope depending only
on the hazard bands and horizon retention. -/
-- @node: positiveRetention_variance_density_le
lemma positiveRetention_variance_density_le (c : ClassConstants) (P : SubjectLaw)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    survival P a t * P.lam a t / retention P a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t) ≤
    c.lambdaMax / c.Ghor + c.lambdaMax ^ 2 * c.dMax * Real.exp c.dMax / c.Ghor := by
  have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
  have hs0 : 0 < survival P a t := Real.exp_pos _
  have hg0 : 0 < retention P a t := c.Ghor_pos.trans_le (hHorizon a t ht)
  have hgi := positiveRetention_inv_retention_le c P hHorizon a ht
  have hsi : (survival P a t)⁻¹ ≤ Real.exp c.dMax := by
    calc
      _ ≤ (Real.exp (-c.dMax))⁻¹ :=
        (inv_le_inv₀ hs0 (Real.exp_pos _)).2 hs.1
      _ = _ := by rw [Real.exp_neg]; simp
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans (hRecurBounds a t ht).1
  have hmax0 : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hd0 : 0 ≤ P.hazard a t := c.dMin_pos.le.trans (hDeathBounds a t ht).1
  have hrec : survival P a t * P.lam a t / retention P a t ≤ c.lambdaMax / c.Ghor := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul
      ((mul_le_mul_of_nonneg_right hs.2 hl0).trans (by simpa using (hRecurBounds a t ht).2))
      hgi (inv_nonneg.mpr hg0.le) hmax0
  have hrem : |remainingTarget c P a 0 t| ≤ c.lambdaMax := by
    have hr := positiveRetention_remainingTarget_zero_abs_le c P hRecurBounds hDeathBounds a ht
    nlinarith [ht.1]
  have hrem2 : remainingTarget c P a 0 t ^ 2 ≤ c.lambdaMax ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hrem 2
  have hdeath : (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
      (survival P a t * retention P a t) ≤
      c.lambdaMax ^ 2 * c.dMax * Real.exp c.dMax / c.Ghor := by
    rw [div_eq_mul_inv, mul_inv_rev, div_eq_mul_inv]
    calc
      _ = ((remainingTarget c P a 0 t) ^ 2 * P.hazard a t *
          (survival P a t)⁻¹) * (retention P a t)⁻¹ := by ring
      _ ≤ (c.lambdaMax ^ 2 * c.dMax * Real.exp c.dMax) * c.Ghor⁻¹ :=
        mul_le_mul (mul_le_mul (mul_le_mul hrem2 (hDeathBounds a t ht).2 hd0
          (sq_nonneg _)) hsi (inv_nonneg.mpr hs0.le)
          (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans c.dMin_lt.le)))
          hgi (inv_nonneg.mpr hg0.le)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans c.dMin_lt.le))
            (Real.exp_pos _).le)
  exact add_le_add hrec hdeath

/-- The arm variance integral is bounded uniformly over the benchmark class. -/
-- @node: positiveRetention_variance_arm_integral_upper
lemma positiveRetention_variance_arm_integral_upper (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    (∫ t in (0 : ℝ)..1,
      survival P a t * P.lam a t / retention P a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t)) ≤
      c.lambdaMax / c.Ghor + c.lambdaMax ^ 2 * c.dMax * Real.exp c.dMax / c.Ghor := by
  have hb := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) (positiveRetention_variance_density_intervalIntegrable c P
      hPoisson hDeath hRecurBounds hDeathBounds hHorizon a)
    intervalIntegrable_const (fun t ht =>
      positiveRetention_variance_density_le c P hRecurBounds hDeathBounds hHorizon a ht)
  simpa using hb

/-- Recurrence energy yields a positive arm floor; death energy is nonnegative. -/
-- @node: positiveRetention_variance_arm_integral_lower
lemma positiveRetention_variance_arm_integral_lower (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Real.exp (-c.dMax) * c.lambdaMin ≤
      ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
        (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) := by
  have hi := positiveRetention_variance_density_intervalIntegrable c P hPoisson
    hDeath hRecurBounds hDeathBounds hHorizon a
  have hb := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) (intervalIntegrable_const (c := Real.exp (-c.dMax) * c.lambdaMin)) hi
    (fun t ht => ?_)
  · simpa using hb
  have hs := survival_bounds_of_deathBounds c P hDeathBounds a ht
  have hr : 0 < retention P a t := c.Ghor_pos.trans_le (hHorizon a t ht)
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans (hRecurBounds a t ht).1
  have hs0 : 0 < survival P a t := Real.exp_pos _
  have hnum : Real.exp (-c.dMax) * c.lambdaMin ≤ survival P a t * P.lam a t :=
    mul_le_mul hs.1 (hRecurBounds a t ht).1 c.lambdaMin_pos.le hs0.le
  have hdiv : survival P a t * P.lam a t ≤
      survival P a t * P.lam a t / retention P a t :=
    (le_div_iff₀ hr).2 (mul_le_of_le_one_right (mul_nonneg hs0.le hl0)
      (retention_le_one P a t))
  have hd : 0 ≤ (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
      (survival P a t * retention P a t) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans (hDeathBounds a t ht).1))
      (mul_nonneg hs0.le hr.le)
  linarith

/-- The benchmark variance is strictly positive without a Holder or tail premise. -/
-- @node: positiveRetention_variance_pos
lemma positiveRetention_variance_pos (c : ClassConstants) (P : SubjectLaw)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) :
    0 < subcriticalVariance c P := by
  have hpos (a : Arm) : 0 < (P.p a)⁻¹ *
      ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
        (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) :=
    mul_pos (inv_pos.mpr (c.pMin_pos.trans_le (hOverlap a)))
      ((mul_pos (Real.exp_pos _) c.lambdaMin_pos).trans_le
        (positiveRetention_variance_arm_integral_lower c P hPoisson hDeath
          hRecurBounds hDeathBounds hHorizon a))
  unfold subcriticalVariance
  exact Finset.sum_pos (fun a _ => hpos a) Finset.univ_nonempty

/-- Summing the two arm envelopes and using treatment overlap yields a finite
class-uniform bound for the variance used in the benchmark CLT. -/
-- @node: positiveRetention_variance_upper
lemma positiveRetention_variance_upper (c : ClassConstants) (P : SubjectLaw)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) :
    subcriticalVariance c P ≤ 2 * c.pMin⁻¹ *
      (c.lambdaMax / c.Ghor + c.lambdaMax ^ 2 * c.dMax * Real.exp c.dMax / c.Ghor) := by
  let B := c.lambdaMax / c.Ghor +
    c.lambdaMax ^ 2 * c.dMax * Real.exp c.dMax / c.Ghor
  have hB : 0 ≤ B := by
    dsimp [B]
    have hl := c.lambdaMin_pos.trans c.lambdaMin_lt
    have hd := c.dMin_pos.trans c.dMin_lt
    have hg := c.Ghor_pos
    positivity
  have ha (a : Arm) : (P.p a)⁻¹ *
      (∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
        (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
          (survival P a t * retention P a t)) ≤ c.pMin⁻¹ * B := by
    have hp := c.pMin_pos.trans_le (hOverlap a)
    calc
      _ ≤ (P.p a)⁻¹ * B := mul_le_mul_of_nonneg_left
        (positiveRetention_variance_arm_integral_upper c P hPoisson hDeath
          hRecurBounds hDeathBounds hHorizon a) (inv_nonneg.mpr hp.le)
      _ ≤ c.pMin⁻¹ * B := mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ hp c.pMin_pos).2 (hOverlap a)) hB
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Arm)) (fun a _ => ha a)
  simpa [subcriticalVariance, Finset.sum_const, B, mul_assoc] using hh

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
