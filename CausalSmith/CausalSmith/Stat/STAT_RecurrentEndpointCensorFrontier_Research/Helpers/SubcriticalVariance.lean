module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerRateBounds

/-! # Full-horizon subcritical variance

The endpoint tail envelope makes inverse retention integrable when kappa is
below one. This supplies full-horizon integrability and positivity of the
oracle variance without adding a score-moment assumption.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The subcritical inference scope contains exactly the model-class atoms. -/
-- @node: SubcriticalScope.modelClass
lemma SubcriticalScope.modelClass {c : ClassConstants} {P : SubjectLaw}
    (h : SubcriticalScope c P) : ModelClass c P := by
  rcases h with ⟨hi, hr, ha, ho, hp, hd, hrd, hc, hb, hdb, he, ht, hg, hint, hl, hdh⟩
  exact ⟨hi, hr, ha, ho, hp, hd, hrd, hc, hb, hdb, hl, hdh, he, ht, hg, hint⟩

/-- The inverse censoring tail is integrable through the terminal time for
subcritical endpoint decay; no inverse-weight premise is needed. -/
-- @node: inv_retention_intervalIntegrable_subcritical
lemma inv_retention_intervalIntegrable_subcritical (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm) :
    IntervalIntegrable (fun t => (retention P a t)⁻¹) volume 0 1 := by
  have hp : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-c.kappa)) volume 0 1 := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (by linarith : -1 < -c.kappa)).comp_sub_left 1).symm
  have henvelope : IntervalIntegrable
      (fun t : ℝ => c.Gint⁻¹ + (2 / c.gMin) * (1 - t) ^ (-c.kappa)) volume 0 1 :=
    intervalIntegrable_const.add (hp.const_mul _)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    at henvelope ⊢
  refine henvelope.mono' (measurable_retention P a).inv.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hr0 : 0 ≤ retention P a t := measureReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr0)]
  have hb := inv_retention_le_piecewise c P hP a ht.1.le ht.2
  have hg : 0 ≤ c.Gint⁻¹ := inv_nonneg.mpr c.Gint_pos.le
  have hp0 : 0 ≤ (2 / c.gMin) * (1 - t) ^ (-c.kappa) := mul_nonneg (div_nonneg (by norm_num) c.gMin_pos.le) (Real.rpow_nonneg (by linarith [ht.2]) _)
  split_ifs at hb <;> linarith

/-- The remaining ordinary target is continuous on the full horizon. -/
-- @node: continuousOn_remainingTarget_zero
@[fun_prop]
lemma continuousOn_remainingTarget_zero (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    ContinuousOn (remainingTarget c P a 0) (Icc (0 : ℝ) 1) := by
  have hi := modelClass_target_intervalIntegrable c P hP a
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have hc := intervalIntegral.continuousOn_primitive_interval_left
    (a := (0 : ℝ)) (b := 1) (f := fun t => survival P a t * P.lam a t)
    (by simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hi)
  unfold remainingTarget
  simpa only [continuationWeight, if_pos rfl, ite_true, sub_zero, one_mul,
    Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc

/-- The deterministic coefficient of inverse retention in the oracle energy
is continuous, since survival never vanishes on the horizon. -/
-- @node: continuousOn_subcriticalVarianceCoefficient
@[fun_prop]
lemma continuousOn_subcriticalVarianceCoefficient (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) :
    ContinuousOn (fun t => survival P a t * P.lam a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t / survival P a t)
      (Icc (0 : ℝ) 1) := by
  exact ((modelClass_survival_continuousOn c P hP a).mul
    (hP.recurrenceHolder a).1.continuousOn).add
    ((((continuousOn_remainingTarget_zero c P hP a).pow 2).mul
      (hP.deathHolder a).1.continuousOn).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne'))

/-- Subcritical oracle energy has a finite full-horizon integral, derived
from the endpoint tail and the bounded continuous energy coefficient. -/
-- @node: subcriticalVariance_density_intervalIntegrable
lemma subcriticalVariance_density_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm) :
    IntervalIntegrable (fun t =>
      survival P a t * P.lam a t / retention P a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t)) volume 0 1 := by
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t +
    (remainingTarget c P a 0 t) ^ 2 * P.hazard a t / survival P a t
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    continuousOn_subcriticalVarianceCoefficient c P hP a
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hi := inv_retention_intervalIntegrable_subcritical c P hP hk a
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    at hi ⊢
  have hprod : IntegrableOn (fun t => f t * (retention P a t)⁻¹) (Icc (0 : ℝ) 1) :=
    hi.bdd_mul (hf.aestronglyMeasurable measurableSet_Icc)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hB t ht)
  have heq : (fun t => survival P a t * P.lam a t / retention P a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t)) =
      (fun t => f t * (retention P a t)⁻¹) := by
    funext t
    dsimp [f]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  exact hprod

/-- The recurrence energy alone gives a strictly positive floor for each arm;
the death energy is nonnegative. -/
-- @node: subcriticalVariance_arm_integral_lower
lemma subcriticalVariance_arm_integral_lower (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm) :
    Real.exp (-c.dMax) * c.lambdaMin ≤
      ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
        (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) := by
  have hi := subcriticalVariance_density_intervalIntegrable c P hP hk a
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := Real.exp (-c.dMax) * c.lambdaMin)) hi
    (fun t ht => ?_)
  · simpa using hbound
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hr := retention_pos_of_modelClass c P hP a t ht.1.le ht.2
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht01
  have hl := hP.recurrenceBounds a t ht01
  have hd := hP.deathBounds a t ht01
  have hs0 : 0 < survival P a t := Real.exp_pos _
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hl.1
  have hnum : Real.exp (-c.dMax) * c.lambdaMin ≤ survival P a t * P.lam a t :=
    mul_le_mul hs.1 hl.1 c.lambdaMin_pos.le hs0.le
  have hdiv : survival P a t * P.lam a t ≤
      survival P a t * P.lam a t / retention P a t :=
    (le_div_iff₀ hr).2 (mul_le_of_le_one_right (mul_nonneg hs0.le hl0)
      (retention_le_one P a t))
  have hdeath : 0 ≤ (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
      (survival P a t * retention P a t) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans hd.1))
      (mul_nonneg hs0.le hr.le)
  linarith

/-- The full-horizon subcritical variance is nondegenerate under the declared
recurrence lower bound and treatment overlap. -/
-- @node: subcriticalVariance_pos
lemma subcriticalVariance_pos (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) :
    0 < subcriticalVariance c P := by
  have hpos (a : Arm) : 0 < (P.p a)⁻¹ *
      ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t +
        (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) := by
    exact mul_pos (inv_pos.mpr (c.pMin_pos.trans_le (hP.treatmentOverlap a)))
      ((mul_pos (Real.exp_pos _) c.lambdaMin_pos).trans_le
        (subcriticalVariance_arm_integral_lower c P hP hk a))
  unfold subcriticalVariance
  exact Finset.sum_pos (fun a _ => hpos a) Finset.univ_nonempty

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
