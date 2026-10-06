module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.Estimators

/-!
# Survival bounds from the death-hazard envelope

The cumulative hazard is nonnegative and at most the class upper bound on the
study horizon. These estimates supply the inverse-survival bound used in the
continuation bias and error decomposition arguments.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: survival_bounds_of_deathBounds
lemma survival_bounds_of_deathBounds (c : ClassConstants) (P : SubjectLaw)
    (hDeath : DeathBounds c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-c.dMax) ≤ survival P a t ∧ survival P a t ≤ 1 := by
  have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..t, P.hazard a u := by
    apply intervalIntegral.integral_nonneg ht.1
    intro u hu
    exact le_trans c.dMin_pos.le (hDeath a u ⟨hu.1, hu.2.trans ht.2⟩).1
  have hnorm :
      ‖∫ u in (0 : ℝ)..t, P.hazard a u‖ ≤ c.dMax * |t - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le ht.1] at hu
    have hbound := hDeath a u ⟨hu.1.le, hu.2.trans ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans c.dMin_pos.le hbound.1)]
    exact hbound.2
  have hcum : ∫ u in (0 : ℝ)..t, P.hazard a u ≤ c.dMax := by
    have hnorm' := (le_abs_self (∫ u in (0 : ℝ)..t, P.hazard a u)).trans
      (by simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using hnorm)
    have hdm : 0 ≤ c.dMax := le_trans c.dMin_pos.le c.dMin_lt.le
    nlinarith [mul_nonneg hdm (sub_nonneg.mpr ht.2)]
  unfold survival
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · simpa using Real.exp_le_exp.mpr (by linarith :
      -(∫ u in (0 : ℝ)..t, P.hazard a u) ≤ 0)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
