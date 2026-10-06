module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRisk

/-! # Positivity of the computable calibration constants

The variance and extinction envelopes are positive directly from the class
constants. Their sum makes the conservative-interval calibration strictly
positive without using an unproved risk or asymptotic assertion.
-/

public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The continuation weight envelope is at least one. -/
-- @node: one_le_weightEnvelope
lemma one_le_weightEnvelope (c : ClassConstants) : 1 ≤ weightEnvelope c := by
  have h : 0 ≤ continuationNorm c := by
    unfold continuationNorm
    apply Finset.sum_nonneg
    intro m _
    positivity
  unfold weightEnvelope
  linarith

/-- The inverse-retention envelope is positive in each endpoint regime. -/
-- @node: reciprocalRetentionEnvelope_pos
lemma reciprocalRetentionEnvelope_pos (c : ClassConstants) :
    0 < reciprocalRetentionEnvelope c := by
  have hi : 0 ≤ (1 - c.x0) / c.Gint := by
    apply div_nonneg _ c.Gint_pos.le
    linarith [c.x0_le]
  unfold reciprocalRetentionEnvelope
  split_ifs with hlt heq
  · have ht : 0 < 2 * c.x0 ^ (1 - c.kappa) / (c.gMin * (1 - c.kappa)) :=
      div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos c.x0_pos _))
        (mul_pos c.gMin_pos (by linarith))
    linarith
  · have ht := div_pos (by norm_num : (0 : ℝ) < 2) c.gMin_pos
    linarith
  · have ht : 0 < 2 / (c.gMin * (c.kappa - 1)) :=
      div_pos (by norm_num) (mul_pos c.gMin_pos (by
        have hk : 1 < c.kappa := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        linarith))
    linarith

/-- The explicit variance coefficient is strictly positive. -/
-- @node: explicitVarianceRisk_pos
lemma explicitVarianceRisk_pos (c : ClassConstants) : 0 < explicitVarianceRisk c := by
  have hr := reciprocalRetentionEnvelope_pos c
  have hw : 0 < weightEnvelope c := lt_of_lt_of_le (by norm_num) (one_le_weightEnvelope c)
  have hl : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  have hd : 0 < c.dMax := c.dMin_pos.trans c.dMin_lt
  have hp := c.pMin_pos
  unfold explicitVarianceRisk
  positivity

/-- The explicit extinction coefficient is strictly positive. -/
-- @node: explicitExtinctionRisk_pos
lemma explicitExtinctionRisk_pos (c : ClassConstants) : 0 < explicitExtinctionRisk c := by
  have hw : 0 < weightEnvelope c := lt_of_lt_of_le (by norm_num) (one_le_weightEnvelope c)
  have hl : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  unfold explicitExtinctionRisk
  positivity

/-- The variance-to-rate envelope is positive in all three regimes. -/
-- @node: varianceRateEnvelope_pos
lemma varianceRateEnvelope_pos (c : ClassConstants) : 0 < varianceRateEnvelope c := by
  unfold varianceRateEnvelope
  dsimp only
  split_ifs with hlt heq
  · norm_num
  · have ha : 0 < bandwidthExponent c := by
      unfold bandwidthExponent
      rw [if_pos (by linarith : c.kappa ≤ 1)]
      apply inv_pos.mpr
      linarith [c.beta_pos]
    have hh : 0 < c.x0 / 2 := by linarith [c.x0_pos]
    have hh1 : c.x0 / 2 ≤ 1 := by linarith [c.x0_le]
    have hlog : 0 ≤ Real.log (1 / (c.x0 / 2)) :=
      Real.log_nonneg ((one_le_div₀ hh).2 hh1)
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have ht : 0 < (1 + Real.log (1 / (c.x0 / 2))) / Real.log 3 :=
      div_pos (by linarith) hlog3
    linarith
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The analytic tail envelope is nonnegative even before proving its
extinction-rate comparison. -/
-- @node: extinctionTailEnvelope_nonneg
lemma extinctionTailEnvelope_nonneg (c : ClassConstants) :
    0 ≤ extinctionTailEnvelope c := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold extinctionTailEnvelope
  dsimp only
  split_ifs <;> positivity

/-- The declared calibration is positive for every positive miscoverage level. -/
-- @node: honestConstant_pos
lemma honestConstant_pos (c : ClassConstants) {alpha : ℝ} (ha : 0 < alpha) :
    0 < honestConstant c alpha := by
  have hb : 0 ≤ explicitBiasRisk c := by unfold explicitBiasRisk; positivity
  have hv := mul_pos (explicitVarianceRisk_pos c) (varianceRateEnvelope_pos c)
  have he : 0 ≤ explicitExtinctionRisk c *
      max (extinctionPreEnvelope c) (extinctionTailEnvelope c) :=
    mul_nonneg (explicitExtinctionRisk_pos c).le
      ((extinctionTailEnvelope_nonneg c).trans (le_max_right _ _))
  unfold honestConstant
  apply div_pos _ ha
  nlinarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
