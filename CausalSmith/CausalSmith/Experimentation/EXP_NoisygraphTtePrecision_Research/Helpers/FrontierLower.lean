module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Estimators
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.BlockTestingLower
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ChannelTransfer
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MissingOnlyTesting
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.SeparatedPriorDecisions
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.TMarkedContraction
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingTestingLower

/-!
# Finite-size testing scales and the three lower costs

The calibrated matching-prior tests supply the false-edge lower bound.
Supported block tests and independent OR transfer supply the degree and missing-edge bound.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [Supported block tests and OR transfer retain the degree and missing-edge costs.](goal) -/
-- @node: degree_missing_lower
lemma degree_missing_lower (n d : ℕ) (hn : nZero ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) :
    ENNReal.ofReal (cLower * min 1 ((d : ℝ)^2/n + d/(n*q))) ≤
      minimaxRisk (noisyDesign (V := Fin n) q r) d := by
  have hl := degree_missing_risk_strong n d (by simpa [nZero] using hn) hd hdu q r hqr
  apply (ENNReal.ofReal_le_ofReal ?_).trans hl
  have hc : cLower ≤ 1/(1280000*Real.pi^2) := by
    unfold cLower
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hnonneg : 0 ≤ min 1 ((d : ℝ)^2/n + d/(n*q)) :=
    le_min (by norm_num) (add_nonneg (by positivity)
      (div_nonneg (by positivity) (mul_nonneg (by positivity) (hqr.1.trans hqr.2.1))))
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hc hnonneg
/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,hr,hregime), [In the planted-matching regime, supported causal-sign separation retains the false-edge cost.](goal) -/
-- @node: false_positive_lower
lemma false_positive_lower (n d : ℕ) (hn : nZero ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) (hr : 0 < r) (hregime : q/2 ≤ (n/2 : ℕ)*r) :
    ENNReal.ofReal (cLower * min 1 (r/q^2)) ≤ minimaxRisk (noisyDesign (V := Fin n) q r) d ∧
    ENNReal.ofReal (cLower * Real.sqrt (min 1 (r/q^2))) ≤
      minimaxLength (noisyDesign (V := Fin n) q r) d := by
  have hstrong := matching_false_positive_lower n d hn hd hdu q r hqr hr hregime
  have hc : cLower ≤ 1/(4*10^9*Real.pi^2) := by
    unfold cLower
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos Real.pi_pos]
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc
      (le_min (by norm_num) (by positivity)))).trans hstrong.1
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc
      (Real.sqrt_nonneg _))).trans hstrong.2

end CausalSmith.Experimentation.NoisygraphTtePrecision
