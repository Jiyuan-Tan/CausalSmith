import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact finite rational witnesses for the three-arm scalar-compression diagnostic. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The full-data rule risk bound is the exact rational certificate used for the three-arm full-information procedure. -/
def fullDataRuleRiskBound : ℚ := 511653 / 4000000
/-- The scalar Bayes certificate is the exact rational lower bound used for the compressed-score experiment. -/
def scalarBayesCertificate : ℚ := 18213 / 136000

/-- [the three-arm rational separation property holds](goal). -/
lemma k3_rational_separation :
    (fullDataRuleRiskBound : ℝ) < (scalarBayesCertificate : ℝ) ∧
      (13 / 100 : ℝ) < 1 - Real.sqrt 3 / 2 := by
  constructor
  · norm_num [fullDataRuleRiskBound, scalarBayesCertificate]
  · have hsqrt : Real.sqrt 3 < 87 / 50 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 87 / 50)]
      norm_num
    linarith

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
