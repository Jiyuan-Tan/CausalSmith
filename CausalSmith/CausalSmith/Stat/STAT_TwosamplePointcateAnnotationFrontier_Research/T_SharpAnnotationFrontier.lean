module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.NuisanceConverse
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.T_RectangularUpper
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.T_SuppliedPropensity

/-!
# T_SharpAnnotationFrontier

Two-channel point-CATE annotation frontier: T_SharpAnnotationFrontier
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- An original-record rule can be supplied to the oracle while ignoring its extra input.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [the oracle risk le minimax risk conclusion](goal) holds. -/
lemma oracleRisk_le_minimaxRisk (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ) :
    oracleRisk d alpha beta gamma L eps n m ≤ minimaxRisk d alpha beta gamma L eps n m := by
  unfold oracleRisk minimaxRisk
  apply Causalean.Stat.minimaxValueENNReal_le_minimaxValue
  intro T
  refine ⟨⟨fun w _ => T.1 w, fun _ => T.2⟩, ?_⟩
  exact le_rfl

/-- The oracle floor and the nuisance converse give one constant valid across all branches.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the sharp rate minimax lower conclusion](goal) holds. -/
lemma sharpRate_minimax_lower
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ n m, 2 ≤ n →
      ENNReal.ofReal (c * sharpRate d alpha beta gamma n m) ≤
        minimaxRisk d alpha beta gamma L eps n m := by
  obtain ⟨cO, CO, hcO, hcOC, horacle⟩ :=
    supplied_propensity d alpha beta gamma L eps hdom
  have hfloor (n m : ℕ) (hn : 2 ≤ n) :
      ENNReal.ofReal (cO * oracleRate d gamma n) ≤
        minimaxRisk d alpha beta gamma L eps n m :=
    (horacle n m hn).1.trans (oracleRisk_le_minimaxRisk d alpha beta gamma L eps n m)
  by_cases hS : alpha + beta < sCrit d gamma
  · obtain ⟨cB, hcB, hpair⟩ :=
      nuisance_frontier_converse d alpha beta gamma L eps hdom hS
    refine ⟨min cO cB, lt_min hcO hcB, ?_⟩
    intro n m hn
    have hbranches := rate_branches d alpha beta gamma L eps hdom n m hn
    by_cases hN : (n : ℝ) + m ≤ (n : ℝ) ^ qStar d alpha beta gamma
    · rw [hbranches.2.1 hS hN]
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right cO cB)
        (Real.rpow_nonneg (by positivity) _))).trans (hpair n m hn hN)
    · rw [hbranches.2.2.1 hS (le_of_not_ge hN)]
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left cO cB)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans (hfloor n m hn)
  · refine ⟨cO, hcO, ?_⟩
    intro n m hn
    rw [(rate_branches d alpha beta gamma L eps hdom n m hn).1 (le_of_not_gt hS)]
    exact hfloor n m hn

-- @node: thm:sharp-annotation-frontier
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the sharp annotation frontier conclusion](goal) holds. -/
theorem sharp_annotation_frontier
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ -- @realizes c(positive claim-local constant) @realizes C(finite claim-local upper constant)
       ∀ (n m : ℕ), 2 ≤ n →
      ∃ hMeas : Measurable (sharpDecision d alpha beta gamma eps n m),
        ENNReal.ofReal (c*sharpRate d alpha beta gamma n m) ≤ minimaxRisk d alpha beta gamma L eps n m ∧
        minimaxRisk d alpha beta gamma L eps n m ≤
          Causalean.Stat.worstCaseRiskENNReal (classRisk d alpha beta gamma L eps n m)
            ⟨sharpDecision d alpha beta gamma eps n m,hMeas⟩ ∧
        Causalean.Stat.worstCaseRiskENNReal (classRisk d alpha beta gamma L eps n m)
          ⟨sharpDecision d alpha beta gamma eps n m,hMeas⟩ ≤ ENNReal.ofReal (C*sharpRate d alpha beta gamma n m) ∧
        (∀ T : Decision d n m, ENNReal.ofReal (c*sharpRate d alpha beta gamma n m) ≤
          Causalean.Stat.worstCaseRiskENNReal (classRisk d alpha beta gamma L eps n m) T) ∧
        (sCrit d gamma ≤ alpha+beta → sharpRate d alpha beta gamma n m = oracleRate d gamma n) ∧
        (alpha+beta < sCrit d gamma → (n:ℝ)+m ≤ (n:ℝ)^qStar d alpha beta gamma →
          sharpRate d alpha beta gamma n m = ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) ∧
        (alpha+beta < sCrit d gamma → (n:ℝ)^qStar d alpha beta gamma ≤ (n:ℝ)+m →
          sharpRate d alpha beta gamma n m = oracleRate d gamma n) ∧
        ((n:ℝ)+m = (n:ℝ)^qStar d alpha beta gamma →
          ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma)) = oracleRate d gamma n) := by
  obtain ⟨c, hc, hlower⟩ := sharpRate_minimax_lower d alpha beta gamma L eps hdom
  obtain ⟨CU, hCU, hrect, hup⟩ := rectangular_upper d alpha beta gamma L eps hdom
  refine ⟨c, max c CU, hc, le_max_left _ _, ?_⟩
  intro n m hn
  obtain ⟨hMeas, hpoint⟩ := hup n m hn
  have hsharp : Measurable (sharpDecision d alpha beta gamma eps n m) := hMeas
  have hupper : Causalean.Stat.worstCaseRiskENNReal (classRisk d alpha beta gamma L eps n m)
      ⟨sharpDecision d alpha beta gamma eps n m, hsharp⟩ ≤
      ENNReal.ofReal (max c CU * sharpRate d alpha beta gamma n m) := by
    apply Causalean.Stat.worstCaseRiskENNReal_le
    intro P
    have hr := hpoint P.1 P.2
    change risk ⟨sharpDecision d alpha beta gamma eps n m, hsharp⟩ P.1 P.2 ≤ _ at hr
    apply hr.trans
    rw [← sharpRate_eq_upperRate]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right (le_max_right c CU)
    exact le_trans (Real.rpow_nonneg (Nat.cast_nonneg n) _) (le_max_left _ _)
  have hmin : minimaxRisk d alpha beta gamma L eps n m ≤
      Causalean.Stat.worstCaseRiskENNReal (classRisk d alpha beta gamma L eps n m)
        ⟨sharpDecision d alpha beta gamma eps n m, hsharp⟩ :=
    Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk _
  refine ⟨hsharp, hlower n m hn, hmin, hupper, ?_,
    rate_branches d alpha beta gamma L eps hdom n m hn⟩
  intro T
  exact (hlower n m hn).trans (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk T)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
