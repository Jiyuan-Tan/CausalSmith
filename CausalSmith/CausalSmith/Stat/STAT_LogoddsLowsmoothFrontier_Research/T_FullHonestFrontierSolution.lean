module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_SharpHonestFrontier
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ConcreteArithmeticEngine

/-! # T FullHonestFrontierSolution

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @node: thm:full-honest-frontier-solution
/-- The full solution includes the concrete sequence and the same absolute guarantees for every implementation. [the stated conclusion](goal) holds. -/
theorem full_honest_frontier_solution : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  UniversalFrontier c C ∧ CompactUniform c C ∧
  (∀ α β : ℝ, ExponentDomain α β → ElbowIdentities α β) ∧
  (∀ α β : ℝ, ExponentDomain α β → ∀ n : ℕ, 1 ≤ n →
    HonestProcedure n α β (starInterval n α β) ∧
    (∀ ω, RationalOutputShape ((starInterval n α β).output ω)) ∧
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
      c*rate n α β r ≤ lengthObjective n α β r ∧
      lengthObjective n α β r ≤ worstLength n α β r (starInterval n α β) ∧
      worstLength n α β r (starInterval n α β) ≤ C*rate n α β r)) ∧
  (∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
    ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
      c*rate n α β r ≤ worstLength n α β r I) := by
  obtain ⟨c, C, hc, hC, hUniversal, hCompact, hElbows, hLower⟩ :=
    sharp_honest_frontier
  refine ⟨c, C, hc, hC, hUniversal, hCompact, hElbows, ?_, hLower⟩
  intro α β hDomain n hn
  obtain ⟨hOperational, hComparison⟩ :=
    hUniversal concreteEngine concreteEngine_admissible
      dyadicFloorPolicy fixed_budget_realization.1 α β hDomain n hn
  refine ⟨hOperational.1, hOperational.2.1, ?_⟩
  intro r hr
  exact hComparison r hr
end CausalSmith.Stat.LogoddsLowsmoothFrontier
