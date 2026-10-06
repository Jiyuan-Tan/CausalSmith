module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FullHonestFrontierSolution

/-! # T FullHonestFrontierAnswer

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @node: thm:full-honest-frontier-answer
/-- The explicit power profile and one concrete data-only sequence answer the full honest-frontier question. [the stated conclusion](goal) holds. -/
theorem full_honest_frontier_answer : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  UniversalFrontier c C ∧ CompactUniform c C ∧
  (∀ α β : ℝ, ExponentDomain α β → ElbowIdentities α β) ∧
  (∀ α β : ℝ, ExponentDomain α β → ∀ n : ℕ, 1 ≤ n →
    HonestProcedure n α β (starInterval n α β) ∧
    (∀ ω, RationalOutputShape ((starInterval n α β).output ω)) ∧
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
      let ρ := (n : ℝ)^(-min (1/2) (2*(α+β)/(2*α+2*β+1)))+
        r*(n : ℝ)^(-(4*β/(4*β+1)))
      c*ρ ≤ lengthObjective n α β r ∧
      lengthObjective n α β r ≤ worstLength n α β r (starInterval n α β) ∧
      worstLength n α β r (starInterval n α β) ≤ C*ρ)) ∧
  (∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
    ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
      c*rate n α β r ≤ worstLength n α β r I) := by
  obtain ⟨c, C, hc, hC, hUniversal, hCompact, hElbows, hConcrete, hLower⟩ :=
    full_honest_frontier_solution
  refine ⟨c, C, hc, hC, hUniversal, hCompact, hElbows, ?_, hLower⟩
  intro α β hDomain n hn
  obtain ⟨hHonest, hRational, hComparison⟩ := hConcrete α β hDomain n hn
  refine ⟨hHonest, hRational, ?_⟩
  intro r hr
  simpa only [rate, diagnosticEnvelope, exponentA, exponentB] using hComparison r hr
end CausalSmith.Stat.LogoddsLowsmoothFrontier
