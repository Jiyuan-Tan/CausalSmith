module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FixedBudgetRealization

/-! # Defs/FrontierSpecifications

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- The two explicit radius-elbow identities, with positivity and shared-boundary agreement. -/
def ElbowIdentities (α β : ℝ) : Prop :=
  0 < exponentA α β-exponentB β ∧
  (α+β ≤ 1/2 → exponentA α β-exponentB β =
    2*(α-β)/((2*α+2*β+1)*(4*β+1))) ∧
  (1/2 ≤ α+β → exponentA α β-exponentB β = (1-4*β)/(2*(4*β+1))) ∧
  (α+β = 1/2 → 2*(α-β)/((2*α+2*β+1)*(4*β+1)) = (1-4*β)/(2*(4*β+1)))
/-- Compact-uniform bounds, expressed as the actual infimum/supremum conditions. -/
def CompactUniform (c C : ℝ) : Prop :=
  ∀ K : Set (ℝ × ℝ), K.Nonempty → IsCompact K →
    K ⊆ {ab | ExponentDomain ab.1 ab.2} →
      0 < sInf ((fun _ : ℝ × ℝ => c) '' K) ∧
      (⨆ ab ∈ K, ENNReal.ofReal C) < ⊤ ∧
      sSup ((fun _ : ℝ × ℝ => (1 : ℕ)) '' K) = 1
  -- @realizes \mathcal K(nonempty compact subset of the public domain)
/-- The all-radius expected-length comparison for one literal implementation. -/
def FrontierComparison (c C : ℝ) (E : ArithmeticEngine) (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (α β r : ℝ) : Prop :=
  c*rate n α β r ≤ lengthObjective n α β r ∧
  lengthObjective n α β r ≤ worstLength n α β r (upperInterval E N hN n α β) ∧
  worstLength n α β r (upperInterval E N hN n α β) ≤ C*rate n α β r
/-- The operational guarantees are properties of the actual supplied-engine output. -/
def FrontierOperational (E : ArithmeticEngine) (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (α β : ℝ) : Prop :=
  HonestProcedure n α β (upperInterval E N hN n α β) ∧
  (∀ ω, RationalOutputShape ((upperInterval E N hN n α β).output ω)) ∧
  (∀ o u v, (upperInterval E N hN n α β).output (o,u) =
      (upperInterval E N hN n α β).output (o,v)) ∧
  (n = 1 → ∀ ω, intervalSet ((upperInterval E N hN n α β).output ω) = Set.Icc (-(1/2 : ℝ)) (1/2))
/-- Concrete sequence uses precisely the certified concrete engine and the floor policy. -/
def starInterval (n : ℕ) (α β : ℝ) : Procedure n :=
  upperInterval concreteEngine dyadicFloorPolicy fixed_budget_realization.1 n α β
/-- Parameter-independent universal generalization of the sharp comparison and output guarantees. -/
def UniversalFrontier (c C : ℝ) : Prop :=
  ∀ (E : ArithmeticEngine), E.Admissible →
  ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
  ∀ n : ℕ, 1 ≤ n →
    FrontierOperational E N hN n α β ∧
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) → FrontierComparison c C E N hN n α β r)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
