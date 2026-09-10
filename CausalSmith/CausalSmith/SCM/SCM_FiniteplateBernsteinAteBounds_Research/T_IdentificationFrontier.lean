import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.FullSupport

/-! # Finite-plate identification frontier -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

/-- A continuous functional is determined by every feasible Bernstein moment fiber. -/
def UniversallyMomentIdentified (m : ℕ) (ε : ℝ) (h : CellLaw → ℝ) : Prop :=
  ∀ b ∈ bernsteinMomentBody m ε, ∀ ν₁ ∈ momentFiber m ε b, ∀ ν₂ ∈ momentFiber m ε b,
    (∫ q, h q ∂ν₁) = ∫ q, h q ∂ν₂

/-- A continuous functional is universally identified exactly when it lies in
the Bernstein span; the causal integrand therefore has strictly positive width
on every relative-interior fiber at each finite positive plate size. -/
-- @node: thm:identification-frontier
theorem identification_frontier (m : ℕ) (ε : ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ)) →
    (∀ h : CellLaw → ℝ, ContinuousOn h (overlapSimplex ε) →
      (UniversallyMomentIdentified m ε h ↔
        ∃ v ∈ bernsteinSpan m, Set.EqOn h v (overlapSimplex ε))) ∧
    ¬ UniversallyMomentIdentified m ε causalIntegrand ∧
    ∀ b ∈ intrinsicInterior ℝ (bernsteinMomentBody m ε),
      lowerEndpoint m ε b < upperEndpoint m ε b := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
