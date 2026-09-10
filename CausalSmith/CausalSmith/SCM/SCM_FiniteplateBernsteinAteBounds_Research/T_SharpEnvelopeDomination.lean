import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_SharpPrimalDual
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_BoundaryDiracRegression

/-! # Sharp domination of valid envelopes -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- Contact image of a Bernstein envelope with the causal integrand. -/
noncomputable def contactHull (m : ℕ) (ε : ℝ) (coeff : CountIndex m → ℝ) :
    Set (CountIndex m → ℝ) :=
  convexHull ℝ (momentMap m '' {q ∈ overlapSimplex ε |
    (∑ c, coeff c * bernsteinCoordinate m c q) = causalIntegrand q})

/-- Relative openness inside an ambient set. -/
def RelativelyOpenIn {α : Type*} [TopologicalSpace α] (ambient region : Set α) : Prop :=
  ∃ U : Set α, IsOpen U ∧ region = ambient ∩ U

/-- Every valid count-measurable envelope contains the sharp interval, with
equality exactly on its contact hull and strict improvement on nonempty
relatively open subsets when `m ≥ 2`. -/
-- @node: thm:sharp-envelope-domination
theorem sharp_envelope_domination (m : ℕ) (ε : ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ)) →
    ∀ pair ∈ validEnvelopeClass m ε, ∀ b ∈ bernsteinMomentBody m ε,
      Set.Icc (lowerEndpoint m ε b) (upperEndpoint m ε b) ⊆
        Set.Icc (coefficientValue pair.1 b) (coefficientValue pair.2 b) ∧
      (lowerEndpoint m ε b = coefficientValue pair.1 b ↔
        b ∈ contactHull m ε pair.1) ∧
      (upperEndpoint m ε b = coefficientValue pair.2 b ↔
        b ∈ contactHull m ε pair.2) ∧
      (2 ≤ m →
        (contactHull m ε pair.1 ⊂ bernsteinMomentBody m ε) ∧
        (contactHull m ε pair.2 ⊂ bernsteinMomentBody m ε) ∧
        ∃ lowerRegion upperRegion : Set (CountIndex m → ℝ),
          lowerRegion.Nonempty ∧ upperRegion.Nonempty ∧
          RelativelyOpenIn (intrinsicInterior ℝ (bernsteinMomentBody m ε)) lowerRegion ∧
          RelativelyOpenIn (intrinsicInterior ℝ (bernsteinMomentBody m ε)) upperRegion ∧
          (∀ x ∈ lowerRegion,
            coefficientValue pair.1 x < lowerEndpoint m ε x) ∧
          (∀ x ∈ upperRegion,
            upperEndpoint m ε x < coefficientValue pair.2 x)) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
