import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.Chebyshev
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.CitedAnalysis
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Analysis.Convex.Intrinsic

/-! # Growing-plate identification modulus -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- Width of one sharp fiber. -/
noncomputable def identifiedWidth (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) : ℝ :=
  upperEndpoint m ε b - lowerEndpoint m ε b

/-- Conditional on the three cited functional-analysis gates, the worst and
relative-interior widths equal twice the uniform approximation modulus and
obey the shifted-Chebyshev exponential bound and plate-size guarantee. -/
-- @node: thm:growing-plate-identification-modulus
theorem growing_plate_identification_modulus
    (hHahnBanach_of_gate : HahnBanachQuotientNorm)
    (hRieszMarkov_of_gate : RieszMarkovRepresentation)
    (hJordanDecomposition_of_gate : JordanDecompositionSignedMeasure)
    (m : ℕ) (ε : ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ)) →
    sSup (identifiedWidth m ε '' bernsteinMomentBody m ε) =
        2 * uniformIdentificationModulus m ε ∧
    (∃ b ∈ bernsteinMomentBody m ε,
      identifiedWidth m ε b = 2 * uniformIdentificationModulus m ε) ∧
    sSup (identifiedWidth m ε ''
        intrinsicInterior ℝ (bernsteinMomentBody m ε)) =
        2 * uniformIdentificationModulus m ε ∧
    0 < uniformIdentificationModulus m ε ∧
    uniformIdentificationModulus m ε ≤ chebyshevError m ε ∧
    chebyshevError m ε =
      1 / Real.cosh (m * Real.arcosh (1 / (1 - 2 * ε))) ∧
    chebyshevError m ε ≤ (1 - 2 * ε) ^ m ∧
    (2 ≤ m → chebyshevError m ε < (1 - 2 * ε) ^ m) ∧
    (∀ b ∈ bernsteinMomentBody m ε,
      identifiedWidth m ε b ≤
        2 / Real.cosh (m * Real.arcosh (1 / (1 - 2 * ε)))) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 2 →
      Real.arcosh (2 / δ) / Real.arcosh (1 / (1 - 2 * ε)) ≤ m →
      ∀ b ∈ bernsteinMomentBody m ε, identifiedWidth m ε b ≤ δ) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
