import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.LimitedPooling
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_SharpEnvelopeDomination
import Mathlib.Topology.Order.Compact

/-! # Optimized scalar-reference limited pooling -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- The limited-pooling envelopes are valid, their optimized extrema are
attained, their intersection contains the sharp interval, and both endpoints
improve simultaneously on one nonempty relatively open region when `m ≥ 2`.
No claim is made about a covariate-dependent procedure. -/
-- @node: prop:optimized-limited-pooling-intersection
theorem optimized_limited_pooling_intersection (m : ℕ) (ε : ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ)) →
    (∀ pstar ∈ Set.Icc ε (1 - ε),
      (lowerLWCoeff m ε pstar, upperLWCoeff m ε pstar) ∈
        validEnvelopeClass m ε) ∧
    (∀ b ∈ bernsteinMomentBody m ε,
      (∃ pLower ∈ Set.Icc ε (1 - ε),
        coefficientValue (lowerLWCoeff m ε pLower) b =
          sSup ((fun p => coefficientValue (lowerLWCoeff m ε p) b) ''
            Set.Icc ε (1 - ε))) ∧
      (∃ pUpper ∈ Set.Icc ε (1 - ε),
        coefficientValue (upperLWCoeff m ε pUpper) b =
          sInf ((fun p => coefficientValue (upperLWCoeff m ε p) b) ''
            Set.Icc ε (1 - ε))) ∧
      Set.Icc (lowerEndpoint m ε b) (upperEndpoint m ε b) ⊆
        limitedPoolingIntersection m ε b ∧
      limitedPoolingIntersection m ε b =
        ⋂ p ∈ Set.Icc ε (1 - ε), limitedPoolingInterval m ε p b) ∧
    (2 ≤ m → ∃ region : Set (CountIndex m → ℝ),
      region.Nonempty ∧ region ⊆ intrinsicInterior ℝ (bernsteinMomentBody m ε) ∧
      RelativelyOpenIn (intrinsicInterior ℝ (bernsteinMomentBody m ε)) region ∧
      (∀ b ∈ region,
        sSup ((fun p => coefficientValue (lowerLWCoeff m ε p) b) ''
          Set.Icc ε (1 - ε)) < lowerEndpoint m ε b ∧
        upperEndpoint m ε b <
          sInf ((fun p => coefficientValue (upperLWCoeff m ε p) b) ''
            Set.Icc ε (1 - ε)))) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
