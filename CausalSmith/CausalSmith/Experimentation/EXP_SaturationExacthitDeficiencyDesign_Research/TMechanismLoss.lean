import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.GaussianGame
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-! # Exact-hit mechanism deficiency frontier -/

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:mechanism-loss
/-- Bernoulli hit mass scales the Gaussian game by `s_A(p)⁻¹/²`, yielding the
strict optimized mechanism-loss frontier and its exact equality criterion. -/
theorem mechanism_loss {n K : ℕ} [NeZero n] [NeZero K] (A : Finset (Fin K))
    (m : Fin K → ℕ) (v p : Fin K → ℝ)
    (hmenu : WellFormedMenu n K m) (hA : 2 ≤ A.card)
    (hv : ∀ k ∈ A, 0 < v k) (hp : InSimplex p) :
    let B := (hitMatrix n m p).1
    gaussianGlobalValueReal A v (matVec B p) =
      (activeHitMass A B p) ^ (-1 / 2 : ℝ) *
        gaussianGlobalValueReal A v (normalizedActiveHits A B p) ∧
    0 < activeHitMass A B p ∧
    activeHitMass A B p ≤ maximumActiveColumnMass A B ∧
    maximumActiveColumnMass A B < 1 ∧
    (faceMechanismValues B A v).1 / (faceMechanismValues B A v).2 ≥
      (maximumActiveColumnMass A B) ^ (-1 / 2 : ℝ) ∧
    1 < (maximumActiveColumnMass A B) ^ (-1 / 2 : ℝ) ∧
    ((faceMechanismValues B A v).1 / (faceMechanismValues B A v).2 =
      (maximumActiveColumnMass A B) ^ (-1 / 2 : ℝ) ↔
      ∃ pStar, InSimplex pStar ∧
        (∀ l, pStar l > 0 → ∑ k ∈ A, B k l = maximumActiveColumnMass A B) ∧
        gaussianGlobalValueReal A v (normalizedActiveHits A B pStar) =
          (faceMechanismValues B A v).2) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
