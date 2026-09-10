import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.ScalarMixture

/-!
# One-sided moment priors at the boundary

This module isolates the approximation-theoretic ingredient needed when a
coordinate of the fixed comparison distribution is of order `log n / n` or
smaller.  Unlike the symmetric interior construction, these priors may put
mass at zero.  Their common first moment controls the total mass of the raw
vector, while their absolute-deviation gap has the boundary-optimal scale.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- A one-sided boundary pair consists of laws on `[0,1]` with a prescribed
common mean, matching higher moments, and a separated absolute deviation
about `a`. -/
structure BoundaryMomentPriorPair (K : ℕ) (a : ℝ≥0) (mean : ℝ) where
  /-- Lower-target scalar law. -/
  ν0 : Measure ℝ≥0
  /-- Upper-target scalar law. -/
  ν1 : Measure ℝ≥0
  /-- The lower law is a probability measure. -/
  ν0_probability : IsProbabilityMeasure ν0
  /-- The upper law is a probability measure. -/
  ν1_probability : IsProbabilityMeasure ν1
  /-- The lower law is supported on `[0,1]`. -/
  ν0_support : ν0 (Set.Icc 0 1) = 1
  /-- The upper law is supported on `[0,1]`. -/
  ν1_support : ν1 (Set.Icc 0 1) = 1
  /-- The lower law has the prescribed first moment. -/
  mean0 : (∫ x, (x : ℝ) ∂ν0) = mean
  /-- The upper law has the prescribed first moment. -/
  mean1 : (∫ x, (x : ℝ) ∂ν1) = mean
  /-- Moments through degree `K+1` agree. -/
  moments_eq : ∀ k ≤ K + 1,
    (∫ x, (x : ℝ) ^ k ∂ν0) = ∫ x, (x : ℝ) ^ k ∂ν1

/-- The oriented absolute-deviation gap of a boundary prior pair. -/
noncomputable def BoundaryMomentPriorPair.absGap {K : ℕ} {a : ℝ≥0} {mean : ℝ}
    (W : BoundaryMomentPriorPair K a mean) : ℝ :=
  absMomentAbout W.ν1 a - absMomentAbout W.ν0 a

/-- Universal one-sided moment priors exist with the boundary-optimal gap.

The proof is the weighted Hahn–Banach construction for
`(|x-a|-a)/x` on `[a/D,1]`, followed by multiplication of each law by
`(a/D)/x` and placement of the missing mass at zero.  This is the precise
approximation-theoretic lemma used in the small-coordinate case of
Jiao–Han–Weissman. -/
theorem exists_boundaryMomentPriorPair :
    ∃ c D : ℝ, 0 < c ∧ 1 < D ∧
      ∀ (K : ℕ) (a : ℝ≥0), 2 ≤ K → 0 < a → (a : ℝ) ≤ 1 / 2 →
        ∃ W : BoundaryMomentPriorPair K a ((a : ℝ) / D),
          c * min (a : ℝ) (Real.sqrt (a : ℝ) / (K + 1 : ℝ)) ≤ W.absGap := by
  sorry

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
