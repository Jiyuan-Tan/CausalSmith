/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevChordDefinitions
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.PairingRearrangement

/-!
# Factorization of paired Chebyshev chords

This module converts the adjacent-pair product of the trigonometric chord
list into the squared complex root-distance product.
-/

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

private lemma adjacentPairProduct_flatMap_pairs
    (t : ℝ) (xs : List ℕ) (a b : ℕ → ℝ) :
    adjacentPairProduct t (xs.flatMap fun k => [a k, b k]) =
      (xs.map fun k => a k * b k + t).prod := by
  induction xs with
  | nil => simp [adjacentPairProduct]
  | cons k xs ih => simp [adjacentPairProduct, ih]

/-- Pairing the two chord squares belonging to each Chebyshev root converts
`a*b + 4y²` into four times the squared distance from `cos θ + iy` to that
root. [the stated inputs](hyp:L,y) establish [the stated conclusion](goal). -/
theorem adjacentPairProduct_chebyshevPairedChordList
    (L : ℕ) (θ y : ℝ) :
    adjacentPairProduct (4 * y ^ 2) (chebyshevPairedChordList L θ) =
      ∏ k ∈ Finset.range L,
        4 * ‖((Real.cos θ - chebyshevZero L k : ℝ) : ℂ) +
          (y : ℂ) * Complex.I‖ ^ 2 := by
  have pair_identity (α : ℝ) :
      (2 - 2 * Real.cos (θ + α)) * (2 - 2 * Real.cos (θ - α)) + 4 * y ^ 2 =
        4 * ‖((Real.cos θ - Real.cos α : ℝ) : ℂ) +
          (y : ℂ) * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [Real.cos_add, Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq α]
  rw [chebyshevPairedChordList, adjacentPairProduct_flatMap_pairs]
  rw [Multiset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro k hk
  rw [cosineChordSq, chebyshevZero]
  exact pair_identity (chebyshevRootAngle L k)

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
