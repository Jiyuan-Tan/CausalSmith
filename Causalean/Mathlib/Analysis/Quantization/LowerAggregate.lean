module
public import Causalean.Mathlib.Analysis.Quantization.LowerMass
public import Causalean.Mathlib.Analysis.Quantization.LowerSum
public import Mathlib.Algebra.Order.Chebyshev

/-! Aggregation of local good-cell moment estimates over a measurable
partition. Bad regions are retained explicitly as a mass deficit. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- On [a nondegenerate interval](hyp:a,b,hab), [a nonempty finite
weight family](hyp:S,hS) with [continuous strictly positive weights](hyp:β,hcont,hpos),
each relative error below one gives [a uniform mass-deficit lower
bound for the scaled cost of every feasible partition](goal). -/
theorem partition_good_mass_lower (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ : ℝ, 0 < δ ∧
      ∀ k : ℕ, 0 < k →
        ∀ (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ),
          IsMeasurablePartition a b k B →
          (∀ j s, z j s ∈ Set.Icc a b) →
          (1 - η) *
              ((∫ x in a..b, Real.sqrt (diagonalWeight S β x)) -
                ∑ j : Fin k,
                  ∫ x in badRegion S k δ B z j,
                    Real.sqrt (diagonalWeight S β x)) ^ 2 / 4 ≤
            (k : ℝ) * weightedCost S k β B z := by
  -- Apply partition_good_square_sum_lower to the good cells, then finite
  -- Cauchy-Schwarz to their masses. Use partition_good_mass_identity to
  -- identify the sum of those masses with total mass minus bad mass.
  intro η hη hη1
  obtain ⟨δ, hδ, hsum⟩ :=
    partition_good_square_sum_lower a b hab S hS β hcont hpos η hη hη1
  refine ⟨δ, hδ, ?_⟩
  intro k hk B z hB hz
  let m : Fin k → ℝ := fun j =>
    ∫ x in B j \ badRegion S k δ B z j,
      Real.sqrt (diagonalWeight S β x)
  have hcs : (∑ j : Fin k, m j) ^ 2 ≤
      (k : ℝ) * ∑ j : Fin k, (m j) ^ 2 := by
    simpa [m] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := m))
  have hfactor : 0 ≤ (1 - η) / 4 := by
    have : 0 ≤ 1 - η := sub_nonneg.mpr hη1.le
    positivity
  have hid := partition_good_mass_identity a b hab S k hS β hcont hpos B z hB δ
  calc
    (1 - η) *
        ((∫ x in a..b, Real.sqrt (diagonalWeight S β x)) -
          ∑ j : Fin k,
            ∫ x in badRegion S k δ B z j,
              Real.sqrt (diagonalWeight S β x)) ^ 2 / 4 =
      (1 - η) / 4 * (∑ j : Fin k, m j) ^ 2 := by
        rw [hid]
        ring
    _ ≤ (1 - η) / 4 * ((k : ℝ) * ∑ j : Fin k, (m j) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hfactor
    _ = (k : ℝ) * ((1 - η) *
        (∑ j : Fin k, (m j) ^ 2) / 4) := by ring
    _ ≤ (k : ℝ) * weightedCost S k β B z := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
      simpa [m] using hsum k hk B z hB hz

end Causalean.Mathlib.Analysis.Quantization
