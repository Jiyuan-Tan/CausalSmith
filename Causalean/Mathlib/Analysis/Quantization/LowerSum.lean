module
public import Causalean.Mathlib.Analysis.Quantization.LowerBad
public import Causalean.Mathlib.Analysis.Quantization.LowerGood

/-! Sum the sharp local good-cell bound over an arbitrary measurable partition.
The good part of a cell is obtained by removing points far from at least one
of its reproduction points. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- On [a nondegenerate interval](hyp:a,b,hab), [a nonempty finite
weight family](hyp:S,hS) with [continuous strictly positive weights](hyp:β,hcont,hpos),
each relative error below one gives [a uniform threshold and a sharp
sum-of-good-cell-masses lower bound for every feasible partition](goal). -/
theorem partition_good_square_sum_lower (a b : ℝ) (hab : a < b)
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
              (∑ j : Fin k,
                (∫ x in B j \ badRegion S k δ B z j,
                  Real.sqrt (diagonalWeight S β x)) ^ 2) / 4 ≤
            weightedCost S k β B z := by
  intro η hη hη1
  obtain ⟨δ, hδ, hlocal⟩ :=
    good_cell_sqrt_mass_lower a b hab S hS β hcont hpos η hη hη1
  refine ⟨δ, hδ, ?_⟩
  intro k hk B z hB hz
  have hsub (j : Fin k) : B j ⊆ Set.Icc a b := by
    intro x hx
    rw [← hB.2.2]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hcell (j : Fin k) :
      (1 - η) *
          (∫ x in B j \ badRegion S k δ B z j,
            Real.sqrt (diagonalWeight S β x)) ^ 2 / 4 ≤
        ∑ s : Fin S, ∫ x in B j, β s x (z j s) * |x - z j s| := by
    apply hlocal (B j) (B j \ badRegion S k δ B z j) (z j)
      (hB.1 j) ((hB.1 j).diff (badRegion_measurable S k δ B z hB.1 j))
      (hsub j) (Set.sdiff_subset)
      (hz j)
    intro x hx s
    apply le_of_lt
    apply lt_of_not_ge
    intro hfar
    exact hx.2 ⟨hx.1, ⟨s, hfar⟩⟩
  calc
    (1 - η) *
        (∑ j : Fin k,
          (∫ x in B j \ badRegion S k δ B z j,
            Real.sqrt (diagonalWeight S β x)) ^ 2) / 4 =
        ∑ j : Fin k,
          (1 - η) *
            (∫ x in B j \ badRegion S k δ B z j,
              Real.sqrt (diagonalWeight S β x)) ^ 2 / 4 := by
          rw [Finset.mul_sum, Finset.sum_div]
    _ ≤ ∑ j : Fin k, ∑ s : Fin S,
        ∫ x in B j, β s x (z j s) * |x - z j s| :=
      Finset.sum_le_sum (fun j _ => hcell j)
    _ = weightedCost S k β B z := rfl

end Causalean.Mathlib.Analysis.Quantization
