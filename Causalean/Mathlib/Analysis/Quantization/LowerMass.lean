module
public import Causalean.Mathlib.Analysis.Quantization.LowerBad
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Good-region mass of a quantization partition

For a finite measurable partition of [a, b] into cells with reproduction points, each cell splits
into its bad region (points at distance at least δ from one of the cell's reproduction points) and
the remaining good region. The integral over [a, b] of the square root of the diagonal weight
Σ_s β_s(x, x), minus its integral over all bad regions, equals its integral over all good regions,
for continuous strictly positive weights β_s. This bookkeeping identity feeds the lower bound on
the optimal quantization cost.

## Main results

* `partition_good_mass_identity` — total square-root diagonal mass minus bad-region mass equals
  good-region mass, for an arbitrary measurable partition and any threshold δ.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- On [a nondegenerate interval](hyp:a,b,hab), [a nonempty finite
weight family](hyp:S,k,hS) with [continuous strictly positive
weights](hyp:β,hcont,hpos),
and [a measurable partition with reproductions and a distance threshold](hyp:B,z,hB,δ),
[total square-root mass minus bad-region mass equals good-region mass](goal). -/
theorem partition_good_mass_identity (a b : ℝ) (hab : a < b)
    (S k : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z)
    (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ)
    (hB : IsMeasurablePartition a b k B) (δ : ℝ) :
    (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) -
        ∑ j : Fin k, ∫ x in badRegion S k δ B z j,
          Real.sqrt (diagonalWeight S β x) =
      ∑ j : Fin k, ∫ x in B j \ badRegion S k δ B z j,
        Real.sqrt (diagonalWeight S β x) := by
  -- Use integral_iUnion_fintype on the measurable partition, then split
  -- each cell into its measurable bad region and complement. The interval
  -- integral agrees with the Icc set integral because endpoints are null.
  have hsub (j : Fin k) : B j ⊆ Set.Icc a b := by
    intro x hx
    rw [← hB.2.2]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hInt (j : Fin k) :
      IntegrableOn (fun x => Real.sqrt (diagonalWeight S β x)) (B j) volume :=
    ((sqrt_mass_regular a b hab S hS β hcont hpos).1.integrableOn_compact
      isCompact_Icc).mono_set (hsub j)
  have hsplit (j : Fin k) :
      (∫ x in B j \ badRegion S k δ B z j,
        Real.sqrt (diagonalWeight S β x)) =
        (∫ x in B j, Real.sqrt (diagonalWeight S β x)) -
          (∫ x in badRegion S k δ B z j,
            Real.sqrt (diagonalWeight S β x)) := by
    exact setIntegral_sdiff
      (badRegion_measurable S k δ B z hB.1 j) (hInt j)
      (by intro x hx; exact hx.1)
  have hpartition :
      (∫ x in Set.Icc a b, Real.sqrt (diagonalWeight S β x)) =
        ∑ j : Fin k, ∫ x in B j, Real.sqrt (diagonalWeight S β x) := by
    rw [← hB.2.2]
    exact integral_iUnion_fintype hB.1 hB.2.1 hInt
  rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
    hpartition]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]

end Causalean.Mathlib.Analysis.Quantization
