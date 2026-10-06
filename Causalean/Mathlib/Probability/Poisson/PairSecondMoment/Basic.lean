module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Mathlib.Algebra.Order.Chebyshev

/-!
# A finite bilinear sum and its pointwise square bound

The bilinear statistic is defined for arbitrary finite samples. Its square is
bounded by the number of index pairs times the sum of squared kernel values.
-/

@[expose] public section

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [a real kernel](hyp:K) and [two finite samples](hyp:s,t), [the
bilinear pair sum](goal) is given by [adding the kernel over every ordered
left-right pair](step:1). -/
def pairSum (K : X → Y → ℝ)
    (s : FiniteSample X) (t : FiniteSample Y) : ℝ :=
  ∑ i : Fin s.1, ∑ j : Fin t.1, K (s.2 i) (t.2 j)

/-- Given [a real kernel](hyp:K) and [two finite samples](hyp:s,t), [the
squared bilinear sum is bounded by its ordered-pair count times the sum of
squared kernel values](goal). -/
theorem pairSum_sq_le_count_mul_sum_sq (K : X → Y → ℝ)
    (s : FiniteSample X) (t : FiniteSample Y) :
    pairSum K s t ^ 2 ≤
      (s.1 : ℝ) * (t.1 : ℝ) *
        (∑ i : Fin s.1, ∑ j : Fin t.1, K (s.2 i) (t.2 j) ^ 2) := by
  -- Apply `sq_sum_le_card_mul_sum_sq` to the product of the two index
  -- finsets. Rewrite the product sum with `Finset.sum_product'`, and its
  -- cardinality with `Finset.card_product` and `Fintype.card_fin`.
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ)
    (f := fun p : Fin s.1 × Fin t.1 => K (s.2 p.1) (t.2 p.2))
  rw [← Finset.univ_product_univ, Finset.sum_product] at h
  rw [Finset.sum_product] at h
  simpa [pairSum, Finset.card_product, Fintype.card_fin, mul_assoc] using h

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment
