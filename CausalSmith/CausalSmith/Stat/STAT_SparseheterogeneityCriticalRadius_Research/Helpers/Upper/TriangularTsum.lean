module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Mixture

/-! A finite triangular part of a nonnegative double series is bounded by the
full iterated series. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

lemma triangular_sum_le_iterated_tsum (r : ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ u v, 0 ≤ a u v) (hinner : ∀ u, Summable (a u))
    (houter : Summable (fun u => ∑' v, a u v)) :
    (∑ u ∈ Finset.range (r + 1),
      ∑ v ∈ Finset.range (r - u + 1), a u v) ≤
      ∑' u, ∑' v, a u v := by
  calc
    _ ≤ ∑ u ∈ Finset.range (r + 1), ∑' v, a u v := by
      apply Finset.sum_le_sum
      intro u hu
      exact (hinner u).sum_le_tsum (Finset.range (r - u + 1))
        (fun v hv => ha u v)
    _ ≤ ∑' u, ∑' v, a u v :=
      houter.sum_le_tsum (Finset.range (r + 1))
        (fun u hu => tsum_nonneg (ha u))

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
