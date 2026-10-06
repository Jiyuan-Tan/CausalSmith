module
public import Causalean.Stat.UStatistic.LocalizedVariance.Bounds
public import Causalean.Stat.UStatistic.LocalizedVariance.Counting

/-!
# Covariance expansion and localized count bound

The variance of the unnormalized unordered pair sum is expanded into ordered
pair-of-pairs covariances. Identical, shared, and disjoint configurations are
bounded separately using the pair and squared row masses.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X]
  (P : Measure X) [IsProbabilityMeasure P]
  {H W : X → X → ℝ} {M : ℝ} (h : LocalizedKernel H W M)

include h

/-- A [probability law and localized-kernel certificate](hyp:P,h) give [an unnormalized pair
sum variance equal to its ordered covariance expansion](goal). -/
theorem pair_sum_variance_eq_covariance_sum {n : ℕ} :
    variance (fun ω => ∑ p ∈ pairIndices n, pairValue H p ω) (iidLaw P n) =
      ∑ p ∈ pairIndices n, ∑ q ∈ pairIndices n,
        covariance (pairValue H p) (pairValue H q) (iidLaw P n) := by
  have : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  exact variance_fun_sum' (fun p _ => pairValue_memLp_two P h p)

/-- A [probability law and localized-kernel certificate](hyp:P,h) with [at least two
observations](hyp:hn) give [an unnormalized pair-sum variance bound retaining both pair and
row mass scales](goal). -/
theorem pair_sum_variance_le_localized_counts {n : ℕ} (hn : 2 ≤ n) :
    variance (fun ω => ∑ p ∈ pairIndices n, pairValue H p ω) (iidLaw P n) ≤
      (n.choose 2 : ℝ) * (M ^ 2 * pairMass P W) +
        ((2 * (n.choose 2) * (n - 2) : ℕ) : ℝ) *
          (2 * M ^ 2 * rowMassSq P W) := by
  classical
  let s := pairIndices n
  let A : ℝ := M ^ 2 * pairMass P W
  let B : ℝ := 2 * M ^ 2 * rowMassSq P W
  have hpoint (pq : (Fin n × Fin n) × (Fin n × Fin n))
      (hpq : pq ∈ s.product s) :
      covariance (pairValue H pq.1) (pairValue H pq.2) (iidLaw P n) ≤
        if pq.1 = pq.2 then A else if SharesIndex pq.1 pq.2 then B else 0 := by
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    split_ifs with heq hshare
    · simpa only [heq, A] using covariance_identical_pair_le_pairMass P h hp
    · exact covariance_shared_pairs_le_rowMassSq P h hp hq heq hshare
    · rw [covariance_disjoint_pairs_eq_zero P h hp hq hshare]
  calc
    variance (fun ω => ∑ p ∈ s, pairValue H p ω) (iidLaw P n)
        = ∑ pq ∈ s.product s,
            covariance (pairValue H pq.1) (pairValue H pq.2) (iidLaw P n) := by
              symm
              change (∑ pq ∈ s ×ˢ s,
                covariance (pairValue H pq.1) (pairValue H pq.2) (iidLaw P n)) = _
              rw [Finset.sum_product]
              exact (pair_sum_variance_eq_covariance_sum P h).symm
    _ ≤ ∑ pq ∈ s.product s,
        (if pq.1 = pq.2 then A else if SharesIndex pq.1 pq.2 then B else 0) :=
          Finset.sum_le_sum hpoint
    _ = (n.choose 2 : ℝ) * A +
        ((2 * (n.choose 2) * (n - 2) : ℕ) : ℝ) * B := by
          simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
          rw [card_identical_pair_configurations,
            card_shared_pair_configurations hn]
    _ = _ := rfl

end Causalean.Stat.UStatistic.LocalizedVariance
