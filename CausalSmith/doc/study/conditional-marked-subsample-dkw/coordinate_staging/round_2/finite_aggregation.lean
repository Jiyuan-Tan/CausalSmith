import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Finite aggregation of conditional probability bounds

This module provides a paper-independent finite-partition identity and its
uniform-bound consequence.  Zero-probability cells are handled explicitly, so
applications only need conditional estimates on positive-probability cells.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

/-- Given [a probability measure](hyp:μ), [a finite collection of cells](hyp:C), [measurability
of every cell](hyp:hC), [pairwise disjointness of distinct cells](hyp:hdisj), [coverage of the whole sample space](hyp:hcover), [an event](hyp:E), and [measurability of that event](hyp:hE), [its probability equals the finite sum of cell mass times conditional event probability](goal). -/
theorem measure_eq_sum_mul_cond_of_finite_partition
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : ι → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⋃ i, C i) = Set.univ) (E : Set Ω) (hE : MeasurableSet E) :
    μ E = ∑ i, μ (C i) * μ[E | C i] := by
  -- Split `E` across the disjoint cover, then expand `cond_apply`; zero cells cancel separately.
  have hdisj_inter : Pairwise (fun i j ↦ Disjoint (C i ∩ E) (C j ∩ E)) := by
    intro i j hij
    exact (hdisj i j hij).mono inter_subset_left inter_subset_left
  calc
    μ E = μ ((⋃ i, C i) ∩ E) := by rw [hcover, univ_inter]
    _ = μ (⋃ i, C i ∩ E) := by rw [iUnion_inter]
    _ = ∑' i, μ (C i ∩ E) := measure_iUnion hdisj_inter fun i ↦ (hC i).inter hE
    _ = ∑ i, μ (C i ∩ E) :=
      tsum_fintype (L := .unconditional ι) (fun i ↦ μ (C i ∩ E))
    _ = ∑ i, μ (C i) * μ[E | C i] := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hzero : μ (C i) = 0
      · have hinter : μ (C i ∩ E) = 0 := measure_mono_null inter_subset_left hzero
        simp [hzero, hinter]
      · rw [cond_apply (hC i), ← mul_assoc,
          ENNReal.mul_inv_cancel hzero (measure_ne_top μ (C i)), one_mul]

/-- Given [a probability measure](hyp:μ), [a finite collection of cells](hyp:C), [measurability
of every cell](hyp:hC), [pairwise disjointness of distinct cells](hyp:hdisj), [coverage of the whole sample space](hyp:hcover), [an event](hyp:E), [measurability of that event](hyp:hE), [a probability bound](hyp:β), and [that bound conditional on each positive-mass cell](hyp:hcond), [the unconditional event probability is at most the same bound](goal). -/
theorem measure_le_of_cond_le_on_finite_partition
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : ι → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⋃ i, C i) = Set.univ) (E : Set Ω) (hE : MeasurableSet E)
    (β : ℝ≥0∞) (hcond : ∀ i, μ (C i) ≠ 0 → μ[E | C i] ≤ β) :
    μ E ≤ β := by
  -- Insert the exact finite sum, bound positive cells by `β`, and use that cell masses sum to one.
  rw [measure_eq_sum_mul_cond_of_finite_partition μ C hC hdisj hcover E hE]
  calc
    ∑ i, μ (C i) * μ[E | C i] ≤ ∑ i, μ (C i) * β := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hzero : μ (C i) = 0
      · simp [hzero]
      · simpa [mul_comm] using mul_le_mul_left (hcond i hzero) (μ (C i))
    _ = (∑ i, μ (C i)) * β := by rw [Finset.sum_mul]
    _ = 1 * β := by
      have hmass : ∑ i, μ (C i) = 1 := by
        simpa only [hcover, measure_univ, tsum_fintype] using
          (measure_iUnion (μ := μ) (fun i j hij ↦ hdisj i j hij) hC).symm
      rw [hmass]
    _ = β := one_mul β

end Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw
