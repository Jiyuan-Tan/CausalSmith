module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformTaggedRank

/-!
# Finite uniform order-statistic CDF

The counting identity and binomial-tail law needed to identify an adjacent
order-statistic mixture with a Bernstein hinge kernel.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- The `r`th sorted coordinate is at most a threshold exactly when at least
`r+1` coordinates of the original finite tuple are at most that threshold. -/
theorem sortedSample_le_iff_count_le {n : ℕ} (x : Fin n → ℝ)
    (r : Fin n) (u : ℝ) :
    sortedSample n x r ≤ u ↔
      r.val + 1 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u)).card := by
  -- Sorting is a permutation. In a monotone tuple, the initial segment below
  -- `u` contains position `r` iff its cardinality is at least `r+1`.
  let σ := Tuple.sort x
  have hcard :
      ((Finset.univ : Finset (Fin n)).filter (fun i => (x ∘ σ) i ≤ u)).card =
        ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u)).card := by
    apply Finset.card_equiv σ
    intro i
    simp [Function.comp_apply]
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone
    (f := x ∘ σ) (a := u) (j := r) (Tuple.monotone_sort x)
  simpa only [sortedSample, σ, hcard, Fin.val_fin_lt, Nat.lt_iff_add_one_le] using h.symm

/-- In an iid sample of `n` unit uniforms, the number of coordinates at most
`u` has the binomial mass with parameters `n` and `u`. -/
theorem uniform_count_le_mass (n k : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    iidSample uniform01 n
      {x | ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u)).card = k} =
      ENNReal.ofReal ((Nat.choose n k : ℝ) * u ^ k * (1 - u) ^ (n - k)) := by
  -- `uniform_subset_lt_count_mass` proves the strict-threshold version.
  -- Each coordinate equals the fixed threshold only on a null set.
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  have hsingle : uniform01 ({u} : Set ℝ) = 0 := by
    simp [uniform01]
  have hcoord (i : Fin n) : ∀ᵐ x ∂iidSample uniform01 n, x i ≠ u := by
    have hp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => uniform01) i
    have hs : iidSample uniform01 n {x | x i = u} = 0 := by
      have hpre : (fun x : Fin n → ℝ => x i) ⁻¹' ({u} : Set ℝ) =
          {x | x i = u} := by ext x; simp
      calc
        iidSample uniform01 n {x | x i = u} = uniform01 ({u} : Set ℝ) := by
          rw [← hpre]
          exact hp.measure_preimage (measurableSet_singleton u).nullMeasurableSet
        _ = 0 := hsingle
    exact (ae_iff).2 (by simpa only [not_not] using hs)
  have hno : ∀ᵐ x ∂iidSample uniform01 n, ∀ i : Fin n, x i ≠ u := by
    simpa only [Filter.eventually_all] using hcoord
  have heq : {x : Fin n → ℝ |
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u)).card = k} =ᵐ[iidSample uniform01 n]
      {x : Fin n → ℝ |
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i < u)).card = k} := by
    filter_upwards [hno] with x hx
    have hf : (Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u) =
        (Finset.univ : Finset (Fin n)).filter (fun i => x i < u) := by
      ext i
      simp [lt_iff_le_and_ne, hx i]
    change (((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u)).card = k) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => x i < u)).card = k)
    rw [hf]
  rw [measure_congr heq]
  simpa using uniform_subset_lt_count_mass (Finset.univ : Finset (Fin n)) k hu

/-- A [sorted position](hyp:r) and [unit-interval threshold](hyp:hu) give
[the upper-binomial-tail formula for its iid uniform CDF](goal). -/
theorem uniform_sorted_cdf_eq_binomial_tail {n : ℕ} (r : Fin n)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ((iidSample uniform01 n).map (fun x => sortedSample n x r)) (Set.Iic u) =
      ENNReal.ofReal
        (∑ k ∈ Finset.Icc (r.val + 1) n,
          (Nat.choose n k : ℝ) * u ^ k * (1 - u) ^ (n - k)) := by
  -- Use `sortedSample_le_iff_count_le`, partition by the finite count,
  -- and sum `uniform_count_le_mass` over the upper tail. Mathlib's
  -- `MeasureTheory.sum_measure_preimage_singleton` gives the finite
  -- partition directly for the count function and `Finset.Icc (r.val+1) n`.
  -- Its measurability follows by a finite sum of indicators of the
  -- measurable coordinate events `{x | x i ≤ u}`.
  let count : (Fin n → ℝ) → ℕ := fun x =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ u)).card
  have hcount : Measurable count := by
    have hsum : Measurable (fun x : Fin n → ℝ =>
        ∑ i : Fin n, if x i ≤ u then (1 : ℕ) else 0) := by
      apply Finset.measurable_sum
      intro i hi
      exact Measurable.ite ((measurable_pi_apply i) measurableSet_Iic)
        measurable_const measurable_const
    simpa only [count, Finset.card_filter] using hsum
  have hsorted : Measurable (fun x : Fin n → ℝ => sortedSample n x r) := by
    apply measurable_of_Iic
    intro t
    have ht : (fun x : Fin n → ℝ => sortedSample n x r) ⁻¹' Set.Iic t =
        {x | r.val + 1 ≤ ((Finset.univ : Finset (Fin n)).filter
          (fun i => x i ≤ t)).card} := by
      ext x
      exact sortedSample_le_iff_count_le x r t
    rw [ht]
    have hcount_t : Measurable (fun x : Fin n → ℝ =>
        ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≤ t)).card) := by
      have hsum : Measurable (fun x : Fin n → ℝ =>
          ∑ i : Fin n, if x i ≤ t then (1 : ℕ) else 0) := by
        apply Finset.measurable_sum
        intro i hi
        exact Measurable.ite ((measurable_pi_apply i) measurableSet_Iic)
          measurable_const measurable_const
      simpa only [Finset.card_filter] using hsum
    exact measurableSet_le measurable_const hcount_t
  have hpre : (fun x : Fin n → ℝ => sortedSample n x r) ⁻¹' Set.Iic u =
      count ⁻¹' (Finset.Icc (r.val + 1) n : Set ℕ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · intro hx
      exact ⟨(sortedSample_le_iff_count_le x r u).mp hx,
        by simpa only [count, Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.filter_subset (fun i => x i ≤ u) Finset.univ)⟩
    · intro hx
      exact (sortedSample_le_iff_count_le x r u).mpr hx.1
  rw [Measure.map_apply hsorted measurableSet_Iic, hpre]
  rw [← MeasureTheory.sum_measure_preimage_singleton
    (μ := iidSample uniform01 n) (Finset.Icc (r.val + 1) n)
    (fun k hk => hcount (measurableSet_singleton k))]
  calc
    ∑ k ∈ Finset.Icc (r.val + 1) n, iidSample uniform01 n (count ⁻¹' {k}) =
        ∑ k ∈ Finset.Icc (r.val + 1) n,
          ENNReal.ofReal ((Nat.choose n k : ℝ) * u ^ k * (1 - u) ^ (n - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact uniform_count_le_mass n k hu
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro k hk
      have hu0 : 0 ≤ u := hu.1
      have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
      positivity

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
