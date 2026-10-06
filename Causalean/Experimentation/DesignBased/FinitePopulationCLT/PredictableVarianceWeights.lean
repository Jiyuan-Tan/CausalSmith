/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVarianceMoments
public import Mathlib.Analysis.PSeries

/-!
# Weighted predictable-variance estimates

This module proves the two weighted prefix-moment estimates in Hájek’s predictable-variance
argument. The bounds are uniform in the allocation fraction by working through the smaller arm.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open FinitePopulationMoments
open ProbabilityTheory

private lemma sum_inv_sq (K L : ℕ) (hL : 0 < L) :
    (∑ j ∈ Finset.range K, (1 : ℝ) / ((L + j : ℕ) : ℝ) ^ 2) ≤
      2 / (L : ℝ) := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) (L - 1) (L + K)
  have hsets : Finset.Ioo (L - 1) (L + K) = Finset.Ico L (L + K) := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [hsets, Finset.sum_Ico_eq_sum_range] at h
  have hLK : L + K - L = K := by omega
  have hLm : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hL
  rw [hLK, hLm] at h
  simpa only [one_div] using h

private lemma sum_remaining_inv_sq (N K : ℕ) (hK : K < N) :
    (∑ k ∈ Finset.range K, (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) ≤
      2 / ((N - K : ℕ) : ℝ) := by
  let L := N - K
  have hL : 0 < L := Nat.sub_pos_of_lt hK
  calc
    (∑ k ∈ Finset.range K, (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) =
        ∑ k ∈ Finset.range K,
          (1 : ℝ) / ((L + (K - 1 - k) : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      congr 3
      dsimp only [L]
      omega
    _ = ∑ j ∈ Finset.range K, (1 : ℝ) / ((L + j : ℕ) : ℝ) ^ 2 := by
      exact Finset.sum_range_reflect (fun j =>
        (1 : ℝ) / ((L + j : ℕ) : ℝ) ^ 2) K
    _ ≤ 2 / (L : ℝ) := sum_inv_sq K L hL

private lemma second_weight (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N) :
    (((N - K : ℕ) : ℝ) / (K : ℝ)) *
        (∑ k ∈ Finset.range K,
          (k : ℝ) / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
      2 / ((N - K : ℕ) : ℝ) := by
  let L := N - K
  have hL : 0 < L := Nat.sub_pos_of_lt hKlt
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum :
      (∑ k ∈ Finset.range K,
          (k : ℝ) / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
        ((K : ℝ) / (L : ℝ)) *
          (∑ k ∈ Finset.range K, (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hkKN : k < N := hk'.trans hKlt
    have hR : L ≤ N - k := by
      dsimp only [L]
      omega
    have hRpos : (0 : ℝ) < (N - k : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt hkKN
    have hratio : (k : ℝ) / (N - k : ℕ) ≤ (K : ℝ) / L := by
      exact div_le_div₀ (by positivity)
        (show (k : ℝ) ≤ K by exact_mod_cast hk'.le) hLR
        (show (L : ℝ) ≤ (N - k : ℕ) by exact_mod_cast hR)
    have hsq0 : 0 ≤ (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2 := by positivity
    calc
      (k : ℝ) / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) =
          ((k : ℝ) / (N - k : ℕ)) *
            ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ ((K : ℝ) / L) * ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hratio hsq0
  have hden := sum_remaining_inv_sq N K hKlt
  calc
    ((L : ℝ) / (K : ℝ)) *
        (∑ k ∈ Finset.range K,
          (k : ℝ) / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
        ((L : ℝ) / (K : ℝ)) * (((K : ℝ) / L) *
          (∑ k ∈ Finset.range K, (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ∑ k ∈ Finset.range K, (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2 := by
      field_simp [ne_of_gt hKR, ne_of_gt hLR]
    _ ≤ 2 / (L : ℝ) := hden

private lemma first_weight_left (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (M v : ℝ) (hM : 0 ≤ M) (hv : 0 ≤ v) :
    (∑ k ∈ Finset.range K,
        Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
      (Real.sqrt ((K : ℝ) * M * v) / ((N - K : ℕ) : ℝ)) *
        (2 / ((N - K : ℕ) : ℝ)) := by
  let L := N - K
  have hL : 0 < L := Nat.sub_pos_of_lt hKlt
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hNR : (0 : ℝ) < N := by exact_mod_cast hKpos.trans hKlt
  have hpoint : ∀ k ∈ Finset.range K,
      Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) ≤
        (Real.sqrt ((K : ℝ) * M * v) / (L : ℝ)) *
          ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hkN : k < N := hk'.trans hKlt
    have hRnat : L ≤ N - k := by
      dsimp only [L]
      omega
    have hRnat' : L + 1 ≤ N - k := by
      dsimp only [L]
      omega
    have hR : (0 : ℝ) < (N - k : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt hkN
    have hRm1 : (0 : ℝ) < (N - k - 1 : ℕ) := by
      exact_mod_cast (by omega : 0 < N - k - 1)
    have hkR : (0 : ℝ) ≤ k := by positivity
    have hfrac : (k : ℝ) * (N - k : ℕ) / (N : ℝ) ≤ K := by
      have hRN : ((N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N k
      have hdiv : ((N - k : ℕ) : ℝ) / N ≤ 1 := (div_le_one hNR).2 hRN
      calc
        (k : ℝ) * (N - k : ℕ) / (N : ℝ) =
            (k : ℝ) * (((N - k : ℕ) : ℝ) / N) := by ring
        _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv hkR
        _ ≤ K := by simpa using (show (k : ℝ) ≤ K by exact_mod_cast hk'.le)
    have hsqrt : Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) ≤
        Real.sqrt ((K : ℝ) * M * v) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfrac hM) hv
    have hinvR : (1 : ℝ) / (N - k : ℕ) ≤ 1 / L := by
      exact one_div_le_one_div_of_le hLR (by exact_mod_cast hRnat)
    have hsq0 : 0 ≤ (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2 := by positivity
    calc
      Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) =
          (Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) *
            ((1 : ℝ) / (N - k : ℕ))) *
              ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ (Real.sqrt ((K : ℝ) * M * v) * ((1 : ℝ) / L)) *
              ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hsq0
        exact mul_le_mul hsqrt hinvR (by positivity) (by positivity)
      _ = (Real.sqrt ((K : ℝ) * M * v) / (L : ℝ)) *
          ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by ring
  calc
    (∑ k ∈ Finset.range K,
        Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ k ∈ Finset.range K,
          (Real.sqrt ((K : ℝ) * M * v) / (L : ℝ)) *
            ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = (Real.sqrt ((K : ℝ) * M * v) / (L : ℝ)) *
        (∑ k ∈ Finset.range K,
          (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (Real.sqrt ((K : ℝ) * M * v) / (L : ℝ)) * (2 / (L : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_remaining_inv_sq N K hKlt) (by positivity)

private lemma first_weight_right (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (M v : ℝ) (hM : 0 ≤ M) (hv : 0 ≤ v) :
    (∑ k ∈ Finset.range K,
        Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
      Real.sqrt (M * v / ((N - K : ℕ) : ℝ)) *
        (2 / ((N - K : ℕ) : ℝ)) := by
  let L := N - K
  have hL : 0 < L := Nat.sub_pos_of_lt hKlt
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hNR : (0 : ℝ) < N := by exact_mod_cast hKpos.trans hKlt
  have hMv0 : 0 ≤ M * v := mul_nonneg hM hv
  have hpoint : ∀ k ∈ Finset.range K,
      Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) ≤
        Real.sqrt (M * v / (L : ℝ)) *
          ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hkN : k < N := hk'.trans hKlt
    have hRnat : L ≤ N - k := by
      dsimp only [L]
      omega
    have hRnat' : L + 1 ≤ N - k := by
      dsimp only [L]
      omega
    have hR : (0 : ℝ) < (N - k : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt hkN
    have hRm1 : (0 : ℝ) < (N - k - 1 : ℕ) := by
      exact_mod_cast (by omega : 0 < N - k - 1)
    have hkNdiv : (k : ℝ) / N ≤ 1 := by
      exact (div_le_one hNR).2 (by exact_mod_cast hkN.le)
    have hinside0 : 0 ≤ (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) := by
      positivity
    have hrootDiv :
        Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
            ((N - k : ℕ) : ℝ) ≤ Real.sqrt (M * v / (L : ℝ)) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, Real.sq_sqrt hinside0]
      have hRinv : (1 : ℝ) / (N - k : ℕ) ≤ 1 / L :=
        one_div_le_one_div_of_le hLR (by exact_mod_cast hRnat)
      calc
        (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
            ((N - k : ℕ) : ℝ) ^ 2 =
            ((k : ℝ) / N) * (M * v) * ((1 : ℝ) / (N - k : ℕ)) := by
          field_simp [ne_of_gt hR, ne_of_gt hNR]
        _ ≤ 1 * (M * v) * ((1 : ℝ) / (N - k : ℕ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hkNdiv hMv0) (one_div_nonneg.mpr hR.le)
        _ ≤ 1 * (M * v) * ((1 : ℝ) / L) :=
          mul_le_mul_of_nonneg_left hRinv (by simpa using hMv0)
        _ = M * v / (L : ℝ) := by ring
    have hsq0 : 0 ≤ (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2 := by positivity
    calc
      Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) =
          (Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
            ((N - k : ℕ) : ℝ)) *
              ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ Real.sqrt (M * v / (L : ℝ)) *
              ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hrootDiv hsq0
  calc
    (∑ k ∈ Finset.range K,
        Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ k ∈ Finset.range K, Real.sqrt (M * v / (L : ℝ)) *
          ((1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = Real.sqrt (M * v / (L : ℝ)) *
        (∑ k ∈ Finset.range K,
          (1 : ℝ) / ((N - k - 1 : ℕ) : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (M * v / (L : ℝ)) * (2 / (L : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_remaining_inv_sq N K hKlt) (by positivity)

private lemma first_weight (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (M v : ℝ) (hM : 0 ≤ M) (hv : 0 < v) :
    ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * v)) *
        (∑ k ∈ Finset.range K,
          Real.sqrt (((k : ℝ) * (N - k : ℕ) / (N : ℝ)) * M * v) /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
      4 * Real.sqrt (M / (((min K (N - K) : ℕ) : ℝ) * v)) := by
  let L := N - K
  have hL : 0 < L := Nat.sub_pos_of_lt hKlt
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hNR : (0 : ℝ) < N := by exact_mod_cast hKpos.trans hKlt
  have hscale0 : 0 ≤ ((L : ℝ) * (N : ℝ)) / ((K : ℝ) * v) := by positivity
  by_cases hKL : K ≤ L
  · have hraw := first_weight_left N K hKpos hKlt M v hM hv.le
    have hmin : min K L = K := min_eq_left hKL
    rw [hmin]
    refine (mul_le_mul_of_nonneg_left hraw hscale0).trans ?_
    let x := (((L : ℝ) * (N : ℝ)) / ((K : ℝ) * v)) *
      ((Real.sqrt ((K : ℝ) * M * v) / (L : ℝ)) * (2 / (L : ℝ)))
    let q := M / ((K : ℝ) * v)
    have hq : 0 ≤ q := div_nonneg hM (mul_pos hKR hv).le
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hrhs : 0 ≤ 4 * Real.sqrt q := by positivity
    apply (sq_le_sq₀ hx hrhs).mp
    have hsqrt : (Real.sqrt ((K : ℝ) * M * v)) ^ 2 = (K : ℝ) * M * v := by
      rw [Real.sq_sqrt]
      positivity
    have hNle : (N : ℝ) ≤ 2 * L := by
      have hsum : N = K + L := by dsimp only [L]; omega
      exact_mod_cast (by omega : N ≤ 2 * L)
    have hN2 : (N : ℝ) ^ 2 ≤ (2 * L) ^ 2 := by nlinarith
    dsimp only [x, q]
    simp only [mul_pow]
    rw [
      show (Real.sqrt (M / ((K : ℝ) * v))) ^ 2 = M / ((K : ℝ) * v) from
        Real.sq_sqrt hq]
    field_simp [ne_of_gt hKR, ne_of_gt hLR, ne_of_gt hv]
    have hsqrt' : (Real.sqrt ((K : ℝ) * v * M)) ^ 2 = (K : ℝ) * v * M := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [hN2, hsqrt']
  · have hLK : L < K := lt_of_not_ge hKL
    have hraw := first_weight_right N K hKpos hKlt M v hM hv.le
    have hmin : min K L = L := min_eq_right hLK.le
    rw [hmin]
    refine (mul_le_mul_of_nonneg_left hraw hscale0).trans ?_
    let x := (((L : ℝ) * (N : ℝ)) / ((K : ℝ) * v)) *
      (Real.sqrt (M * v / (L : ℝ)) * (2 / (L : ℝ)))
    let q := M / ((L : ℝ) * v)
    have hq : 0 ≤ q := div_nonneg hM (mul_pos hLR hv).le
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hrhs : 0 ≤ 4 * Real.sqrt q := by positivity
    apply (sq_le_sq₀ hx hrhs).mp
    have hinside : 0 ≤ M * v / (L : ℝ) := by positivity
    have hsqrt : (Real.sqrt (M * v / (L : ℝ))) ^ 2 = M * v / (L : ℝ) :=
      Real.sq_sqrt hinside
    have hNle : (N : ℝ) ≤ 2 * K := by
      have hsum : N = K + L := by dsimp only [L]; omega
      exact_mod_cast (by omega : N ≤ 2 * K)
    have hN2 : (N : ℝ) ^ 2 ≤ (2 * K) ^ 2 := by nlinarith
    dsimp only [x, q]
    simp only [mul_pow]
    rw [
      show (Real.sqrt (M / ((L : ℝ) * v))) ^ 2 = M / ((L : ℝ) * v) from
        Real.sq_sqrt hq]
    field_simp [ne_of_gt hKR, ne_of_gt hLR, ne_of_gt hv]
    have hsqrt' : (Real.sqrt (v * M / (L : ℝ))) ^ 2 = v * M / (L : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    rw [hsqrt'] at *
    field_simp [ne_of_gt hLR] at *
    nlinarith [hN2]

private lemma sum_range_sub_succ (K : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range K, (f j - f (j + 1))) = f 0 - f K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private lemma sum_inv_product (N K : ℕ) (hKlt : K < N) :
    (∑ k ∈ Finset.range K,
      (1 : ℝ) / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ))) =
      (K : ℝ) / (((N - K : ℕ) : ℝ) * (N : ℝ)) := by
  let L := N - K
  have hL : 0 < L := Nat.sub_pos_of_lt hKlt
  calc
    (∑ k ∈ Finset.range K,
      (1 : ℝ) / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range K,
          (1 : ℝ) / (((L + (K - 1 - k) + 1 : ℕ) : ℝ) *
            ((L + (K - 1 - k) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      congr 4 <;> dsimp only [L] <;> omega
    _ =
        ∑ j ∈ Finset.range K,
          (1 : ℝ) / (((L + j + 1 : ℕ) : ℝ) * ((L + j : ℕ) : ℝ)) := by
      exact Finset.sum_range_reflect (fun j =>
        (1 : ℝ) / (((L + j + 1 : ℕ) : ℝ) * ((L + j : ℕ) : ℝ))) K
    _ = ∑ j ∈ Finset.range K,
        ((1 : ℝ) / ((L + j : ℕ) : ℝ) -
          1 / ((L + j + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hLj : (0 : ℝ) < (L + j : ℕ) := by positivity
      have hLjs : (0 : ℝ) < (L + j + 1 : ℕ) := by positivity
      field_simp [ne_of_gt hLj, ne_of_gt hLjs]
      norm_num
    _ = (1 : ℝ) / (L : ℝ) - 1 / ((L + K : ℕ) : ℝ) := by
      simpa only [Nat.add_zero, Nat.add_assoc] using sum_range_sub_succ K
        (fun j => (1 : ℝ) / ((L + j : ℕ) : ℝ))
    _ = (K : ℝ) / ((L : ℝ) * (N : ℝ)) := by
      have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hKlt).ne'
      have hsum : L + K = N := by dsimp only [L]; omega
      rw [hsum]
      have hcast : (N : ℝ) = (L : ℝ) + K := by exact_mod_cast hsum.symm
      field_simp [hLR, hNR]
      linarith

/-- Given [a population size](hyp:N), [a positive proper sample size](hyp:K,hKpos,hKlt),
and [a positive finite-population variance](hyp:v,hv), [the deterministic mean terms in the
standardized predictable-variance expansion sum exactly to one](goal). -/
lemma predictableVariance_deterministicBaseline (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (v : ℝ) (hv : 0 < v) :
    ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * v)) *
      (∑ k ∈ Finset.range K,
        ((((N - 1 : ℕ) : ℝ) * v -
              (k : ℝ) * (((N - 1 : ℕ) : ℝ) * v) / (N : ℝ)) /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) -
          (((k : ℕ) : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * v) /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2))) = 1 := by
  have hterm : ∀ k ∈ Finset.range K,
      ((((N - 1 : ℕ) : ℝ) * v -
            (k : ℝ) * (((N - 1 : ℕ) : ℝ) * v) / (N : ℝ)) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) -
        (((k : ℕ) : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * v) /
          (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)) =
        v / (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (hKpos.trans hKlt).ne'
    have hR : ((N - k : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt (hk'.trans hKlt)).ne'
    have hRmNat : 0 < N - k - 1 := by
      rw [Nat.sub_sub]
      exact Nat.sub_pos_of_lt ((Nat.succ_le_iff.mpr hk').trans_lt hKlt)
    have hRm : ((N - k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hRmNat.ne'
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    have hcastR : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) :=
      Nat.cast_sub (hk'.trans hKlt).le
    have hcastRm : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N - k), hcastR]
      norm_num
    rw [hcastR, hcastRm]
    have hR' : (N : ℝ) - (k : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt (hk'.trans hKlt)))
    have hRm' : (N : ℝ) - (k : ℝ) - 1 ≠ 0 := by
      have hksNR : (k : ℝ) + 1 < N := by exact_mod_cast
        ((Nat.succ_le_iff.mpr hk').trans_lt hKlt)
      linarith
    field_simp [hNR, hR', hRm']
    ring
  rw [Finset.sum_congr rfl hterm]
  simp_rw [div_eq_mul_inv v]
  rw [← Finset.mul_sum]
  rw [show (∑ i ∈ Finset.range K,
      (((N - i : ℕ) : ℝ) * ((N - i - 1 : ℕ) : ℝ))⁻¹) =
      (K : ℝ) / (((N - K : ℕ) : ℝ) * (N : ℝ)) by
    simpa only [one_div] using sum_inv_product N K hKlt]
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hLR : ((N - K : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hKlt).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (hKpos.trans hKlt).ne'
  field_simp [hKR, hLR, hNR, hv.ne']

/-- Given [a population size](hyp:N), [a positive proper sample size](hyp:K,hKpos,hKlt),
[population outcomes](hyp:y), and [their positive variance](hyp:hvar), [the weighted expected
absolute fluctuations of the revealed centered-square sums are bounded by four times the square
root of the Li–Ding maximal-deviation sufficient-condition ratio](goal). -/
lemma predictableVariance_firstWeightedEstimate {N : ℕ} [Nonempty (Fin N)]
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (hvar : 0 < popVar y) :
    ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)) *
      (∑ k ∈ Finset.range K,
        (∫ π, |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) (min k N)
              (min_le_right k N) π -
            (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)|
            ∂(uniformPermutationDesign N).toMeasure) /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
      4 * Real.sqrt (popMaxSqDev y /
        (((min K (N - K) : ℕ) : ℝ) * popVar y)) := by
  have hN : 2 ≤ N := by omega
  have hM : 0 ≤ popMaxSqDev y := by
    let i : Fin N := Classical.choice (inferInstance : Nonempty (Fin N))
    exact (sq_nonneg (y i - popMean y)).trans (by
      unfold popMaxSqDev
      exact Finset.le_sup' (fun j : Fin N => (y j - popMean y) ^ 2) (Finset.mem_univ i))
  have hscale : 0 ≤ (((N - K : ℕ) : ℝ) * (N : ℝ)) /
      ((K : ℝ) * popVar y) := by positivity
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk ↦ ?_) hscale).trans
    (first_weight N K hKpos hKlt (popMaxSqDev y) (popVar y) hM hvar)
  have hk' := Finset.mem_range.mp hk
  have hmink : min k N = k := min_eq_left (hk'.le.trans hKlt.le)
  simp only [hmink]
  have hden : 0 ≤ (((N - k : ℕ) : ℝ) *
      ((N - k - 1 : ℕ) : ℝ) ^ 2) := by positivity
  apply div_le_div_of_nonneg_right _ hden
  by_cases hk0 : k = 0
  · subst k
    simp [permutationRevealedSum]
  · exact integral_abs_centeredSq_revealedSum_le y k (hk'.le.trans hKlt.le)
      (Nat.pos_of_ne_zero hk0) hN

/-- Given [a population size](hyp:N), [a positive proper sample size](hyp:K,hKpos,hKlt),
[population outcomes](hyp:y), and [their positive variance](hyp:hvar), [the weighted expected
squares of the centered revealed sums are at most twice the inverse complementary-arm
size](goal). -/
lemma predictableVariance_secondWeightedEstimate {N : ℕ} [Nonempty (Fin N)]
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (hvar : 0 < popVar y) :
    ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)) *
      (∑ k ∈ Finset.range K,
        (∫ π, (permutationRevealedSum (fun i => y i - popMean y) (min k N)
              (min_le_right k N) π) ^ 2
            ∂(uniformPermutationDesign N).toMeasure) /
          (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)) ≤
      2 / ((N - K : ℕ) : ℝ) := by
  have hN : 2 ≤ N := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hKpos.trans hKlt
  have hvR : popVar y ≠ 0 := hvar.ne'
  have heq :
      ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)) *
        (∑ k ∈ Finset.range K,
          (∫ π, (permutationRevealedSum (fun i => y i - popMean y) (min k N)
                (min_le_right k N) π) ^ 2
              ∂(uniformPermutationDesign N).toMeasure) /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)) =
        (((N - K : ℕ) : ℝ) / (K : ℝ)) *
          (∑ k ∈ Finset.range K,
            (k : ℝ) / (((N - k : ℕ) : ℝ) *
              ((N - k - 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hmink : min k N = k := min_eq_left (hk'.le.trans hKlt.le)
    simp only [hmink]
    by_cases hk0 : k = 0
    · subst k
      simp [permutationRevealedSum]
    · rw [integral_centered_revealedSum_sq y k (hk'.le.trans hKlt.le)
          (Nat.pos_of_ne_zero hk0) hN]
      have hR : (0 : ℝ) < (N - k : ℕ) := by
        exact_mod_cast Nat.sub_pos_of_lt (hk'.trans hKlt)
      have hRm : (0 : ℝ) < (N - k - 1 : ℕ) := by
        have hksN : k + 1 < N := (Nat.succ_le_iff.mpr hk').trans_lt hKlt
        rw [Nat.sub_sub]
        exact_mod_cast Nat.sub_pos_of_lt hksN
      field_simp [ne_of_gt hKR, ne_of_gt hNR, ne_of_gt hR, ne_of_gt hRm, hvR]
      rw [Nat.cast_sub (hk'.trans hKlt).le]
  rw [heq]
  exact second_weight N K hKpos hKlt


end Causalean.Experimentation.DesignBased
