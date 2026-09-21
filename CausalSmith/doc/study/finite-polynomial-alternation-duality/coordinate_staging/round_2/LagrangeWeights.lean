/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Normalized signed Lagrange weights on ordered nodes

This module defines normalized barycentric Lagrange weights for `L+2` real
nodes.  For strictly ordered nodes it records normalization, alternating signs,
and annihilation of every monomial through degree `L`.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- The normalized signed Lagrange weight at a node is its barycentric nodal
weight divided by the sum of the absolute barycentric weights. [the stated inputs](hyp:n,nodes,i) establish [the defined object](goal). -/
noncomputable def normalizedLagrangeWeight {n : ℕ}
    (nodes : Fin n → ℝ) (i : Fin n) : ℝ :=
  Lagrange.nodalWeight Finset.univ nodes i /
    ∑ k : Fin n, |Lagrange.nodalWeight Finset.univ nodes k|

/-- For `L+2` distinct real nodes, the normalized signed Lagrange weights have
total absolute mass one. [the stated inputs](hyp:L,nodes,hnodes) establish [the stated conclusion](goal). -/
theorem sum_abs_normalizedLagrangeWeight_eq_one
    {L : ℕ} {nodes : Fin (L + 2) → ℝ} (hnodes : Function.Injective nodes) :
    ∑ i, |normalizedLagrangeWeight nodes i| = 1 := by
  classical
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hweight : Lagrange.nodalWeight Finset.univ nodes (0 : Fin (L + 2)) ≠ 0 :=
    Lagrange.nodalWeight_ne_zero hnodes.injOn (Finset.mem_univ _)
  have hZ : 0 < Z := by
    apply Finset.sum_pos'
    · exact fun k _ ↦ abs_nonneg _
    · exact ⟨0, Finset.mem_univ _, abs_pos.mpr hweight⟩
  change ∑ i, |Lagrange.nodalWeight Finset.univ nodes i / Z| = 1
  simp_rw [abs_div, abs_of_pos hZ]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt hZ)

/-- For `L+2` strictly increasing real nodes, the normalized Lagrange weight
at index `i` has sign `(-1)^(L+1-i)`. [the stated inputs](hyp:L,nodes,hnodes,i) establish [the stated conclusion](goal). -/
theorem normalizedLagrangeWeight_alternates
    {L : ℕ} {nodes : Fin (L + 2) → ℝ} (hnodes : StrictMono nodes)
    (i : Fin (L + 2)) :
    normalizedLagrangeWeight nodes i =
      (-1 : ℝ) ^ (L + 1 - (i : ℕ)) * |normalizedLagrangeWeight nodes i| := by
  classical
  have hfactor (k : Fin (L + 2))
      (hk : k ∈ (Finset.univ : Finset (Fin (L + 2))).erase i) :
      (nodes i - nodes k)⁻¹ =
        (if i < k then (-1 : ℝ) else 1) * |(nodes i - nodes k)⁻¹| := by
    by_cases hik : i < k
    · rw [if_pos hik, abs_of_neg]
      · ring
      · exact inv_neg''.mpr (sub_neg.mpr (hnodes hik))
    · rw [if_neg hik, one_mul, abs_of_pos]
      have hki : k < i :=
        lt_of_le_of_ne (le_of_not_gt hik) (Finset.ne_of_mem_erase hk)
      exact inv_pos.mpr (sub_pos.mpr (hnodes hki))
  have hsign :
      (∏ k ∈ (Finset.univ : Finset (Fin (L + 2))).erase i,
        if i < k then (-1 : ℝ) else 1) =
          (-1 : ℝ) ^ (L + 1 - (i : ℕ)) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have hfilter :
        ((Finset.univ : Finset (Fin (L + 2))).erase i).filter (fun k ↦ i < k) =
          Finset.Ioi i := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        Finset.mem_Ioi]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨⟨ne_of_gt h, trivial⟩, h⟩
    rw [hfilter, Fin.card_Ioi]
    rw [show L + 2 - 1 - (i : ℕ) = L + 1 - (i : ℕ) by omega]
  have hweight :
      Lagrange.nodalWeight Finset.univ nodes i =
        (-1 : ℝ) ^ (L + 1 - (i : ℕ)) *
          |Lagrange.nodalWeight Finset.univ nodes i| := by
    rw [Lagrange.nodalWeight]
    calc
      (∏ k ∈ Finset.univ.erase i, (nodes i - nodes k)⁻¹) =
          ∏ k ∈ Finset.univ.erase i,
            ((if i < k then (-1 : ℝ) else 1) * |(nodes i - nodes k)⁻¹|) := by
              apply Finset.prod_congr rfl
              intro k hk
              exact hfactor k hk
      _ = (∏ k ∈ Finset.univ.erase i, if i < k then (-1 : ℝ) else 1) *
          (∏ k ∈ Finset.univ.erase i, |(nodes i - nodes k)⁻¹|) := by
            rw [Finset.prod_mul_distrib]
      _ = (-1 : ℝ) ^ (L + 1 - (i : ℕ)) *
          |∏ k ∈ Finset.univ.erase i, (nodes i - nodes k)⁻¹| := by
            rw [hsign, Finset.abs_prod]
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hnodeInjective : Function.Injective nodes := hnodes.injective
  have hweight_ne : Lagrange.nodalWeight Finset.univ nodes i ≠ 0 :=
    Lagrange.nodalWeight_ne_zero hnodeInjective.injOn (Finset.mem_univ _)
  have hZ : 0 < Z := by
    apply Finset.sum_pos'
    · exact fun k _ ↦ abs_nonneg _
    · exact ⟨i, Finset.mem_univ _, abs_pos.mpr hweight_ne⟩
  change Lagrange.nodalWeight Finset.univ nodes i / Z =
    (-1 : ℝ) ^ (L + 1 - (i : ℕ)) *
      |Lagrange.nodalWeight Finset.univ nodes i / Z|
  rw [abs_div, abs_of_pos hZ]
  nth_rewrite 1 [hweight]
  ring

/-- For `L+2` distinct real nodes, the normalized signed Lagrange weights
annihilate the monomial `x^j` whenever `j ≤ L`. [the stated inputs](hyp:L,j,nodes,hnodes,hj) establish [the stated conclusion](goal). -/
theorem sum_normalizedLagrangeWeight_mul_pow_eq_zero
    {L j : ℕ} {nodes : Fin (L + 2) → ℝ}
    (hnodes : Function.Injective nodes) (hj : j ≤ L) :
    ∑ i, normalizedLagrangeWeight nodes i * nodes i ^ j = 0 := by
  classical
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hdegree : (X ^ j : Polynomial ℝ).degree <
      (Finset.univ : Finset (Fin (L + 2))).card := by
    rw [degree_X_pow]
    norm_cast
    simpa using (show j < L + 2 by omega)
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (L + 2)))) (v := nodes)
    hnodes.injOn (P := (X ^ j : Polynomial ℝ)) hdegree
  have hsum : ∑ i : Fin (L + 2),
      Lagrange.nodalWeight Finset.univ nodes i * nodes i ^ j = 0 := by
    simpa [Lagrange.nodalWeight, div_eq_mul_inv, Finset.prod_inv_distrib,
      mul_comm, ne_of_gt (lt_of_le_of_lt hj (Nat.lt_succ_self L))] using hcoeff.symm
  change ∑ i : Fin (L + 2),
    (Lagrange.nodalWeight Finset.univ nodes i / Z) * nodes i ^ j = 0
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum, zero_mul]

/-- For `L+2` distinct real nodes, the normalized signed Lagrange weights
annihilate the values of every real polynomial of degree at most `L`. [the stated inputs](hyp:L,nodes,hnodes,Q,hQ) establish [the stated conclusion](goal). -/
theorem sum_normalizedLagrangeWeight_mul_eval_eq_zero
    {L : ℕ} {nodes : Fin (L + 2) → ℝ}
    (hnodes : Function.Injective nodes) {Q : Polynomial ℝ}
    (hQ : Q.natDegree ≤ L) :
    ∑ i, normalizedLagrangeWeight nodes i * Q.eval (nodes i) = 0 := by
  classical
  let Z := ∑ k : Fin (L + 2), |Lagrange.nodalWeight Finset.univ nodes k|
  have hdegree : Q.degree < (Finset.univ : Finset (Fin (L + 2))).card := by
    apply lt_of_le_of_lt Q.degree_le_natDegree
    norm_cast
    simpa using (show Q.natDegree < L + 2 by omega)
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (L + 2)))) (v := nodes)
    hnodes.injOn (P := Q) hdegree
  have hcoeffzero : Q.coeff (L + 1) = 0 :=
    Q.coeff_eq_zero_of_natDegree_lt (by omega)
  have hsum : ∑ i : Fin (L + 2),
      Lagrange.nodalWeight Finset.univ nodes i * Q.eval (nodes i) = 0 := by
    simpa [Lagrange.nodalWeight, div_eq_mul_inv, Finset.prod_inv_distrib,
      mul_comm, hcoeffzero] using hcoeff.symm
  change ∑ i : Fin (L + 2),
    (Lagrange.nodalWeight Finset.univ nodes i / Z) * Q.eval (nodes i) = 0
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum, zero_mul]

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
