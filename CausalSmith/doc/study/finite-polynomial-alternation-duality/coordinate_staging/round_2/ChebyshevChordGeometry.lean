/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.CenteredRemainder
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevChordFactorization
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevChordOrdering
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevChordPermutation

/-!
# Finite chord geometry for Chebyshev roots

This module isolates the trigonometric geometry in the Duffin--Schaeffer
vertical-modulus argument.  The purely finite rearrangement inequality lives
in `PairingRearrangement`; here it is applied to chord squares between roots
of unity.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- Given [a positive degree](hyp:L,hL), [a point of the unit interval](hyp:x,hx),
and [a real height](hyp:y), [some abscissa in that interval, weakly to the
right of all degree-`L` Chebyshev roots, has at least as large a vertical
root-distance product](goal).

The proof uses `x = cos θ` and reduces `θ` modulo `π / L` to a centered
angle `φ`.  The `2L` chord squares for `θ` and `φ` are permutations of one
another.  At the centered angle the root pairing is the adjacent pairing of
the decreasing chord squares, so
`adjacentPairProduct_le_of_perm_sorted` gives product domination.  Finally
`|φ| ≤ π / (2L)` places `cos φ` to the right of the largest root.

The imported helper modules isolate centered remainder selection, cyclic
chord permutation, centered adjacent ordering, and conversion from chord-pair
products to complex root distances. -/
theorem exists_rootProduct_dominating_abscissa_past_chebyshevZeros
    {L : ℕ} (hL : 0 < L) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) (y : ℝ) :
    ∃ x₀ ∈ Set.Icc (-1 : ℝ) 1,
      (∀ k ∈ Finset.range L, chebyshevZero L k ≤ x₀) ∧
        (∏ k ∈ Finset.range L,
            ‖((x - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ≤
          ∏ k ∈ Finset.range L,
            ‖((x₀ - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
  let θ := Real.arccos x
  rcases exists_int_abs_sub_mul_pi_div_le hL θ with ⟨m, hm⟩
  let φ := θ - (m : ℝ) * (Real.pi / (L : ℝ))
  have hφ : |φ| ≤ Real.pi / (2 * (L : ℝ)) := by
    simpa [φ] using hm
  have hshift : φ + (m : ℝ) * (Real.pi / (L : ℝ)) = θ := by
    dsimp [φ]
    ring
  have hpermθφ :
      (chebyshevPairedChordList L θ).Perm
        (chebyshevPairedChordList L φ) := by
    rw [← hshift]
    exact chebyshevPairedChordList_add_int_mul_pi_div_perm hL φ m
  rcases
      exists_sorted_chebyshevChordList_with_adjacentPairProduct_eq_of_centered
        (t := 4 * y ^ 2) hL hφ with
    ⟨zs, hzsperm, hzssorted, hzsprod⟩
  have hlen : (chebyshevPairedChordList L φ).length = 2 * L := by
    simp [chebyshevPairedChordList, Nat.mul_comm]
  have hzseven : Even zs.length := by
    rw [hzsperm.length_eq, hlen]
    exact ⟨L, by omega⟩
  have hchord_nonneg (a : ℝ) : 0 ≤ cosineChordSq a := by
    unfold cosineChordSq
    nlinarith [Real.cos_le_one a]
  have hzsnonneg : ∀ a ∈ zs, 0 ≤ a := by
    intro a ha
    have ha' : a ∈ chebyshevPairedChordList L φ := hzsperm.mem_iff.mp ha
    simp only [chebyshevPairedChordList, List.mem_flatMap,
      Multiset.mem_toList, Finset.mem_val, Finset.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with ⟨k, hk, rfl | rfl⟩
    · exact hchord_nonneg _
    · exact hchord_nonneg _
  have hadj :
      adjacentPairProduct (4 * y ^ 2) (chebyshevPairedChordList L θ) ≤
        adjacentPairProduct (4 * y ^ 2) (chebyshevPairedChordList L φ) := by
    have h := adjacentPairProduct_le_of_perm_sorted
      (t := 4 * y ^ 2) (xs := zs)
      (ys := chebyshevPairedChordList L θ)
      (by positivity) hzseven hzssorted hzsnonneg
      (hpermθφ.trans hzsperm.symm)
    simpa [hzsprod] using h
  have hcosθ : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos hx.1 hx.2
  let A : ℝ := ∏ k ∈ Finset.range L,
    ‖((x - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖
  let B : ℝ := ∏ k ∈ Finset.range L,
    ‖((Real.cos φ - chebyshevZero L k : ℝ) : ℂ) +
      (y : ℂ) * Complex.I‖
  have hfactor (u : ℕ → ℝ) :
      (∏ k ∈ Finset.range L, 4 * u k ^ 2) =
        4 ^ L * (∏ k ∈ Finset.range L, u k) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
    simp
  have hsquares : 4 ^ L * A ^ 2 ≤ 4 ^ L * B ^ 2 := by
    rw [adjacentPairProduct_chebyshevPairedChordList,
      adjacentPairProduct_chebyshevPairedChordList] at hadj
    simpa [A, B, hcosθ, hfactor] using hadj
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hAB : A ≤ B := by
    have hfour : 0 < (4 : ℝ) ^ L := pow_pos (by norm_num) L
    have hsq : A ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_left hsquares hfour
    exact (sq_le_sq₀ hA hB).mp hsq
  refine ⟨Real.cos φ, ⟨Real.neg_one_le_cos φ, Real.cos_le_one φ⟩, ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_range] at hk
    have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
    have hkr : (k : ℝ) ≤ (L : ℝ) - 1 := by
      have : k + 1 ≤ L := by omega
      have hkr' : (k : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast this
      linarith
    have hcoef : (((2 * k + 1 : ℕ) : ℝ)) = 2 * (k : ℝ) + 1 := by
      push_cast
      ring
    have hangle0 : 0 ≤ chebyshevRootAngle L k := by
      rw [chebyshevRootAngle]
      positivity
    have hanglepi : chebyshevRootAngle L k ≤ Real.pi := by
      rw [chebyshevRootAngle]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      rw [hcoef]
      field_simp
      nlinarith [Real.pi_pos]
    have hφangle : |φ| ≤ chebyshevRootAngle L k := by
      apply hφ.trans
      rw [chebyshevRootAngle]
      rw [hcoef]
      field_simp
      nlinarith [Real.pi_pos]
    rw [chebyshevZero, ← Real.cos_abs φ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) hanglepi hφangle
  · simpa [A, B] using hAB

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
