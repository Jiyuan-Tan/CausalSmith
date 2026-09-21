/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PairingRearrangement
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.List.FinRange

/-!
# Finite chord geometry for Chebyshev roots

This module centers angles on the odd Chebyshev grid, proves the grid's cyclic
symmetry and adjacent ordering, and derives the root-product domination used in
the vertical-modulus argument.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Centered angular remainders -/


/-- [Every real angle](hyp:θ) differs from an integer multiple of the step determined by
[a positive integer](hyp:L,hL) by [at most half of that step](goal). -/
theorem exists_int_abs_sub_mul_pi_div_le
    {L : ℕ} (hL : 0 < L) (θ : ℝ) :
    ∃ m : ℤ,
      |θ - (m : ℝ) * (Real.pi / (L : ℝ))| ≤
        Real.pi / (2 * (L : ℝ)) := by
  -- Choose the nearest integer to `θ / (π/L)`. Mathlib's floor/round
  -- bounds give a remainder in `[-1/2,1/2]`; positivity of `π/L` then
  -- rescales that bound to the displayed interval.
  let d : ℝ := Real.pi / (L : ℝ)
  have hd : 0 < d := div_pos Real.pi_pos (by exact_mod_cast hL)
  refine ⟨round (θ / d), ?_⟩
  have hr : |θ / d - (round (θ / d) : ℝ)| ≤ (1 : ℝ) / 2 :=
    abs_sub_round (θ / d)
  have heq :
      θ - (round (θ / d) : ℝ) * d =
        d * (θ / d - (round (θ / d) : ℝ)) := by
    field_simp
  rw [show Real.pi / (L : ℝ) = d by rfl, heq, abs_mul, abs_of_pos hd]
  calc
    d * |θ / d - (round (θ / d) : ℝ)| ≤ d * ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hr hd.le
    _ = Real.pi / (2 * (L : ℝ)) := by
      dsimp [d]
      field_simp

/-! ## Cyclic symmetry of the chord grid -/


private noncomputable def chebyshevChordGridEntry
    (L : ℕ) (θ : ℝ) (j : ℕ) : ℝ :=
  cosineChordSq
    (θ + ((((2 * j + 1 : ℕ) : ℝ) * Real.pi) / (2 * (L : ℝ))))

private theorem chebyshevSignedIndexList_perm (L : ℕ) :
    ((List.range L).flatMap fun k => [k, L + (L - 1 - k)]).Perm
      (List.range (2 * L)) := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 ?_
  · rw [List.nodup_flatMap]
    constructor
    · intro k hk
      simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]
      simp only [List.mem_range] at hk
      exact Nat.ne_of_lt (lt_of_lt_of_le hk (Nat.le_add_right L _))
    · refine List.pairwise_lt_range.imp_of_mem ?_
      intro a b ha hb hab
      unfold Function.onFun
      rw [List.disjoint_iff_ne]
      intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      simp only [List.mem_range] at ha hb
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · omega
      · exact Nat.ne_of_lt (lt_of_lt_of_le ha (Nat.le_add_right L _))
      · exact (Nat.ne_of_lt (lt_of_lt_of_le hb (Nat.le_add_right L _))).symm
      · omega
  intro x
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨k, hk, rfl | rfl⟩ <;> omega
  · intro hx
    by_cases h : x < L
    · exact ⟨x, h, Or.inl rfl⟩
    · refine ⟨L - 1 - (x - L), ?_, Or.inr ?_⟩ <;> omega

private theorem chebyshevChordGridEntry_reverse
    {L k : ℕ} (hL : 0 < L) (hk : k < L) (θ : ℝ) :
    chebyshevChordGridEntry L θ (L + (L - 1 - k)) =
      cosineChordSq (θ - chebyshevRootAngle L k) := by
  have hid : 2 * (L + (L - 1 - k)) + 1 + (2 * k + 1) = 4 * L := by omega
  have hidR :
      ((2 * (L + (L - 1 - k)) + 1 : ℕ) : ℝ) +
        ((2 * k + 1 : ℕ) : ℝ) = 4 * (L : ℝ) := by
    exact_mod_cast hid
  push_cast at hidR
  unfold chebyshevChordGridEntry cosineChordSq
  congr 2
  rw [show
    θ + ((((2 * (L + (L - 1 - k)) + 1 : ℕ) : ℝ) * Real.pi) /
        (2 * (L : ℝ))) =
      (θ - chebyshevRootAngle L k) + (1 : ℤ) * (2 * Real.pi) by
        rw [chebyshevRootAngle]
        norm_num
        field_simp
        linear_combination Real.pi * hidR]
  exact Real.cos_add_int_mul_two_pi _ 1

private theorem chebyshevPairedChordList_perm_grid
    {L : ℕ} (hL : 0 < L) (θ : ℝ) :
    (chebyshevPairedChordList L θ).Perm
      ((List.range (2 * L)).map (chebyshevChordGridEntry L θ)) := by
  have hrange :
      (Finset.range L).val.toList.Perm (List.range L) := by
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 ?_
    · rw [← Multiset.coe_nodup, Multiset.coe_toList]
      exact (Finset.range L).nodup
    · simp
  rw [chebyshevPairedChordList]
  refine (hrange.flatMap fun _ _ => List.Perm.refl _).trans ?_
  have hpairs :
      ((List.range L).flatMap fun k =>
        [cosineChordSq (θ + chebyshevRootAngle L k),
          cosineChordSq (θ - chebyshevRootAngle L k)]).Perm
      ((List.range L).flatMap fun k =>
        [chebyshevChordGridEntry L θ k,
          chebyshevChordGridEntry L θ (L + (L - 1 - k))]) := by
    apply List.Perm.flatMap_left
    intro k hk
    simp only [List.mem_range] at hk
    rw [chebyshevChordGridEntry_reverse hL hk]
    simp [chebyshevChordGridEntry, chebyshevRootAngle]
  refine hpairs.trans ?_
  simpa [List.map_flatMap] using
    ((chebyshevSignedIndexList_perm L).map (chebyshevChordGridEntry L θ))

private theorem chebyshevChordGridEntry_add_pi_div
    {L : ℕ} (hL : 0 < L) (θ : ℝ) (i : Fin (2 * L)) :
    chebyshevChordGridEntry L (θ + Real.pi / (L : ℝ)) i.val =
      chebyshevChordGridEntry L θ (finRotate (2 * L) i).val := by
  letI : NeZero (2 * L) := ⟨by omega⟩
  have hone : ((1 : Fin (2 * L)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt] <;> omega
  rw [finRotate_apply, Fin.val_add, hone]
  by_cases hi : i.val + 1 < 2 * L
  · rw [Nat.mod_eq_of_lt hi]
    have hcoef :
        ((2 * (i.val + 1) + 1 : ℕ) : ℝ) =
          ((2 * i.val + 1 : ℕ) : ℝ) + 2 := by
      exact_mod_cast
        (show 2 * (i.val + 1) + 1 = (2 * i.val + 1) + 2 by omega)
    unfold chebyshevChordGridEntry
    congr 1
    rw [hcoef]
    field_simp
    ring
  · have hieq : i.val + 1 = 2 * L := by omega
    have hival : i.val = 2 * L - 1 := by omega
    rw [hieq, Nat.mod_self, hival]
    have hcoef :
        ((2 * (2 * L - 1) + 1 : ℕ) : ℝ) =
          (4 : ℝ) * (L : ℝ) - 1 := by
      have hn : 2 * (2 * L - 1) + 1 = 4 * L - 1 := by omega
      rw [hn, Nat.cast_sub (by omega)]
      push_cast
      ring
    unfold chebyshevChordGridEntry cosineChordSq
    congr 2
    rw [hcoef]
    rw [show
      θ + Real.pi / (L : ℝ) +
          ((4 : ℝ) * (L : ℝ) - 1) * Real.pi / (2 * (L : ℝ)) =
        (θ + (1 : ℝ) * Real.pi / (2 * (L : ℝ))) +
          (1 : ℤ) * (2 * Real.pi) by
      norm_num
      field_simp
      ring]
    convert Real.cos_add_int_mul_two_pi
      (θ + (1 : ℝ) * Real.pi / (2 * (L : ℝ))) 1 using 1 <;> norm_num

private theorem ofFn_val_eq_map_range
    {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  rw [List.ofFn_eq_pmap]
  simp

private theorem chebyshevChordGrid_add_pi_div_perm
    {L : ℕ} (hL : 0 < L) (θ : ℝ) :
    ((List.range (2 * L)).map
      (chebyshevChordGridEntry L (θ + Real.pi / (L : ℝ)))).Perm
    ((List.range (2 * L)).map (chebyshevChordGridEntry L θ)) := by
  letI : NeZero (2 * L) := ⟨by omega⟩
  rw [← ofFn_val_eq_map_range, ← ofFn_val_eq_map_range]
  have heq :
      (fun i : Fin (2 * L) =>
        chebyshevChordGridEntry L (θ + Real.pi / (L : ℝ)) i.val) =
      (fun i : Fin (2 * L) => chebyshevChordGridEntry L θ i.val) ∘
        finRotate (2 * L) := by
    funext i
    exact chebyshevChordGridEntry_add_pi_div hL θ i
  rw [heq]
  exact (finRotate (2 * L)).ofFn_comp_perm
    (fun i : Fin (2 * L) => chebyshevChordGridEntry L θ i.val)

private theorem chebyshevPairedChordList_add_pi_div_perm
    {L : ℕ} (hL : 0 < L) (θ : ℝ) :
    (chebyshevPairedChordList L (θ + Real.pi / (L : ℝ))).Perm
      (chebyshevPairedChordList L θ) :=
  (chebyshevPairedChordList_perm_grid hL _).trans <|
    (chebyshevChordGrid_add_pi_div_perm hL θ).trans <|
      (chebyshevPairedChordList_perm_grid hL θ).symm

/-- Shifting [a real angle](hyp:θ) by [an integer multiple](hyp:m) of the step determined by
[a positive integer](hyp:L,hL) [permutes the paired list of Chebyshev chord squares](goal). -/
theorem chebyshevPairedChordList_add_int_mul_pi_div_perm
    {L : ℕ} (hL : 0 < L) (θ : ℝ) (m : ℤ) :
    (chebyshevPairedChordList L
      (θ + (m : ℝ) * (Real.pi / (L : ℝ)))).Perm
        (chebyshevPairedChordList L θ) := by
  induction m using Int.induction_on with
  | zero => simp
  | @succ i ih =>
      have hstep := chebyshevPairedChordList_add_pi_div_perm hL
        (θ + (i : ℝ) * (Real.pi / (L : ℝ)))
      have heq :
          θ + (((i : ℤ) + 1 : ℤ) : ℝ) * (Real.pi / (L : ℝ)) =
            θ + (i : ℝ) * (Real.pi / (L : ℝ)) + Real.pi / (L : ℝ) := by
        norm_num
        ring
      rw [heq]
      exact hstep.trans ih
  | @pred i ih =>
      have hstep := chebyshevPairedChordList_add_pi_div_perm hL
        (θ + ((-(i : ℤ) - 1 : ℤ) : ℝ) * (Real.pi / (L : ℝ)))
      have heq :
          θ + ((-(i : ℤ) - 1 : ℤ) : ℝ) * (Real.pi / (L : ℝ)) +
              Real.pi / (L : ℝ) =
            θ + ((-(i : ℤ) : ℤ) : ℝ) * (Real.pi / (L : ℝ)) := by
        norm_num
        ring
      rw [heq] at hstep
      exact hstep.symm.trans ih

/-! ## Adjacent chord ordering -/


private lemma cosineChordSq_mono_on_zero_pi {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ Real.pi) (hxy : x ≤ y) :
    cosineChordSq x ≤ cosineChordSq y := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx hy hxy
  unfold cosineChordSq
  linarith

private lemma adjacentPairProduct_flatMap_two (t : ℝ) (ks : List ℕ)
    (a b : ℕ → ℝ) :
    adjacentPairProduct t (ks.flatMap fun k => [a k, b k]) =
      (ks.map fun k => a k * b k + t).prod := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      simpa [adjacentPairProduct] using
        congrArg (fun z => (a k * b k + t) * z) ih

/-- At a centered angle `|φ| ≤ π/(2L)`, decreasingly sorting all `2L` chord
squares can be done without changing the product obtained from the root-angle
pairing, for any common additive term. [The degree, its positivity, the angle,
and the additive term](hyp:L,hL,φ,hφ,t) establish [the stated conclusion](goal). -/
theorem exists_sorted_chebyshevChordList_with_adjacentPairProduct_eq_of_centered
    {L : ℕ} (hL : 0 < L) {φ t : ℝ}
    (hφ : |φ| ≤ Real.pi / (2 * (L : ℝ))) :
    ∃ zs : List ℝ,
      zs.Perm (chebyshevPairedChordList L φ) ∧
        zs.Pairwise (fun a b => b ≤ a) ∧
          adjacentPairProduct t zs =
            adjacentPairProduct t (chebyshevPairedChordList L φ) := by
  let δ : ℝ := Real.pi / (2 * (L : ℝ))
  let u : ℝ := |φ|
  let a : ℕ → ℝ := fun k =>
    cosineChordSq (chebyshevRootAngle L k + u)
  let b : ℕ → ℝ := fun k =>
    cosineChordSq (chebyshevRootAngle L k - u)
  -- Reverse the roots, and put the larger circular distance first in each
  -- root block. At `u = δ`, neighboring blocks may tie.
  let zs := (List.range L).reverse.flatMap fun k => [a k, b k]
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hu0 : 0 ≤ u := abs_nonneg φ
  have huδ : u ≤ δ := hφ
  have hangle (k : ℕ) :
      chebyshevRootAngle L k = ((2 * k + 1 : ℕ) : ℝ) * δ := by
    simp only [chebyshevRootAngle, δ]
    ring
  have hcast (k : ℕ) : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hδpi : 2 * (L : ℝ) * δ = Real.pi := by
    dsimp [δ]
    field_simp
  have hbounds (k : ℕ) (hk : k < L) :
      0 ≤ chebyshevRootAngle L k - u ∧
        chebyshevRootAngle L k + u ≤ Real.pi := by
    have hkcast : (k : ℝ) ≤ (L : ℝ) - 1 := by
      have hkn : k + 1 ≤ L := by omega
      have hkr : (k : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hkn
      linarith
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    rw [hangle, hcast]
    constructor <;> nlinarith
  have hwithin (k : ℕ) (hk : k < L) : b k ≤ a k := by
    dsimp [a, b]
    apply cosineChordSq_mono_on_zero_pi
    · exact (hbounds k hk).1
    · exact (hbounds k hk).2
    · linarith
  have hcross (j k : ℕ) (hj : j < L) (hk : k < L) (hjk : j < k) :
      a j ≤ b k := by
    have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
    dsimp [a, b]
    apply cosineChordSq_mono_on_zero_pi
    · have h := (hbounds j hj).1
      rw [hangle, hcast] at h ⊢
      nlinarith
    · have h := (hbounds k hk).2
      rw [hangle, hcast] at h ⊢
      nlinarith
    · rw [hangle, hangle, hcast, hcast]
      nlinarith
  have hsorted : zs.Pairwise (fun x y => y ≤ x) := by
    dsimp [zs]
    rw [List.pairwise_flatMap]
    constructor
    · intro k hk
      simp only [List.mem_reverse, List.mem_range] at hk
      simpa using hwithin k hk
    · rw [List.pairwise_reverse]
      have hrangePair : (List.range L).Pairwise
          (fun j k => j < k ∧ k < L) := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.length_range] at hi hj
        simp only [List.getElem_range]
        omega
      apply hrangePair.imp
      intro j k hjk x hx y hy
      have hj : j < L := lt_trans hjk.1 hjk.2
      have hk : k < L := hjk.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hcross j k hj hk hjk.1).trans (hwithin k hk)
      · exact (hwithin j hj).trans
          ((hcross j k hj hk hjk.1).trans (hwithin k hk))
      · exact hcross j k hj hk hjk.1
      · exact (hwithin j hj).trans (hcross j k hj hk hjk.1)
  -- Replacing `φ` by `|φ|` only swaps the two entries in each root block.
  have hpairs (k : ℕ) (hk : k < L) :
      [a k, b k].Perm
        [cosineChordSq (φ + chebyshevRootAngle L k),
          cosineChordSq (φ - chebyshevRootAngle L k)] := by
    by_cases hφ0 : 0 ≤ φ
    · have hu : u = φ := abs_of_nonneg hφ0
      have ha : a k = cosineChordSq (φ + chebyshevRootAngle L k) := by
        dsimp [a]
        rw [hu]
        congr 1 <;> ring
      have hb : b k = cosineChordSq (φ - chebyshevRootAngle L k) := by
        dsimp [b]
        rw [hu]
        rw [show chebyshevRootAngle L k - φ =
          -(φ - chebyshevRootAngle L k) by ring]
        simp only [cosineChordSq]
        rw [Real.cos_neg]
      rw [ha, hb]
    · have hφ0' : φ ≤ 0 := le_of_not_ge hφ0
      have hu : u = -φ := abs_of_nonpos hφ0'
      have ha : a k = cosineChordSq (φ - chebyshevRootAngle L k) := by
        dsimp [a]
        rw [hu]
        rw [show chebyshevRootAngle L k + -φ =
          -(φ - chebyshevRootAngle L k) by ring]
        simp only [cosineChordSq]
        rw [Real.cos_neg]
      have hb : b k = cosineChordSq (φ + chebyshevRootAngle L k) := by
        dsimp [b]
        rw [hu]
        congr 1 <;> ring
      rw [ha, hb]
      exact List.Perm.swap _ _ []
  have hrange : (Finset.range L).val.toList.Perm (List.range L) := by
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 ?_
    · rw [← Multiset.coe_nodup, Multiset.coe_toList]
      exact (Finset.range L).nodup
    · simp
  have hperm : zs.Perm (chebyshevPairedChordList L φ) := by
    dsimp [zs]
    rw [chebyshevPairedChordList]
    exact ((List.reverse_perm (List.range L)).flatMap
      (fun k hk => List.Perm.refl _)).trans <|
        hrange.symm.flatMap fun k hk => hpairs k (by simpa using hk)
  refine ⟨zs, hperm, hsorted, ?_⟩
  rw [chebyshevPairedChordList]
  rw [adjacentPairProduct_flatMap_two, adjacentPairProduct_flatMap_two]
  rw [List.map_reverse, List.prod_reverse]
  rw [(hrange.symm.map (fun k => a k * b k + t)).prod_eq]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hp := (hpairs k (by simpa using hk)).prod_eq
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun z => z + t) hp

/-! ## Root-product geometry -/


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
