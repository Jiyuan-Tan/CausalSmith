/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.ChebyshevChordDefinitions
public import Mathlib.Data.List.FinRange

/-!
# Cyclic permutation of the Chebyshev chord grid

The union of the positive and negative degree-`L` Chebyshev root angles is
the odd `2L`-point grid on the circle. Translating the base angle by an
integer multiple of `π/L` therefore only permutes its chord squares.
-/

@[expose] public section

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

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

/-- Shifting an angle by any integer multiple of `π/L` permutes the paired
list of the `2L` Chebyshev chord squares. -/
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

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
