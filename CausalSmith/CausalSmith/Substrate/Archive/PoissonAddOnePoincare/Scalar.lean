/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.PoissonAddOnePoincare.Foundations

/-!
# Scalar Poisson add-one Poincaré inequality

This module proves the sharp scalar Poincaré inequality first for finitely supported
sequences and then for arbitrary functions in the graph domain of the Poisson add-one
operator. The theorem is stated for every nonnegative rate, so the degenerate zero-rate
Poisson law is included.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators NNReal

namespace CausalSmith.Substrate.PoissonAddOnePoincare

noncomputable section

private theorem poisson_crossing_coefficient (lambda : NNReal) (k : Nat) :
    (∑ n ∈ Finset.range (k + 1), ∑' j : Nat,
      poissonWeight lambda n * poissonWeight lambda (k + 1 + j) *
        ((k + 1 + j - n : Nat) : Real)) =
      (lambda : Real) * poissonWeight lambda k := by
  have hp : Summable (poissonWeight lambda) :=
    (poissonWeight_hasSum_one lambda).summable
  have hp0 : (∑' n : Nat, poissonWeight lambda n) = 1 :=
    (poissonWeight_hasSum_one lambda).tsum_eq
  let A : Real := ∑ n ∈ Finset.range (k + 1), poissonWeight lambda n
  let D : Real := ∑ n ∈ Finset.range k, poissonWeight lambda n
  let B : Real := ∑' j : Nat, poissonWeight lambda (j + k)
  let E : Real := ∑' j : Nat, poissonWeight lambda (j + (k + 1))
  have htailB : D + B = 1 := by
    simpa only [D, B, hp0] using hp.sum_add_tsum_nat_add k
  have htailE : A + E = 1 := by
    simpa only [A, E, hp0] using hp.sum_add_tsum_nat_add (k + 1)
  have hA : A = D + poissonWeight lambda k := by
    simp only [A, D, Finset.sum_range_succ]
  have hB : B = poissonWeight lambda k + E := by
    dsimp only [B, E]
    have h := ((summable_nat_add_iff k).2 hp).sum_add_tsum_nat_add 1
    simpa [add_assoc, add_comm, add_left_comm] using h.symm
  have hmoment :
      (∑ n ∈ Finset.range (k + 1), (n : Real) * poissonWeight lambda n) =
        (lambda : Real) * D := by
    calc
      (∑ n ∈ Finset.range (k + 1), (n : Real) * poissonWeight lambda n) =
          ∑ n ∈ Finset.range k,
            ((n + 1 : Nat) : Real) * poissonWeight lambda (n + 1) := by
        rw [Finset.sum_range_succ']
        simp
      _ = ∑ n ∈ Finset.range k,
            (lambda : Real) * poissonWeight lambda n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact poissonWeight_succ_shift lambda n
      _ = (lambda : Real) * D := by
        rw [← Finset.mul_sum]
  have hinner (n : Nat) (hn : n < k + 1) :
      (∑' j : Nat,
        poissonWeight lambda n * poissonWeight lambda (k + 1 + j) *
          ((k + 1 + j - n : Nat) : Real)) =
        poissonWeight lambda n *
          ((lambda : Real) * B - (n : Real) * E) := by
    have hpk : Summable (fun j : Nat ↦ poissonWeight lambda (j + k)) :=
      (summable_nat_add_iff k).2 hp
    have hpe : Summable (fun j : Nat ↦ poissonWeight lambda (j + (k + 1))) :=
      (summable_nat_add_iff (k + 1)).2 hp
    calc
      _ = ∑' j : Nat, poissonWeight lambda n *
          ((lambda : Real) * poissonWeight lambda (j + k) -
            (n : Real) * poissonWeight lambda (j + (k + 1))) := by
        apply tsum_congr
        intro j
        have hle : n ≤ k + 1 + j := by omega
        have hshift := poissonWeight_succ_shift lambda (j + k)
        simp only [add_assoc, add_comm, add_left_comm] at hshift ⊢
        rw [Nat.cast_sub (by omega : n ≤ k + (j + 1))]
        rw [← hshift]
        ring
      _ = poissonWeight lambda n *
          ((∑' j : Nat, (lambda : Real) * poissonWeight lambda (j + k)) -
            ∑' j : Nat, (n : Real) * poissonWeight lambda (j + (k + 1))) := by
        let F : Nat → Real := fun j ↦ (lambda : Real) * poissonWeight lambda (j + k)
        let G : Nat → Real := fun j ↦ (n : Real) * poissonWeight lambda (j + (k + 1))
        have hF : Summable F := hpk.mul_left (lambda : Real)
        have hG : Summable G := hpe.mul_left (n : Real)
        calc
          _ = poissonWeight lambda n * (∑' j : Nat, (F j - G j)) := by
            exact (hF.sub hG).tsum_mul_left (poissonWeight lambda n)
          _ = _ := by
            rw [hF.tsum_sub hG]
      _ = _ := by
        rw [hpk.tsum_mul_left, hpe.tsum_mul_left]
  calc
    _ = ∑ n ∈ Finset.range (k + 1),
        poissonWeight lambda n * ((lambda : Real) * B - (n : Real) * E) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hinner n (by simpa using hn)
    _ = (lambda : Real) * B * A - E *
        (∑ n ∈ Finset.range (k + 1), (n : Real) * poissonWeight lambda n) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      have h₁ :
          (∑ n ∈ Finset.range (k + 1),
            poissonWeight lambda n * ((lambda : Real) * B)) =
            A * ((lambda : Real) * B) := by
        rw [← Finset.sum_mul]
      have h₂ :
          (∑ n ∈ Finset.range (k + 1),
            poissonWeight lambda n * ((n : Real) * E)) =
            (∑ n ∈ Finset.range (k + 1),
              (n : Real) * poissonWeight lambda n) * E := by
        calc
          _ = ∑ n ∈ Finset.range (k + 1),
              ((n : Real) * poissonWeight lambda n) * E := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = _ := by rw [← Finset.sum_mul]
      rw [h₁, h₂]
      ring
    _ = (lambda : Real) * poissonWeight lambda k := by
      rw [hmoment, hA, hB]
      have hone : D + poissonWeight lambda k + E = 1 := by
        linarith [htailB, htailE]
      calc
        (lambda : Real) * (poissonWeight lambda k + E) *
              (D + poissonWeight lambda k) -
            E * ((lambda : Real) * D) =
            (lambda : Real) * poissonWeight lambda k *
              (D + poissonWeight lambda k + E) := by ring
        _ = _ := by rw [hone, mul_one]

private theorem summable_poisson_crossing (lambda : NNReal) (k : Nat) :
    Summable (fun q : Fin (k + 1) × Nat ↦
      poissonWeight lambda q.1 * poissonWeight lambda (k + 1 + q.2) *
        ((k + 1 + q.2 - q.1 : Nat) : Real)) := by
  have hp : Summable (poissonWeight lambda) :=
    (poissonWeight_hasSum_one lambda).summable
  rw [summable_prod_of_nonneg]
  constructor
  · intro n
    have hpk : Summable (fun j : Nat ↦ poissonWeight lambda (j + k)) :=
      (summable_nat_add_iff k).2 hp
    have hpe : Summable (fun j : Nat ↦ poissonWeight lambda (j + (k + 1))) :=
      (summable_nat_add_iff (k + 1)).2 hp
    have hmajor : Summable (fun j : Nat ↦ poissonWeight lambda n *
        ((lambda : Real) * poissonWeight lambda (j + k) +
          (n : Real) * poissonWeight lambda (j + (k + 1)))) :=
      ((hpk.mul_left (lambda : Real)).add
        (hpe.mul_left (n : Real))).mul_left (poissonWeight lambda n)
    refine hmajor.of_nonneg_of_le (fun j ↦ ?_) (fun j ↦ ?_)
    · exact mul_nonneg
        (mul_nonneg (poissonWeight_nonneg lambda n)
          (poissonWeight_nonneg lambda (k + 1 + j))) (Nat.cast_nonneg _)
    · have hle : (n : Nat) ≤ k + (j + 1) := by omega
      have hshift := poissonWeight_succ_shift lambda (j + k)
      simp only [add_assoc, add_comm, add_left_comm] at hshift ⊢
      rw [Nat.cast_sub hle, ← hshift]
      have hleR : (n : Real) ≤ ((k + (j + 1) : Nat) : Real) := by
        exact_mod_cast hle
      have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg _
      have hp_n := poissonWeight_nonneg lambda n
      have hp_m := poissonWeight_nonneg lambda (k + (j + 1))
      have hdiff : ((k + (j + 1) : Nat) : Real) - (n : Real) ≤
          ((k + (j + 1) : Nat) : Real) + (n : Real) := by linarith
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdiff hp_m) hp_n
      calc
        poissonWeight lambda n * poissonWeight lambda (k + (j + 1)) *
            (((k + (j + 1) : Nat) : Real) - (n : Real)) =
            poissonWeight lambda n *
              (poissonWeight lambda (k + (j + 1)) *
                (((k + (j + 1) : Nat) : Real) - (n : Real))) := by ring
        _ ≤ poissonWeight lambda n *
              (poissonWeight lambda (k + (j + 1)) *
                (((k + (j + 1) : Nat) : Real) + (n : Real))) := hmul
        _ = poissonWeight lambda n *
            (((k + (j + 1) : Nat) : Real) * poissonWeight lambda (k + (j + 1)) +
              (n : Real) * poissonWeight lambda (k + (j + 1))) := by ring
  · apply summable_of_hasFiniteSupport
    exact Set.toFinite _
  · intro q
    exact mul_nonneg
      (mul_nonneg (poissonWeight_nonneg lambda q.1)
        (poissonWeight_nonneg lambda (k + 1 + q.2))) (Nat.cast_nonneg _)

private theorem poisson_crossing_coefficient_all (lambda : NNReal) (k : Nat) :
    (∑' q : Nat × Nat, if q.1 ≤ k ∧ k < q.2 then
      poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real) else 0) =
      (lambda : Real) * poissonWeight lambda k := by
  let s : Set (Nat × Nat) := {q | q.1 ≤ k ∧ k < q.2}
  let e : s ≃ Fin (k + 1) × Nat :=
    { toFun := fun q ↦ (⟨q.1.1, by simpa [s] using q.2.1⟩, q.1.2 - k - 1)
      invFun := fun q ↦ ⟨(q.1.1, k + 1 + q.2), by
        simp only [s, Set.mem_setOf_eq]
        constructor
        · omega
        · omega⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · simp only
          have := q.2.2
          simp only [s, Set.mem_setOf_eq] at this
          omega
      right_inv := by
        intro q
        apply Prod.ext
        · apply Fin.ext
          rfl
        · simp only
          omega }
  let a : Nat × Nat → Real := fun q ↦
    poissonWeight lambda q.1 * poissonWeight lambda q.2 *
      ((q.2 - q.1 : Nat) : Real)
  calc
    _ = ∑' q : s, a q := by
      rw [tsum_subtype]
      apply tsum_congr
      intro q
      by_cases hq : q ∈ s
      · rw [Set.indicator_of_mem hq]
        simp only [s, Set.mem_setOf_eq] at hq
        simp [a, hq]
      · simp only [Set.indicator, hq, ↓reduceIte]
        simp only [s, Set.mem_setOf_eq] at hq
        simp [a, hq]
    _ = ∑' q : Fin (k + 1) × Nat,
        poissonWeight lambda q.1 * poissonWeight lambda (k + 1 + q.2) *
          ((k + 1 + q.2 - q.1 : Nat) : Real) := by
      rw [← e.tsum_eq]
      apply tsum_congr
      intro q
      have hq := q.2
      simp only [s, Set.mem_setOf_eq] at hq
      have hm : q.1.2 = k + 1 + (q.1.2 - k - 1) := by omega
      change a q.1 = poissonWeight lambda q.1.1 *
        poissonWeight lambda (k + 1 + (q.1.2 - k - 1)) *
          ((k + 1 + (q.1.2 - k - 1) - q.1.1 : Nat) : Real)
      dsimp only [a]
      rw [← hm]
    _ = ∑ n : Fin (k + 1), ∑' j : Nat,
        poissonWeight lambda n * poissonWeight lambda (k + 1 + j) *
          ((k + 1 + j - n : Nat) : Real) := by
      rw [(summable_poisson_crossing lambda k).tsum_prod, tsum_fintype]
    _ = _ := by
      have h := poisson_crossing_coefficient lambda k
      rw [← Fin.sum_univ_eq_sum_range] at h
      exact h

private theorem summable_poisson_crossing_all (lambda : NNReal) (k : Nat) :
    Summable (fun q : Nat × Nat ↦ if q.1 ≤ k ∧ k < q.2 then
      poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real) else 0) := by
  have hp : Summable (poissonWeight lambda) :=
    (poissonWeight_hasSum_one lambda).summable
  have hmoment : Summable (fun n : Nat ↦ (n : Real) * poissonWeight lambda n) := by
    rw [← summable_nat_add_iff 1]
    refine (hp.mul_left (lambda : Real)).congr ?_
    intro n
    simpa [add_comm] using (poissonWeight_succ_shift lambda n).symm
  let M : Real := ∑' n : Nat, (n : Real) * poissonWeight lambda n
  let P : Real := ∑' n : Nat, poissonWeight lambda n
  have hfirst : Summable (fun q : Nat × Nat ↦
      poissonWeight lambda q.1 * ((q.2 : Real) * poissonWeight lambda q.2)) := by
    rw [summable_prod_of_nonneg]
    constructor
    · intro n
      exact hmoment.mul_left (poissonWeight lambda n)
    · have houter : Summable (fun n : Nat ↦ poissonWeight lambda n * M) :=
        hp.mul_right M
      refine houter.congr ?_
      intro n
      change poissonWeight lambda n * M =
        ∑' y : Nat, poissonWeight lambda n * ((y : Real) * poissonWeight lambda y)
      rw [hmoment.tsum_mul_left]
    · intro q
      exact mul_nonneg (poissonWeight_nonneg lambda q.1)
        (mul_nonneg (Nat.cast_nonneg _) (poissonWeight_nonneg lambda q.2))
  have hsecond : Summable (fun q : Nat × Nat ↦
      ((q.1 : Real) * poissonWeight lambda q.1) * poissonWeight lambda q.2) := by
    rw [summable_prod_of_nonneg]
    constructor
    · intro n
      exact hp.mul_left ((n : Real) * poissonWeight lambda n)
    · refine (hmoment.mul_right P).congr ?_
      intro n
      change ((n : Real) * poissonWeight lambda n) * P =
        ∑' y : Nat, ((n : Real) * poissonWeight lambda n) * poissonWeight lambda y
      rw [hp.tsum_mul_left]
    · intro q
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (poissonWeight_nonneg lambda q.1))
        (poissonWeight_nonneg lambda q.2)
  have hmajor : Summable (fun q : Nat × Nat ↦
      poissonWeight lambda q.1 * ((q.2 : Real) * poissonWeight lambda q.2) +
        ((q.1 : Real) * poissonWeight lambda q.1) * poissonWeight lambda q.2) :=
    hfirst.add hsecond
  refine hmajor.of_nonneg_of_le (fun q ↦ ?_) (fun q ↦ ?_)
  · by_cases hq : q.1 ≤ k ∧ k < q.2
    · simp only [hq, ↓reduceIte]
      exact mul_nonneg
        (mul_nonneg (poissonWeight_nonneg lambda q.1)
          (poissonWeight_nonneg lambda q.2)) (Nat.cast_nonneg _)
    · simp [hq]
  · by_cases hq : q.1 ≤ k ∧ k < q.2
    · simp only [hq, ↓reduceIte]
      have hnm : q.1 ≤ q.2 := by omega
      rw [Nat.cast_sub hnm]
      have hp₁ := poissonWeight_nonneg lambda q.1
      have hp₂ := poissonWeight_nonneg lambda q.2
      have hn : 0 ≤ (q.1 : Real) := Nat.cast_nonneg _
      have hm : 0 ≤ (q.2 : Real) := Nat.cast_nonneg _
      have hdiff : (q.2 : Real) - (q.1 : Real) ≤
          (q.2 : Real) + (q.1 : Real) := by linarith
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdiff hp₂) hp₁
      calc
        poissonWeight lambda q.1 * poissonWeight lambda q.2 *
            ((q.2 : Real) - (q.1 : Real)) =
            poissonWeight lambda q.1 *
              (poissonWeight lambda q.2 * ((q.2 : Real) - (q.1 : Real))) := by ring
        _ ≤ poissonWeight lambda q.1 *
              (poissonWeight lambda q.2 * ((q.2 : Real) + (q.1 : Real))) := hmul
        _ = _ := by ring
    · simp only [hq, ↓reduceIte]
      exact add_nonneg
        (mul_nonneg (poissonWeight_nonneg lambda q.1)
          (mul_nonneg (Nat.cast_nonneg _) (poissonWeight_nonneg lambda q.2)))
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (poissonWeight_nonneg lambda q.1))
          (poissonWeight_nonneg lambda q.2))

set_option maxHeartbeats 800000 in
private theorem poisson_upper_path_tsum
    (lambda : NNReal) (f : Nat → Real)
    (hf : (Function.support f).Finite) :
    (∑' q : Nat × Nat, if q.1 < q.2 then
      poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real) *
          ∑ k ∈ Finset.Ico q.1 q.2, (addOne f k) ^ 2 else 0) =
      (lambda : Real) *
        ∑' k : Nat, poissonWeight lambda k * (addOne f k) ^ 2 := by
  let b : Nat → Nat × Nat → Real := fun k q ↦
    if q.1 ≤ k ∧ k < q.2 then
      poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real) * (addOne f k) ^ 2 else 0
  have hb_nonneg (k : Nat) (q : Nat × Nat) : 0 ≤ b k q := by
    dsimp only [b]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (poissonWeight_nonneg lambda q.1)
            (poissonWeight_nonneg lambda q.2)) (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  have hb_summable (k : Nat) : Summable (b k) := by
    have h := (summable_poisson_crossing_all lambda k).mul_right ((addOne f k) ^ 2)
    refine h.congr ?_
    intro q
    dsimp only [b]
    by_cases hq : q.1 ≤ k ∧ k < q.2 <;> simp [hq]
  have hb_tsum (k : Nat) :
      (∑' q : Nat × Nat, b k q) =
        (lambda : Real) * poissonWeight lambda k * (addOne f k) ^ 2 := by
    calc
      _ = ∑' q : Nat × Nat, (if q.1 ≤ k ∧ k < q.2 then
          poissonWeight lambda q.1 * poissonWeight lambda q.2 *
            ((q.2 - q.1 : Nat) : Real) else 0) * (addOne f k) ^ 2 := by
        apply tsum_congr
        intro q
        dsimp only [b]
        by_cases hq : q.1 ≤ k ∧ k < q.2 <;> simp [hq]
      _ = (∑' q : Nat × Nat, if q.1 ≤ k ∧ k < q.2 then
          poissonWeight lambda q.1 * poissonWeight lambda q.2 *
            ((q.2 - q.1 : Nat) : Real) else 0) * (addOne f k) ^ 2 :=
        (summable_poisson_crossing_all lambda k).tsum_mul_right _
      _ = _ := by rw [poisson_crossing_coefficient_all]
  have henergy : Summable (fun k : Nat ↦
      poissonWeight lambda k * (addOne f k) ^ 2) := by
    apply summable_of_hasFiniteSupport
    refine (finiteSupport_addOne f hf).subset ?_
    intro k hk
    simp only [Function.mem_support] at hk ⊢
    intro hdk
    simp [hdk] at hk
  have hb_outer : Summable (fun k : Nat ↦ ∑' q : Nat × Nat, b k q) := by
    refine ((henergy.mul_left (lambda : Real)).congr ?_)
    intro k
    rw [hb_tsum]
    ring
  have hb_joint : Summable (fun z : Nat × (Nat × Nat) ↦ b z.1 z.2) := by
    rw [summable_prod_of_nonneg (fun z ↦ hb_nonneg z.1 z.2)]
    exact ⟨hb_summable, hb_outer⟩
  have hrow (q : Nat × Nat) :
      (if q.1 < q.2 then
        poissonWeight lambda q.1 * poissonWeight lambda q.2 *
          ((q.2 - q.1 : Nat) : Real) *
            ∑ k ∈ Finset.Ico q.1 q.2, (addOne f k) ^ 2 else 0) =
        ∑' k : Nat, b k q := by
    by_cases hq : q.1 < q.2
    · simp only [hq, ↓reduceIte]
      let c : Real := poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real)
      let g : Nat → Real := fun k ↦ if k ∈ Finset.Ico q.1 q.2 then
        (addOne f k) ^ 2 else 0
      have hg : Summable g := by
        apply summable_of_hasFiniteSupport
        refine (Finset.finite_toSet (Finset.Ico q.1 q.2)).subset ?_
        intro k hk
        simp only [Function.mem_support] at hk
        have hmem : k ∈ Finset.Ico q.1 q.2 := by
          by_contra hnot
          have hgk : g k = 0 := by
            change (if k ∈ Finset.Ico q.1 q.2 then (addOne f k) ^ 2 else 0) = 0
            exact if_neg hnot
          exact hk hgk
        exact hmem
      have hgt : (∑' k : Nat, g k) =
          ∑ k ∈ Finset.Ico q.1 q.2, (addOne f k) ^ 2 := by
        calc
          _ = ∑' k : Nat, (Finset.Ico q.1 q.2 : Set Nat).indicator
              (fun k ↦ (addOne f k) ^ 2) k := by
            apply tsum_congr
            intro k
            simp [g, Set.indicator]
          _ = ∑' k : {k // k ∈ Finset.Ico q.1 q.2}, (addOne f k) ^ 2 := by
            exact (tsum_subtype (Finset.Ico q.1 q.2 : Set Nat)
              (fun k : Nat ↦ (addOne f k) ^ 2)).symm
          _ = _ := Finset.tsum_subtype (Finset.Ico q.1 q.2)
            (fun k : Nat ↦ (addOne f k) ^ 2)
      calc
        c * ∑ k ∈ Finset.Ico q.1 q.2, (addOne f k) ^ 2 =
            c * ∑' k : Nat, g k := by rw [hgt]
        _ = ∑' k : Nat, c * g k := (hg.tsum_mul_left c).symm
        _ = _ := by
          apply tsum_congr
          intro k
          dsimp only [b, c, g]
          by_cases hk : k ∈ Finset.Ico q.1 q.2
          · have hcross : q.1 ≤ k ∧ k < q.2 := by simpa using hk
            simp [hk, hcross]
          · have hcross : ¬(q.1 ≤ k ∧ k < q.2) := by simpa using hk
            simp [hk, hcross]
    · have hzero (k : Nat) : b k q = 0 := by
        dsimp only [b]
        have : ¬(q.1 ≤ k ∧ k < q.2) := by omega
        simp [this]
      simp only [hq, ↓reduceIte]
      rw [show (fun k : Nat ↦ b k q) = fun _ ↦ (0 : Real) by
        funext k
        exact hzero k, tsum_zero]
  calc
    _ = ∑' q : Nat × Nat, ∑' k : Nat, b k q := by
      apply tsum_congr
      exact hrow
    _ = ∑' k : Nat, ∑' q : Nat × Nat, b k q := hb_joint.tsum_comm
    _ = ∑' k : Nat,
        (lambda : Real) * (poissonWeight lambda k * (addOne f k) ^ 2) := by
      apply tsum_congr
      intro k
      rw [hb_tsum]
      ring
    _ = _ := henergy.tsum_mul_left (lambda : Real)

private theorem summable_poisson_upper_path
    (lambda : NNReal) (f : Nat → Real)
    (hf : (Function.support f).Finite) :
    Summable (fun q : Nat × Nat ↦ if q.1 < q.2 then
      poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real) *
          ∑ k ∈ Finset.Ico q.1 q.2, (addOne f k) ^ 2 else 0) := by
  let S : Finset Nat := (finiteSupport_addOne f hf).toFinset
  let b : Nat → Nat × Nat → Real := fun k q ↦
    if q.1 ≤ k ∧ k < q.2 then
      poissonWeight lambda q.1 * poissonWeight lambda q.2 *
        ((q.2 - q.1 : Nat) : Real) * (addOne f k) ^ 2 else 0
  have hb (k : Nat) : Summable (b k) := by
    have h := (summable_poisson_crossing_all lambda k).mul_right ((addOne f k) ^ 2)
    refine h.congr ?_
    intro q
    dsimp only [b]
    by_cases hq : q.1 ≤ k ∧ k < q.2 <;> simp [hq]
  have hsum : Summable (fun q : Nat × Nat ↦ ∑ k ∈ S, b k q) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
        simpa [Finset.sum_insert, hk] using (hb k).add ih
  refine hsum.congr ?_
  intro q
  by_cases hq : q.1 < q.2
  · simp only [hq, ↓reduceIte]
    let I := Finset.Ico q.1 q.2
    have hpath : (∑ k ∈ I, (addOne f k) ^ 2) =
        ∑ k ∈ S.filter (fun k ↦ k ∈ I), (addOne f k) ^ 2 := by
      symm
      have hsub : S.filter (fun k ↦ k ∈ I) ⊆ I := by
        intro k hk
        simp only [Finset.mem_filter] at hk
        exact hk.2
      apply Finset.sum_subset hsub
      intro k hkI hkS
      have hknotS : k ∉ S := by
        intro hk
        exact hkS (by simp [hkI, hk])
      have hdk : addOne f k = 0 := by
        by_contra hne
        have hsupp : k ∈ Function.support (addOne f) := by
          simpa [Function.mem_support] using hne
        exact hknotS (by simpa [S] using hsupp)
      simp [hdk]
    rw [hpath, Finset.mul_sum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [b]
    by_cases hki : k ∈ I
    · have hcross : q.1 ≤ k ∧ k < q.2 := by simpa [I] using hki
      simp [hki, hcross]
    · have hcross : ¬(q.1 ≤ k ∧ k < q.2) := by simpa [I] using hki
      simp [hki, hcross]
  · have hcross (k : Nat) : ¬(q.1 ≤ k ∧ k < q.2) := by omega
    simp [hq, b, hcross]

set_option maxHeartbeats 800000 in
private theorem poisson_pairwise_tsum_le
    (lambda : NNReal) (f : Nat → Real)
    (hf : (Function.support f).Finite) :
    (∑' n : Nat, ∑' m : Nat,
      poissonWeight lambda n * poissonWeight lambda m * (f n - f m) ^ 2) ≤
      2 * (lambda : Real) *
        ∑' k : Nat, poissonWeight lambda k * (addOne f k) ^ 2 := by
  let u : Nat × Nat → Real := fun q ↦ if q.1 < q.2 then
    poissonWeight lambda q.1 * poissonWeight lambda q.2 *
      ((q.2 - q.1 : Nat) : Real) *
        ∑ k ∈ Finset.Ico q.1 q.2, (addOne f k) ^ 2 else 0
  let a : Nat × Nat → Real := fun q ↦
    poissonWeight lambda q.1 * poissonWeight lambda q.2 * (f q.1 - f q.2) ^ 2
  have hu : Summable u := summable_poisson_upper_path lambda f hf
  have huswap : Summable (fun q : Nat × Nat ↦ u q.swap) :=
    hu.comp_injective Prod.swap_injective
  have hu_nonneg (q : Nat × Nat) : 0 ≤ u q := by
    dsimp only [u]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (poissonWeight_nonneg lambda q.1)
            (poissonWeight_nonneg lambda q.2)) (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun k hk ↦ sq_nonneg _)
    · exact le_rfl
  have ha_nonneg (q : Nat × Nat) : 0 ≤ a q := by
    exact mul_nonneg
      (mul_nonneg (poissonWeight_nonneg lambda q.1)
        (poissonWeight_nonneg lambda q.2)) (sq_nonneg _)
  have hpoint (q : Nat × Nat) : a q ≤ u q + u q.swap := by
    rcases q with ⟨n, m⟩
    rcases lt_trichotomy n m with hlt | heq | hgt
    · have hs : (f m - f n) ^ 2 ≤
          (m - n : Nat) * ∑ k ∈ Finset.Ico n m, (addOne f k) ^ 2 := by
        simpa only [addOne] using
          sq_sub_le_nat_sub_mul_sum_sq_step f (Nat.le_of_lt hlt)
      have hp := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (poissonWeight_nonneg lambda m))
        (poissonWeight_nonneg lambda n)
      have hau : a (n, m) ≤ u (n, m) := by
        dsimp only [a, u]
        simp only [hlt, ↓reduceIte]
        calc
          poissonWeight lambda n * poissonWeight lambda m * (f n - f m) ^ 2 =
              poissonWeight lambda n * poissonWeight lambda m * (f m - f n) ^ 2 := by ring
          _ = poissonWeight lambda n *
              (poissonWeight lambda m * (f m - f n) ^ 2) := by ring
          _ ≤ _ := hp
          _ = _ := by ring
      exact hau.trans (le_add_of_nonneg_right (hu_nonneg (n, m).swap))
    · subst m
      simpa [a] using hu_nonneg (n, n)
    · have hs : (f n - f m) ^ 2 ≤
          (n - m : Nat) * ∑ k ∈ Finset.Ico m n, (addOne f k) ^ 2 := by
        simpa only [addOne] using
          sq_sub_le_nat_sub_mul_sum_sq_step f (Nat.le_of_lt hgt)
      have hp := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (poissonWeight_nonneg lambda n))
        (poissonWeight_nonneg lambda m)
      have hau : a (n, m) ≤ u (n, m).swap := by
        dsimp only [a, u]
        simp only [Prod.swap_prod_mk, hgt, ↓reduceIte]
        calc
          poissonWeight lambda n * poissonWeight lambda m * (f n - f m) ^ 2 =
              poissonWeight lambda m * poissonWeight lambda n * (f n - f m) ^ 2 := by ring
          _ = poissonWeight lambda m *
              (poissonWeight lambda n * (f n - f m) ^ 2) := by ring
          _ ≤ _ := hp
          _ = _ := by ring
      exact hau.trans (le_add_of_nonneg_left (hu_nonneg (n, m)))
  have ha : Summable a :=
    (hu.add huswap).of_nonneg_of_le ha_nonneg hpoint
  calc
    (∑' n : Nat, ∑' m : Nat, a (n, m)) = ∑' q : Nat × Nat, a q :=
      ha.tsum_prod.symm
    _ ≤ ∑' q : Nat × Nat, (u q + u q.swap) :=
      ha.tsum_le_tsum hpoint (hu.add huswap)
    _ = (∑' q : Nat × Nat, u q) + ∑' q : Nat × Nat, u q.swap :=
      hu.tsum_add huswap
    _ = 2 * ∑' q : Nat × Nat, u q := by
      have hswap : (∑' q : Nat × Nat, u q.swap) = ∑' q : Nat × Nat, u q := by
        exact (Equiv.prodComm Nat Nat).tsum_eq u
      rw [hswap]
      ring
    _ = _ := by
      rw [poisson_upper_path_tsum lambda f hf]
      ring

private theorem integral_sq_tendsto_of_integral_sq_sub_tendsto_zero
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (u : Nat → alpha → Real) (g : alpha → Real)
    (hu : ∀ K, MemLp (u K) 2 mu) (hg : MemLp g 2 mu)
    (hconv : Tendsto (fun K ↦ ∫ x, (u K x - g x) ^ 2 ∂mu)
      atTop (nhds 0)) :
    Tendsto (fun K ↦ ∫ x, (u K x) ^ 2 ∂mu)
      atTop (nhds (∫ x, g x ^ 2 ∂mu)) := by
  let d : Nat → alpha → Real := fun K x ↦ u K x - g x
  have hd (K : Nat) : MemLp (d K) 2 mu := by
    convert (hu K).sub hg using 1
    ext x
    rfl
  have hCS (v w : alpha → Real) (hv : MemLp v 2 mu) (hw : MemLp w 2 mu) :
      |∫ x, v x * w x ∂mu| ≤
        Real.sqrt (∫ x, v x ^ 2 ∂mu) * Real.sqrt (∫ x, w x ^ 2 ∂mu) := by
    calc
      |∫ x, v x * w x ∂mu| = ‖∫ x, v x * w x ∂mu‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ x, ‖v x * w x‖ ∂mu := norm_integral_le_integral_norm _
      _ = ∫ x, ‖v x‖ * ‖w x‖ ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_mul]
      _ ≤ (∫ x, ‖v x‖ ^ (2 : Real) ∂mu) ^ ((1 : Real) / 2) *
          (∫ x, ‖w x‖ ^ (2 : Real) ∂mu) ^ ((1 : Real) / 2) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
          (by simpa using hv) (by simpa using hw)
      _ = _ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        congr 2 <;> apply integral_congr_ae <;> filter_upwards with x <;>
          simp [sq_abs]
  have hsqrt : Tendsto (fun K ↦ Real.sqrt (∫ x, d K x ^ 2 ∂mu))
      atTop (nhds 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
    convert h using 1 <;> simp [Function.comp_def, d]
  have hcross : Tendsto (fun K ↦ ∫ x, g x * d K x ∂mu) atTop (nhds 0) := by
    refine squeeze_zero_norm
      (a := fun K ↦ Real.sqrt (∫ x, g x ^ 2 ∂mu) *
        Real.sqrt (∫ x, d K x ^ 2 ∂mu)) ?_ ?_
    · intro K
      exact hCS g (d K) hg (hd K)
    · simpa using ((tendsto_const_nhds : Tendsto
        (fun _ : Nat ↦ Real.sqrt (∫ x, g x ^ 2 ∂mu)) atTop
        (nhds (Real.sqrt (∫ x, g x ^ 2 ∂mu)))).mul hsqrt)
  convert ((tendsto_const_nhds : Tendsto
      (fun _ : Nat ↦ ∫ x, g x ^ 2 ∂mu) atTop (nhds (∫ x, g x ^ 2 ∂mu))).add
        (hconv.add (hcross.const_mul 2))) using 1
  · funext K
    calc
      (∫ x, u K x ^ 2 ∂mu) =
          ∫ x, g x ^ 2 + ((u K x - g x) ^ 2 + 2 * (g x * d K x)) ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        simp [d]
        ring
      _ = (∫ x, g x ^ 2 ∂mu) +
          ∫ x, (u K x - g x) ^ 2 + 2 * (g x * d K x) ∂mu :=
        integral_add hg.integrable_sq
          ((hd K).integrable_sq.add ((MemLp.integrable_mul hg (hd K)).const_mul 2))
      _ = _ := by
        have hdsq : Integrable (fun x ↦ (u K x - g x) ^ 2) mu := by
          simpa only [d] using (hd K).integrable_sq
        have hprod : Integrable (fun x ↦ g x * d K x) mu := by
          convert MemLp.integrable_mul hg (hd K) using 1
          ext x
          rfl
        congr 1
        rw [integral_add hdsq (hprod.const_mul 2), integral_const_mul]
  · simp

/-- A finitely supported real sequence has Poisson variance at most the rate times the
expected square of its add-one increment, for every nonnegative rate. -/
theorem poisson_addOne_poincare_finiteSupport
    (lambda : NNReal) (f : Nat → Real)
    (hf : (Function.support f).Finite) :
    variance f (poissonMeasure lambda) ≤
      (lambda : Real) *
        ∫ n, (addOne f n) ^ 2 ∂(poissonMeasure lambda) := by
  -- Use the pairwise product-law identity, split the double sum into the two strict
  -- triangles, telescope each `f m - f n`, and reindex the resulting nonnegative sums.
  -- The Poisson shift identity collapses the coefficient of each squared increment to
  -- at most `lambda * p_k`. Keep the zero-rate case inside the same mass calculation.
  have hflp : MemLp f 2 (poissonMeasure lambda) :=
    memLp_poissonMeasure_of_finiteSupport lambda f hf
  have hfi : Integrable f (poissonMeasure lambda) := hflp.integrable one_le_two
  have hfsq : Integrable (fun n ↦ f n ^ 2) (poissonMeasure lambda) :=
    hflp.integrable_sq
  have hfst : Integrable (fun z : Nat × Nat ↦ f z.1 ^ 2)
      ((poissonMeasure lambda).prod (poissonMeasure lambda)) :=
    hfsq.comp_fst (poissonMeasure lambda)
  have hsnd : Integrable (fun z : Nat × Nat ↦ f z.2 ^ 2)
      ((poissonMeasure lambda).prod (poissonMeasure lambda)) :=
    hfsq.comp_snd (poissonMeasure lambda)
  have hcross : Integrable (fun z : Nat × Nat ↦ f z.1 * f z.2)
      ((poissonMeasure lambda).prod (poissonMeasure lambda)) :=
    hfi.mul_prod hfi
  have hpair : Integrable (fun z : Nat × Nat ↦ (f z.1 - f z.2) ^ 2)
      ((poissonMeasure lambda).prod (poissonMeasure lambda)) := by
    have h := (hfst.sub (hcross.const_mul 2)).add hsnd
    refine h.congr ?_
    filter_upwards with z
    change f z.1 ^ 2 - 2 * (f z.1 * f z.2) + f z.2 ^ 2 =
      (f z.1 - f z.2) ^ 2
    ring
  rw [variance_eq_half_integral_prod_sq_sub (poissonMeasure lambda) f hflp]
  rw [integral_prod _ hpair]
  have hinner (n : Nat) :
      (∫ m, (f n - f m) ^ 2 ∂(poissonMeasure lambda)) =
        ∑' m : Nat, poissonWeight lambda m * (f n - f m) ^ 2 := by
    rw [integral_poissonMeasure]
    simp only [poissonWeight, smul_eq_mul]
  have hp : Summable (poissonWeight lambda) :=
    (poissonWeight_hasSum_one lambda).summable
  have hpsq : Summable (fun m : Nat ↦ poissonWeight lambda m * f m ^ 2) := by
    have h := integrable_poissonMeasure_iff.mp hfsq
    refine h.congr ?_
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f n))]
    rfl
  have hinnerSummable (n : Nat) :
      Summable (fun m : Nat ↦ poissonWeight lambda m * (f n - f m) ^ 2) := by
    have hmajor : Summable (fun m : Nat ↦
        2 * (poissonWeight lambda m * f n ^ 2 +
          poissonWeight lambda m * f m ^ 2)) :=
      ((hp.mul_right (f n ^ 2)).add hpsq).mul_left 2
    refine hmajor.of_nonneg_of_le (fun m ↦ ?_) (fun m ↦ ?_)
    · exact mul_nonneg (poissonWeight_nonneg lambda m) (sq_nonneg _)
    · have hs : (f n - f m) ^ 2 ≤ 2 * (f n ^ 2 + f m ^ 2) := by
        nlinarith [sq_nonneg (f n + f m)]
      have hm := mul_le_mul_of_nonneg_left hs (poissonWeight_nonneg lambda m)
      nlinarith
  rw [integral_poissonMeasure]
  simp only [poissonWeight, smul_eq_mul]
  have hdouble :
      (∑' n : Nat,
        (Real.exp (-(lambda : Real)) * (lambda : Real) ^ n / Nat.factorial n) *
          ∫ m, (f n - f m) ^ 2 ∂(poissonMeasure lambda)) =
        ∑' n : Nat, ∑' m : Nat,
          poissonWeight lambda n * poissonWeight lambda m * (f n - f m) ^ 2 := by
    apply tsum_congr
    intro n
    rw [hinner]
    change poissonWeight lambda n *
        (∑' m : Nat, poissonWeight lambda m * (f n - f m) ^ 2) = _
    rw [← (hinnerSummable n).tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  rw [hdouble]
  have hpairBound := poisson_pairwise_tsum_le lambda f hf
  have henergy :
      (∫ n, (addOne f n) ^ 2 ∂(poissonMeasure lambda)) =
        ∑' n : Nat, poissonWeight lambda n * (addOne f n) ^ 2 := by
    rw [integral_poissonMeasure]
    simp only [poissonWeight, smul_eq_mul]
  rw [henergy]
  nlinarith

/-- Every square-integrable real sequence with square-integrable add-one increment has
Poisson variance at most the rate times its expected squared add-one increment. -/
theorem poisson_addOne_poincare
    (lambda : NNReal) (f : Nat → Real)
    (hf : MemLp f 2 (poissonMeasure lambda))
    (hdf : MemLp (addOne f) 2 (poissonMeasure lambda)) :
    variance f (poissonMeasure lambda) ≤
      (lambda : Real) *
        ∫ n, (addOne f n) ^ 2 ∂(poissonMeasure lambda) := by
  -- Apply the finite-support result to `supportTruncation K f`. Pass variance and energy
  -- to the limit with the two graph-norm closure lemmas and L² variance continuity.
  let fK : Nat → Nat → Real := fun K ↦ supportTruncation K f
  have hfK (K : Nat) : MemLp (fK K) 2 (poissonMeasure lambda) :=
    memLp_poissonMeasure_of_finiteSupport lambda _ (supportTruncation_finiteSupport K f)
  have hdfK (K : Nat) : MemLp (addOne (fK K)) 2 (poissonMeasure lambda) :=
    memLp_poissonMeasure_of_finiteSupport lambda _
      (finiteSupport_addOne _ (supportTruncation_finiteSupport K f))
  have hvar : Tendsto (fun K ↦ variance (fK K) (poissonMeasure lambda)) atTop
      (nhds (variance f (poissonMeasure lambda))) :=
    variance_tendsto_of_integral_sq_sub_tendsto_zero
      (poissonMeasure lambda) fK f hfK hf
      (by simpa [fK] using supportTruncation_integral_sq_tendsto_zero lambda f hf)
  have henergy : Tendsto
      (fun K ↦ ∫ n, (addOne (fK K) n) ^ 2 ∂(poissonMeasure lambda)) atTop
      (nhds (∫ n, (addOne f n) ^ 2 ∂(poissonMeasure lambda))) :=
    integral_sq_tendsto_of_integral_sq_sub_tendsto_zero
      (poissonMeasure lambda) (fun K ↦ addOne (fK K)) (addOne f) hdfK hdf
      (by simpa [fK] using
        supportTruncation_addOne_integral_sq_tendsto_zero lambda f hf hdf)
  exact le_of_tendsto_of_tendsto' hvar
    ((tendsto_const_nhds : Tendsto (fun _ : Nat ↦ (lambda : Real)) atTop
      (nhds (lambda : Real))).mul henergy)
    (fun K ↦ poisson_addOne_poincare_finiteSupport lambda (fK K)
      (supportTruncation_finiteSupport K f))

/-- The scalar Poisson Poincaré inequality can equivalently be written as a countable
series against the explicit Poisson weights. -/
theorem poisson_addOne_poincare_tsum
    (lambda : NNReal) (f : Nat → Real)
    (hf : MemLp f 2 (poissonMeasure lambda))
    (hdf : MemLp (addOne f) 2 (poissonMeasure lambda)) :
    variance f (poissonMeasure lambda) ≤
      (lambda : Real) *
        ∑' n : Nat, poissonWeight lambda n * (addOne f n) ^ 2 := by
  -- Rewrite the integrable squared increment with `integral_poissonMeasure` and simplify
  -- real scalar multiplication.
  have h := poisson_addOne_poincare lambda f hf hdf
  rw [integral_poissonMeasure] at h
  simpa only [poissonWeight, smul_eq_mul] using h

/-- At rate zero the Poisson law is concentrated at zero, so every square-integrable
sequence has zero variance. -/
theorem variance_poissonMeasure_zero
    (f : Nat → Real) (hf : MemLp f 2 (poissonMeasure 0)) :
    variance f (poissonMeasure 0) = 0 := by
  -- The singleton-mass formula identifies `poissonMeasure 0` with `Measure.dirac 0`;
  -- alternatively specialize the main inequality and combine with variance nonnegativity.
  rw [variance_eq_sub hf]
  rw [integral_poissonMeasure, integral_poissonMeasure]
  simp only [NNReal.coe_zero, neg_zero, Real.exp_zero, one_mul, smul_eq_mul]
  have hs (g : Nat → Real) :
      (∑' n : Nat, (0 : Real) ^ n / Nat.factorial n * g n) = g 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zero_pow hn]
      simp
  rw [hs, hs]
  simp

end

end CausalSmith.Substrate.PoissonAddOnePoincare
