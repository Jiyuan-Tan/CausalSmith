module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Algebra and coordinate oscillation of the categorical Gram denominator

The Gram is both a sum of squared residualized treatment weights and the
treatment-weighted residualized numerator. Adding a single observation to a
cell changes its Gram by a number in [0,1]; deleting and adding an observation
therefore gives a coordinate-replacement oscillation bound of one.
-/

public section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open scoped BigOperators

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- If [a cell has total count m and treated count t](hyp:m,t) with
[the treated count not exceeding the total](hyp:ht), then [adding one treated observation
increases the cell Gram contribution by an amount between zero and one](goal), even when the cell
was empty.

For positive m the increment equals (m-t)^2 / (m(m+1)); isolate m=0 first.
Use t≤m to rewrite natural subtraction before field arithmetic. -/
lemma cellGram_add_treated (m t : ℕ) (ht : t ≤ m) :
    0 ≤ cellGram (m + 1) (t + 1) - cellGram m t ∧
      cellGram (m + 1) (t + 1) - cellGram m t ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    simp [cellGram]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have htr : (t : ℝ) ≤ m := by exact_mod_cast ht
  have htpos : (0 : ℝ) ≤ t := by positivity
  have heq :
      cellGram (m + 1) (t + 1) - cellGram m t =
        ((m : ℝ) - t) ^ 2 / ((m : ℝ) * (m + 1)) := by
    simp [cellGram, hm, Nat.cast_sub ht, Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [heq]
  constructor
  · positivity
  · apply (div_le_iff₀ (mul_pos hmpos hmp)).2
    nlinarith

/-- If [a cell has total count m and treated count t](hyp:m,t) with
[the treated count not exceeding the total](hyp:ht), then [adding one control observation
increases the cell Gram contribution by an amount between zero and one](goal), even when the cell
was empty.

For positive m the increment equals t^2 / (m(m+1)); use symmetry with the
treated increment or clear the positive denominators directly. -/
lemma cellGram_add_control (m t : ℕ) (ht : t ≤ m) :
    0 ≤ cellGram (m + 1) t - cellGram m t ∧
      cellGram (m + 1) t - cellGram m t ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    simp [cellGram]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have htr : (t : ℝ) ≤ m := by exact_mod_cast ht
  have htpos : (0 : ℝ) ≤ t := by positivity
  have heq :
      cellGram (m + 1) t - cellGram m t =
        (t : ℝ) ^ 2 / ((m : ℝ) * (m + 1)) := by
    simp [cellGram, hm, Nat.cast_sub ht, Nat.cast_sub (Nat.le_trans ht (Nat.le_succ m)),
      Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [heq]
  constructor
  · positivity
  · apply (div_le_iff₀ (mul_pos hmpos hmp)).2
    nlinarith

omit [Fintype κ] in
/-- In [a design d of n cell-treatment pairs](hyp:n,d), [summing a real constant c](hyp:c) over
the observations in [a cell k](hyp:k) [gives the cell count of k times c](goal). -/
lemma sum_cell_constant {n : ℕ} (d : Fin n → κ × Bool) (k : κ) (c : ℝ) :
    (∑ i, if (d i).1 = k then c else 0) =
      (cellCount (fun i => (d i).1) k : ℝ) * c := by
  rw [cellCount, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

omit [Fintype κ] in
/-- In [a design d of n cell-treatment pairs](hyp:n,d), [summing the treatment indicators over the
observations in a cell k](hyp:k) [gives the treated count of k](goal). -/
lemma sum_cell_treatment {n : ℕ} (d : Fin n → κ × Bool) (k : κ) :
    (∑ i, if (d i).1 = k then (if (d i).2 then (1 : ℝ) else 0) else 0) =
      (treatedCount d k : ℝ) := by
  rw [treatedCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hk : (d i).1 = k <;> cases (d i).2 <;> simp [hk]

omit [Fintype κ] in
/-- In [a design d of n cell-treatment pairs](hyp:n,d), [the residualized treatment weights of the
observations in any cell k](hyp:k) [sum to zero](goal), including in empty cells. -/
lemma sum_residualWeight_cell {n : ℕ} (d : Fin n → κ × Bool) (k : κ) :
    (∑ i, if (d i).1 = k then residualWeight d i else 0) = 0 := by
  have heq :
      (∑ i, if (d i).1 = k then residualWeight d i else 0) =
        (treatedCount d k : ℝ) -
          (cellCount (fun i => (d i).1) k : ℝ) * treatmentFraction d k := by
    rw [← sum_cell_treatment d k, ← sum_cell_constant d k, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hk : (d i).1 = k <;> simp [residualWeight, hk]
  rw [heq]
  have ht := treatedCount_le d k
  unfold treatmentFraction
  split_ifs with hm
  · have ht0 : treatedCount d k = 0 := Nat.eq_zero_of_le_zero (hm ▸ ht)
    simp [hm, ht0]
  · have hm' : (cellCount (fun i => (d i).1) k : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
    ring

omit [Fintype κ] in
/-- In [a design d of n cell-treatment pairs](hyp:n,d), [summing the residualized treatment weight
times the treatment indicator over the observations in a cell k](hyp:k) [gives that cell's Gram
contribution](goal). -/
lemma sum_cell_residual_treatment {n : ℕ} (d : Fin n → κ × Bool) (k : κ) :
    (∑ i, if (d i).1 = k then
      residualWeight d i * (if (d i).2 then (1 : ℝ) else 0) else 0) =
      cellGram (cellCount (fun i => (d i).1) k) (treatedCount d k) := by
  have heq :
      (∑ i, if (d i).1 = k then
        residualWeight d i * (if (d i).2 then (1 : ℝ) else 0) else 0) =
        (treatedCount d k : ℝ) * (1 - treatmentFraction d k) := by
    rw [← sum_cell_treatment d k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hk : (d i).1 = k <;> cases ha : (d i).2 <;>
      simp [residualWeight, hk, ha]
  rw [heq]
  have ht := treatedCount_le d k
  unfold treatmentFraction cellGram
  split_ifs with hm
  · have ht0 : treatedCount d k = 0 := Nat.eq_zero_of_le_zero (hm ▸ ht)
    simp [ht0]
  · rw [Nat.cast_sub ht]
    have hm' : (cellCount (fun i => (d i).1) k : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

/-- For [every design d of n cell-treatment pairs](hyp:n,d), [the sum of the squared residualized
treatment weights equals the Gram denominator](goal). -/
lemma sum_residualWeight_sq {n : ℕ} (d : Fin n → κ × Bool) :
    (∑ i, residualWeight d i ^ 2) = gram d := by
  have hcell (k : κ) :
      (∑ i, if (d i).1 = k then residualWeight d i ^ 2 else 0) =
        cellGram (cellCount (fun i => (d i).1) k) (treatedCount d k) := by
    rw [← sum_cell_residual_treatment d k]
    have heq :
        (∑ i, if (d i).1 = k then residualWeight d i ^ 2 else 0) =
          (∑ i, if (d i).1 = k then
            residualWeight d i * (if (d i).2 then (1 : ℝ) else 0) else 0) -
          treatmentFraction d k *
            (∑ i, if (d i).1 = k then residualWeight d i else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hk : (d i).1 = k
      · cases ha : (d i).2 <;> simp [hk, residualWeight, ha] <;> ring
      · simp [hk]
    rw [heq, sum_residualWeight_cell, mul_zero, sub_zero]
  unfold gram
  simp_rw [← hcell]
  rw [Finset.sum_comm]
  simp

/-- For [every design d of n cell-treatment pairs](hyp:n,d), [the sum of the treatment indicators
weighted by their residualized treatment weights equals the Gram denominator](goal). -/
lemma sum_residualWeight_treatment {n : ℕ} (d : Fin n → κ × Bool) :
    (∑ i, residualWeight d i * (if (d i).2 then (1 : ℝ) else 0)) = gram d := by
  unfold gram
  simp_rw [← sum_cell_residual_treatment d]
  rw [Finset.sum_comm]
  simp

/-- For [every design d of n cell-treatment pairs](hyp:n,d), [the Gram denominator is at most
n/4](goal). -/
lemma gram_le_sample_quarter {n : ℕ} (d : Fin n → κ × Bool) :
    gram d ≤ (n : ℝ) / 4 := by
  have hcell (k : κ) :
      cellGram (cellCount (fun i => (d i).1) k) (treatedCount d k) ≤
        (cellCount (fun i => (d i).1) k : ℝ) / 4 := by
    have ht := treatedCount_le d k
    unfold cellGram
    split_ifs with hm
    · simp [hm]
    · rw [Nat.cast_sub ht]
      have hmpos : (0 : ℝ) < cellCount (fun i => (d i).1) k := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      apply (div_le_iff₀ hmpos).2
      nlinarith [sq_nonneg ((cellCount (fun i => (d i).1) k : ℝ) -
        2 * (treatedCount d k : ℝ))]
  calc
    gram d ≤ ∑ k, (cellCount (fun i => (d i).1) k : ℝ) / 4 :=
      Finset.sum_le_sum fun k _ => hcell k
    _ = (n : ℝ) / 4 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, sum_cellCount]

/-- If [cell total counts m and treated counts t](hyp:m,t) satisfy [treated count at most total
count in every cell](hyp:ht), then [adding one observation v](hyp:v) [increases the summed cell
Gram contributions by an amount between zero and one](goal). -/
lemma sum_cellGram_add (m t : κ → ℕ) (ht : ∀ k, t k ≤ m k) (v : κ × Bool) :
    0 ≤ (∑ k, cellGram (m k + if v.1 = k then 1 else 0)
      (t k + if v.1 = k ∧ v.2 = true then 1 else 0)) -
      (∑ k, cellGram (m k) (t k)) ∧
    (∑ k, cellGram (m k + if v.1 = k then 1 else 0)
      (t k + if v.1 = k ∧ v.2 = true then 1 else 0)) -
      (∑ k, cellGram (m k) (t k)) ≤ 1 := by
  have heq :
      (∑ k, cellGram (m k + if v.1 = k then 1 else 0)
        (t k + if v.1 = k ∧ v.2 = true then 1 else 0)) -
        (∑ k, cellGram (m k) (t k)) =
      cellGram (m v.1 + 1) (t v.1 + if v.2 then 1 else 0) -
        cellGram (m v.1) (t v.1) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ k, if k = v.1 then
          cellGram (m v.1 + 1) (t v.1 + if v.2 then 1 else 0) -
            cellGram (m v.1) (t v.1) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k = v.1
        · subst k
          cases v.2 <;> simp
        · simp [h, Ne.symm h]
      _ = _ := by simp
  rw [heq]
  cases ha : v.2
  · simpa [ha] using cellGram_add_control (m v.1) (t v.1) (ht v.1)
  · simpa [ha] using cellGram_add_treated (m v.1) (t v.1) (ht v.1)

/-- For [a design d of n cell-treatment pairs](hyp:n,d), replacing [the observation at a
coordinate i](hyp:i) by [any cell-treatment pair v](hyp:v) [changes the Gram denominator by at
most one in absolute value](goal).

Replacing one categorical observation changes the Gram denominator by at most one.

Remove coordinate i, forming counts over univ.erase i. Both old and new
designs add one observation to these common counts. If their cells differ,
the change is the difference of two increments in [0,1]. If the cells agree,
it is still the difference of two such increments. This sharper bound, not
the triangle-inequality bound two, is needed for the numerical risk corollary. -/
theorem gram_update_oscillation {n : ℕ} (d : Fin n → κ × Bool)
    (i : Fin n) (v : κ × Bool) :
    |gram d - gram (Function.update d i v)| ≤ 1 := by
  classical
  let s : Finset (Fin n) := Finset.univ.erase i
  let m (k : κ) : ℕ := ∑ j ∈ s, if (d j).1 = k then 1 else 0
  let t (k : κ) : ℕ := ∑ j ∈ s, if (d j).1 = k ∧ (d j).2 = true then 1 else 0
  have ht (k : κ) : t k ≤ m k := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hk : (d j).1 = k <;> by_cases ha : (d j).2 = true <;> simp [hk, ha]
  have hcounts (w : κ × Bool) (k : κ) :
      cellCount (fun j => (Function.update d i w j).1) k =
        m k + (if w.1 = k then 1 else 0) ∧
      treatedCount (Function.update d i w) k =
        t k + if w.1 = k ∧ w.2 = true then 1 else 0 := by
    constructor
    · rw [cellCount, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update_of_ne hji]
    · rw [treatedCount, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update_of_ne hji]
  have hg (w : κ × Bool) :
      gram (Function.update d i w) =
        ∑ k, cellGram (m k + if w.1 = k then 1 else 0)
          (t k + if w.1 = k ∧ w.2 = true then 1 else 0) := by
    unfold gram
    apply Finset.sum_congr rfl
    intro k hk
    rw [(hcounts w k).1, (hcounts w k).2]
  have hold := sum_cellGram_add m t ht (d i)
  have hnew := sum_cellGram_add m t ht v
  rw [← hg (d i), Function.update_eq_self] at hold
  rw [← hg v] at hnew
  rw [abs_le]
  constructor <;> linarith [hold.1, hold.2, hnew.1, hnew.2]

end Causalean.Stat.Sample.Stratified.TreatmentRegression
