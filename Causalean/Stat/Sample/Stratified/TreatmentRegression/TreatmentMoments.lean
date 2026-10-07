module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Finite conditional treatment moments

Explicit enumeration of independent Boolean assignments at fixed categorical
labels. The expected cell Gram is (N-1)_+ times pi(1-pi), including empty and
singleton cells. Bernoulli design moments in Causalean provide the independent
one- and two-coordinate expectations; these statements expose the required
count and denominator algebra.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open scoped BigOperators

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- [The conditional weight of a treatment assignment](goal) [a of n Boolean treatments](hyp:n,a)
at [fixed cell labels x](hyp:x), under [cell propensities p](hyp:p), is the product over
observations of p at the observation's cell when it is treated and one minus that value when it
is not. -/
def assignmentWeight {n : ℕ} (p : κ → ℝ) (x : Fin n → κ)
    (a : Fin n → Bool) : ℝ :=
  ∏ i, if a i then p (x i) else 1 - p (x i)

omit [Fintype κ] [DecidableEq κ] in
/-- For [arbitrary real cell weights p](hyp:p), [fixed labels x of n observations](hyp:n,x) and
[real coordinate functions g](hyp:g), [the assignment-weighted sum of the product of the
coordinate functions factors into the product of the per-coordinate two-point averages](goal). -/
private lemma assignment_prod_mean {n : ℕ} (p : κ → ℝ) (x : Fin n → κ)
    (g : Fin n → Bool → ℝ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a * ∏ i, g i (a i)) =
      ∏ i, (p (x i) * g i true + (1 - p (x i)) * g i false) := by
  classical
  simp only [assignmentWeight, ← Finset.prod_mul_distrib]
  have h := Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
    (fun i b => (if b then p (x i) else 1 - p (x i)) * g i b)
  rw [Fintype.piFinset_univ] at h
  simpa [add_comm] using h

omit [Fintype κ] [DecidableEq κ] in
/-- For [arbitrary real cell weights p](hyp:p), [fixed labels x of n observations](hyp:n,x),
[a coordinate i](hyp:i) and [a real function g of one treatment](hyp:g),
[the assignment-weighted sum of g at coordinate i equals its two-point average
p·g(true) + (1 − p)·g(false) at that coordinate's cell](goal). -/
private lemma assignment_coord_mean {n : ℕ} (p : κ → ℝ) (x : Fin n → κ)
    (i : Fin n) (g : Bool → ℝ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a * g (a i)) =
      p (x i) * g true + (1 - p (x i)) * g false := by
  classical
  have h := assignment_prod_mean p x (fun j b => if j = i then g b else 1)
  simp only [Fintype.prod_ite_eq'] at h
  have hf (j : Fin n) :
      p (x j) * (if j = i then g true else 1) +
        (1 - p (x j)) * (if j = i then g false else 1) =
      if j = i then p (x i) * g true + (1 - p (x i)) * g false else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa only [hf, Fintype.prod_ite_eq'] using h

omit [Fintype κ] [DecidableEq κ] in
/-- For [arbitrary real cell weights p](hyp:p), [fixed labels x of n observations](hyp:n,x),
[two coordinates i and j](hyp:i,j) that [are distinct](hyp:hij), and
[real functions g and h of one treatment](hyp:g,h), [the assignment-weighted sum of
g at coordinate i times h at coordinate j is the product of their two-point averages](goal). -/
private lemma assignment_pair_mean {n : ℕ} (p : κ → ℝ) (x : Fin n → κ)
    (i j : Fin n) (hij : i ≠ j) (g h : Bool → ℝ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a * (g (a i) * h (a j))) =
      (p (x i) * g true + (1 - p (x i)) * g false) *
      (p (x j) * h true + (1 - p (x j)) * h false) := by
  classical
  have H := assignment_prod_mean p x
    (fun l b => (if l = i then g b else 1) * (if l = j then h b else 1))
  simp only [Finset.prod_mul_distrib, Fintype.prod_ite_eq'] at H
  have hf (l : Fin n) :
      p (x l) * ((if l = i then g true else 1) * (if l = j then h true else 1)) +
        (1 - p (x l)) * ((if l = i then g false else 1) * (if l = j then h false else 1)) =
      (if l = i then p (x i) * g true + (1 - p (x i)) * g false else 1) *
      (if l = j then p (x j) * h true + (1 - p (x j)) * h false else 1) := by
    by_cases hi : l = i <;> by_cases hj : l = j <;> simp_all
  simpa only [hf, Finset.prod_mul_distrib, Fintype.prod_ite_eq'] using H

omit [Fintype κ] [DecidableEq κ] in
/-- For [arbitrary real cell weights p](hyp:p) and [fixed labels x of n observations](hyp:n,x),
[the conditional weights of all Boolean treatment assignments sum to one](goal). -/
lemma sum_assignmentWeight {n : ℕ} (p : κ → ℝ) (x : Fin n → κ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a) = 1 := by
  have h := assignment_prod_mean p x (fun _ _ => 1)
  simpa using h

omit [Fintype κ] in
/-- For [arbitrary real cell weights p](hyp:p) and [fixed labels x of n observations](hyp:n,x),
and [a cell k](hyp:k), [the assignment-weighted sum of the treated count of k equals the cell count
of k times p at k](goal).

Rewrite assignmentWeight using bernoulliDesign and apply its one-coordinate
expectation to the finite sum of treatment indicators. The identity is
polynomial and holds even without propensity bounds. -/
lemma assignment_treatedCount_mean {n : ℕ} (p : κ → ℝ) (x : Fin n → κ) (k : κ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a *
      (treatedCount (fun i => (x i, a i)) k : ℝ)) =
      (cellCount x k : ℝ) * p k := by
  classical
  have hc (a : Fin n → Bool) :
      (treatedCount (fun i => (x i, a i)) k : ℝ) =
        ∑ i, if x i = k then (if a i then (1 : ℝ) else 0) else 0 := by
    simp only [treatedCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x i = k <;> by_cases ha : a i = true <;> simp [hx, ha]
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (i : Fin n) :
      (∑ a : Fin n → Bool, assignmentWeight p x a *
        (if x i = k then (if a i then (1 : ℝ) else 0) else 0)) =
      if x i = k then p k else 0 := by
    by_cases hx : x i = k
    · simpa [hx] using assignment_coord_mean p x i (fun b => if b then (1 : ℝ) else 0)
    · simp [hx]
  simp_rw [hm]
  simp only [cellCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]

omit [Fintype κ] in
/-- For [arbitrary real cell weights p](hyp:p) and [fixed labels x of n observations](hyp:n,x),
and [a cell k](hyp:k), [the assignment-weighted sum of the treated count of k times its control
count equals N(N − 1)·p(1 − p), where N is the cell count of k, p is the weight at k, and N − 1
is truncated at zero](goal); it is zero in empty and singleton cells.

Expand into ordered distinct coordinate pairs, using Boolean idempotence on
the diagonal and product moments off it. Natural subtraction is harmless
because treatedCount_le holds for every assignment. -/
lemma assignment_treated_control_mean {n : ℕ} (p : κ → ℝ)
    (x : Fin n → κ) (k : κ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a *
      ((treatedCount (fun i => (x i, a i)) k : ℝ) *
        (cellCount x k - treatedCount (fun i => (x i, a i)) k : ℕ))) =
      (cellCount x k : ℝ) * (cellCount x k - 1 : ℕ) * p k * (1 - p k) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = k)
  have hs : S.card = cellCount x k := by
    simp [S, cellCount]
  have hx {i : Fin n} (hi : i ∈ S) : x i = k := (Finset.mem_filter.mp hi).2
  have ht (a : Fin n → Bool) :
      (treatedCount (fun i => (x i, a i)) k : ℝ) =
        ∑ i ∈ S, if a i then (1 : ℝ) else 0 := by
    simp only [treatedCount, Nat.cast_sum, Finset.sum_filter, S]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i = k <;> by_cases ha : a i = true <;> simp [hi, ha]
  have hc (a : Fin n → Bool) :
      (cellCount x k - treatedCount (fun i => (x i, a i)) k : ℕ) =
        (∑ i ∈ S, if a i then (0 : ℝ) else 1) := by
    rw [Nat.cast_sub (treatedCount_le (fun i => (x i, a i)) k), ht, ← hs]
    have hcard : (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp
    rw [hcard, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ha : a i = true <;> simp [ha]
  simp_rw [ht, hc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ S) :
      (∑ a : Fin n → Bool, assignmentWeight p x a *
        ((if a i then (1 : ℝ) else 0) * (if a j then (0 : ℝ) else 1))) =
      if j = i then 0 else p k * (1 - p k) := by
    by_cases hij : j = i
    · subst j
      have hz (a : Fin n → Bool) :
          (if a i then (1 : ℝ) else 0) * (if a i then (0 : ℝ) else 1) = 0 := by
        by_cases ha : a i = true <;> simp [ha]
      simp [hz]
    · simpa [hx hi, hx hj, hij] using assignment_pair_mean p x i j (Ne.symm hij)
        (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (0 : ℝ) else 1)
  have hiMean (i : Fin n) (hi : i ∈ S) :
      (∑ j ∈ S, ∑ a : Fin n → Bool, assignmentWeight p x a *
        ((if a i then (1 : ℝ) else 0) * (if a j then (0 : ℝ) else 1))) =
      (S.card - 1 : ℕ) * (p k * (1 - p k)) := by
    calc
      _ = ∑ j ∈ S, if j = i then (0 : ℝ) else p k * (1 - p k) :=
        Finset.sum_congr rfl (hm i hi)
      _ = _ := by
        rw [← Finset.sum_erase_add _ _ hi]
        simp only [ite_true, add_zero]
        calc
          _ = ∑ _j ∈ S.erase i, p k * (1 - p k) :=
            Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))
          _ = _ := by simp [Finset.card_erase_of_mem hi]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, ∑ a : Fin n → Bool, assignmentWeight p x a *
        ((if a i then (1 : ℝ) else 0) * (if a j then (0 : ℝ) else 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, (S.card - 1 : ℕ) * (p k * (1 - p k)) :=
      Finset.sum_congr rfl hiMean
    _ = _ := by simp [hs]; ring

/-- For [arbitrary real cell weights p](hyp:p) and [fixed labels x of n observations](hyp:n,x),
[the assignment-weighted sum of the Gram denominator equals the sum over cells of
(N − 1)·p(1 − p)](goal), where N is the cell count, N − 1 is truncated at zero, and p is the
weight at that cell — the repeated counts times the Bernoulli variances. -/
theorem assignment_gram_mean {n : ℕ} (p : κ → ℝ) (x : Fin n → κ) :
    (∑ a : Fin n → Bool, assignmentWeight p x a * gram (fun i => (x i, a i))) =
      ∑ k, (cellCount x k - 1 : ℕ) * p k * (1 - p k) := by
  classical
  simp only [gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hm : cellCount x k = 0
  · simp [cellGram, hm]
  · have hmR : (cellCount x k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simp only [cellGram, hm, if_false]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, assignment_treated_control_mean]
    field_simp


/-- Given [fixed labels x](hyp:x) and [cell propensities p](hyp:p), if
[ε is an overlap margin](hyp:epsilon) and
[every occupied cell has propensity between ε and 1 − ε](hyp:hoverlap), then
[the assignment-weighted sum of the Gram denominator is at least ε(1 − ε) times the repeat
count of the labels](goal).

Propensity overlap on cells appearing in the fixed labels lower bounds
the conditional Gram mean by epsilon(1-epsilon) times the repeat count. -/
theorem assignment_gram_mean_lower {n : ℕ} (p : κ → ℝ) (x : Fin n → κ)
    (epsilon : ℝ)
    (hoverlap : ∀ k, 0 < cellCount x k → epsilon ≤ p k ∧ p k ≤ 1 - epsilon) :
    epsilon * (1 - epsilon) * (repeatCount x : ℝ) ≤
      ∑ a : Fin n → Bool, assignmentWeight p x a * gram (fun i => (x i, a i)) := by
  rw [assignment_gram_mean]
  simp only [repeatCount, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : cellCount x k = 0
  · simp [hk]
  · obtain ⟨hl, hu⟩ := hoverlap k (Nat.pos_of_ne_zero hk)
    have hv : epsilon * (1 - epsilon) ≤ p k * (1 - p k) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)]
    have hn : (0 : ℝ) ≤ (cellCount x k - 1 : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hv hn]

end Causalean.Stat.Sample.Stratified.TreatmentRegression
