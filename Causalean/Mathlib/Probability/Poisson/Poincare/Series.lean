/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Series algebra for the Poisson add-one inequality

This module isolates the explicit Poisson weights, their size-bias shift, two nonnegative
upper-triangle reindexings, and the finite telescoping/Cauchy–Schwarz estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.PoissonAddOnePoincare

noncomputable section

/-- A [nonnegative Poisson rate](hyp:lambda) and [count value](hyp:n) determine [the real Poisson probability mass at that count](goal), given by [the standard exponential--factorial mass formula](step:1). -/
def poissonWeight (lambda : NNReal) (n : Nat) : Real :=
  Real.exp (-(lambda : Real)) * (lambda : Real) ^ n / Nat.factorial n

/-- At [a nonnegative Poisson rate](hyp:lambda), the mass at [any count](hyp:n) [is nonnegative](goal). -/
lemma poissonWeight_nonneg (lambda : NNReal) (n : Nat) :
    0 ≤ poissonWeight lambda n := by
  unfold poissonWeight
  positivity

/-- At [a nonnegative Poisson rate](hyp:lambda), [the Poisson probability masses sum to one](goal). -/
lemma poissonWeight_hasSum_one (lambda : NNReal) :
    HasSum (poissonWeight lambda) 1 := by
  change HasSum
    (fun n ↦ Real.exp (-(lambda : Real)) * (lambda : Real) ^ n / Nat.factorial n) 1
  simpa using ProbabilityTheory.hasSum_one_poissonMeasure lambda

/-- At [a nonnegative Poisson rate](hyp:lambda), the singleton probability of [a count](hyp:n) [equals its explicit real Poisson mass](goal). -/
lemma poissonWeight_eq_measureReal_singleton (lambda : NNReal) (n : Nat) :
    poissonWeight lambda n = (poissonMeasure lambda).real {n} := by
  simpa only [poissonWeight] using
    (ProbabilityTheory.poissonMeasure_real_singleton lambda n).symm

/-- At [a nonnegative Poisson rate](hyp:lambda) and [a count](hyp:n), [successive Poisson masses obey the size-bias shift identity](goal). -/
lemma poissonWeight_succ_shift (lambda : NNReal) (n : Nat) :
    ((n + 1 : Nat) : Real) * poissonWeight lambda (n + 1) =
      (lambda : Real) * poissonWeight lambda n := by
  -- Unfold the weight, rewrite `Nat.factorial_succ`, and cancel the positive successor cast;
  -- no division by `lambda` is needed, so the same calculation covers `lambda = 0`.
  simp only [poissonWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp

/-- At [a nonnegative Poisson rate](hyp:lambda), a [positive count](hyp:hn) [satisfies the predecessor form of the Poisson size-bias shift identity](goal). -/
lemma poissonWeight_shift (lambda : NNReal) {n : Nat} (hn : 0 < n) :
    (n : Real) * poissonWeight lambda n =
      (lambda : Real) * poissonWeight lambda (n - 1) := by
  -- Write `n` as `(n - 1) + 1` using `hn`, then apply the successor shift identity.
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa only [h] using poissonWeight_succ_shift lambda (n - 1)

/-- For [a nonnegative doubly indexed series](hyp:a), [summing its strict upper triangle by endpoints equals summing its finite rows](goal). -/
theorem ENNReal_tsum_lt_eq_tsum_fin (a : Nat → Nat → ENNReal) :
    (∑' m : Nat, ∑' n : Nat, if n < m then a n m else 0) =
      ∑' m : Nat, ∑' n : Fin m, a n m := by
  -- Convert the finite `Fin m` tsum with `Finset.tsum_subtype`, then use indicator/subtype
  -- reindexing. ENNReal Tonelli permits every exchange without a summability premise.
  congr 1
  funext m
  calc
    (∑' n : Nat, if n < m then a n m else 0) =
        ∑' n : Nat, Set.indicator {n | n < m} (fun n => a n m) n := by
      congr 1
      funext n
      simp only [Set.indicator_apply]
      rfl
    _ = ∑' n : {n : Nat // n < m}, a n m :=
      (tsum_subtype {n : Nat | n < m} (fun n => a n m)).symm
    _ = ∑' n : Fin m, a n m := by
      symm
      simpa using (Fin.equivSubtype.tsum_eq
        (fun n : {n : Nat // n < m} => a n m))

/-- For [a nonnegative doubly indexed series](hyp:a), [the strict upper triangle has equal sums under the gap and endpoint parametrizations](goal). -/
theorem ENNReal_tsum_upperTriangle_gap (a : Nat → Nat → ENNReal) :
    (∑' n : Nat, ∑' k : Nat, a n (n + k + 1)) =
      ∑' m : Nat, ∑' n : Fin m, a n m := by
  -- Reindex the countable type of pairs `(n,k)` by the strict triangle
  -- `Σ m, Fin m`, via `(n,k) ↦ ⟨n+k+1, n⟩`, and use `Equiv.tsum_eq`.
  let e : Nat × Nat ≃ Σ m : Nat, Fin m :=
    { toFun := fun p => ⟨p.1 + p.2 + 1, ⟨p.1, by omega⟩⟩
      invFun := fun q => (q.2.1, q.1 - q.2.1 - 1)
      left_inv := by
        intro p
        apply Prod.ext
        · rfl
        · simp only
          omega
      right_inv := by
        intro q
        have h : q.2.1 + (q.1 - q.2.1 - 1) + 1 = q.1 := by omega
        apply Sigma.eq h
        dsimp
        apply Fin.ext
        have cast_val {r s : Nat} (hrs : r = s) (i : Fin r) :
            (hrs ▸ i).val = i.val := by
          subst s
          rfl
        exact cast_val h _ }
  calc
    (∑' n : Nat, ∑' k : Nat, a n (n + k + 1)) =
        ∑' p : Nat × Nat, a p.1 (p.1 + p.2 + 1) :=
      ENNReal.tsum_prod.symm
    _ = ∑' q : Σ m : Nat, Fin m, a q.2 q.1 := by
      rw [← e.tsum_eq (fun q : Σ m : Nat, Fin m => a q.2 q.1)]
      rfl
    _ = ∑' m : Nat, ∑' n : Fin m, a n m :=
      ENNReal.tsum_sigma (fun (m : Nat) (n : Fin m) => a n m)

/-- For [a real sequence](hyp:f) and [ordered endpoints](hyp:hnm), [the squared endpoint difference is bounded by path length times the sum of squared adjacent increments](goal). -/
theorem sq_sub_le_nat_sub_mul_sum_sq_step
    (f : Nat → Real) {n m : Nat} (hnm : n ≤ m) :
    (f m - f n) ^ 2 ≤
      (m - n : Nat) * ∑ k ∈ Finset.Ico n m, (f (k + 1) - f k) ^ 2 := by
  -- Rewrite the left difference by `Finset.sum_Ico_sub`; apply finite Cauchy–Schwarz to
  -- the increments paired with the constant-one vector, and simplify its squared norm.
  rw [← Finset.sum_Ico_sub f hnm]
  calc
    (∑ k ∈ Finset.Ico n m, (f (k + 1) - f k)) ^ 2 =
        (∑ k ∈ Finset.Ico n m, (f (k + 1) - f k) * 1) ^ 2 := by simp
    _ ≤ (∑ k ∈ Finset.Ico n m, (f (k + 1) - f k) ^ 2) *
          ∑ k ∈ Finset.Ico n m, (1 : Real) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (m - n : Nat) * ∑ k ∈ Finset.Ico n m, (f (k + 1) - f k) ^ 2 := by
      simp [Nat.card_Ico]
      ring

end

end Causalean.Mathlib.Probability.PoissonAddOnePoincare
