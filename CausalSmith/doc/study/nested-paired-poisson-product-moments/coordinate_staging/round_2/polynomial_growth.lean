/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments.Flattening
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Polynomial moments and L² closure for nested paired Poisson arrays

Finite Poisson products have moments of every natural order.  This module packages that fact as
a total-count moment theorem and a polynomial-growth criterion for a statistic and each of its
two add-one increments.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments

noncomputable section

open Causalean.Mathlib.Probability.PoissonAddOnePoincare

/-- A [nested array of count pairs](hyp:x) determines [its total count](goal), given by
[summing both counts across every finite array cell](step:1). -/
def nestedPairedTotalCount
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (x : iota → kappa → Nat × Nat) : Nat :=
  ∑ i, ∑ j, ((x i j).1 + (x i j).2)

private theorem nestedPairedTotalCount_update_fst
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (x : iota → kappa → Nat × Nat) (i : iota) (j : kappa) :
    nestedPairedTotalCount
      (Function.update x i
        (Function.update (x i) j ((x i j).1 + 1, (x i j).2))) =
      nestedPairedTotalCount x + 1 := by
  let upd := Function.update x i
    (Function.update (x i) j ((x i j).1 + 1, (x i j).2))
  let z := nestedPairedPoissonFlattening iota kappa x
  let p : NestedPairedPoissonIndex iota kappa := ⟨i, ⟨j, 0⟩⟩
  have htotal_flat (y : iota → kappa → Nat × Nat) :
      nestedPairedTotalCount y =
        ∑ q, nestedPairedPoissonFlattening iota kappa y q := by
    simp only [nestedPairedTotalCount]
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_sigma]
    simp [Fin.sum_univ_two]
  have hu := nestedPairedPoissonUnflattening_update_fst z i j
  have hz : nestedPairedPoissonUnflattening iota kappa z = x :=
    (nestedPairedPoissonUnflattening iota kappa).apply_symm_apply x
  have hu' : nestedPairedPoissonUnflattening iota kappa
      (Function.update z p (z p + 1)) = upd := by
    simpa [p, upd, hz, z] using hu
  have hflat : nestedPairedPoissonFlattening iota kappa upd =
      Function.update z p (z p + 1) := by
    rw [← hu']
    exact (nestedPairedPoissonUnflattening iota kappa).symm_apply_apply _
  rw [htotal_flat upd, hflat]
  rw [show (∑ q, Function.update z p (z p + 1) q) =
      (z p + 1) + ∑ q ∈ Finset.univ \ {p}, z q by
    simpa using Finset.sum_update_of_mem (s := Finset.univ) (i := p)
      (Finset.mem_univ p) z (z p + 1)]
  rw [htotal_flat x]
  change _ = (∑ q, z q) + 1
  rw [show (∑ q, z q) = z p + ∑ q ∈ Finset.univ \ {p}, z q by
    simpa using Finset.sum_update_of_mem (s := Finset.univ) (i := p)
      (Finset.mem_univ p) z (z p)]
  omega

private theorem nestedPairedTotalCount_update_snd
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (x : iota → kappa → Nat × Nat) (i : iota) (j : kappa) :
    nestedPairedTotalCount
      (Function.update x i
        (Function.update (x i) j ((x i j).1, (x i j).2 + 1))) =
      nestedPairedTotalCount x + 1 := by
  let upd := Function.update x i
    (Function.update (x i) j ((x i j).1, (x i j).2 + 1))
  let z := nestedPairedPoissonFlattening iota kappa x
  let p : NestedPairedPoissonIndex iota kappa := ⟨i, ⟨j, 1⟩⟩
  have htotal_flat (y : iota → kappa → Nat × Nat) :
      nestedPairedTotalCount y =
        ∑ q, nestedPairedPoissonFlattening iota kappa y q := by
    simp only [nestedPairedTotalCount]
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_sigma]
    simp [Fin.sum_univ_two]
  have hu := nestedPairedPoissonUnflattening_update_snd z i j
  have hz : nestedPairedPoissonUnflattening iota kappa z = x :=
    (nestedPairedPoissonUnflattening iota kappa).apply_symm_apply x
  have hu' : nestedPairedPoissonUnflattening iota kappa
      (Function.update z p (z p + 1)) = upd := by
    simpa [p, upd, hz, z] using hu
  have hflat : nestedPairedPoissonFlattening iota kappa upd =
      Function.update z p (z p + 1) := by
    rw [← hu']
    exact (nestedPairedPoissonUnflattening iota kappa).symm_apply_apply _
  rw [htotal_flat upd, hflat]
  rw [show (∑ q, Function.update z p (z p + 1) q) =
      (z p + 1) + ∑ q ∈ Finset.univ \ {p}, z q by
    simpa using Finset.sum_update_of_mem (s := Finset.univ) (i := p)
      (Finset.mem_univ p) z (z p + 1)]
  rw [htotal_flat x]
  change _ = (∑ q, z q) + 1
  rw [show (∑ q, z q) = z p + ∑ q ∈ Finset.univ \ {p}, z q by
    simpa using Finset.sum_update_of_mem (s := Finset.univ) (i := p)
      (Finset.mem_univ p) z (z p)]
  omega

/-- A [nonnegative Poisson rate](hyp:lambda) and [natural-number exponent](hyp:degree) have
[an integrable real-valued count power under the Poisson law](goal). -/
theorem integrable_natCast_pow_poissonMeasure (lambda : NNReal) (degree : Nat) :
    Integrable (fun n : Nat => (n : Real) ^ degree) (poissonMeasure lambda) := by
  apply integrable_pow_of_integrable_exp_mul (t := 1) (by norm_num)
  · rw [integrable_poissonMeasure_iff]
    have h :=
      (Real.summable_pow_div_factorial ((lambda : Real) * Real.exp 1)).mul_left
        (Real.exp (-(lambda : Real)))
    simpa [Real.norm_eq_abs, Real.abs_exp, Real.exp_nat_mul, mul_pow, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using h
  · refine Integrable.mono
      (integrable_const (μ := poissonMeasure lambda) (c := (1 : Real))) ?_
      (ae_of_all _ fun n => ?_)
    · fun_prop
    · simp only [Real.norm_eq_abs, Real.abs_exp, norm_one]
      rw [Real.exp_le_one_iff]
      norm_num

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂) and a
[natural-number exponent](hyp:degree) have
[an integrable power of the nested array's total count](goal). -/
theorem integrable_nestedPairedTotalCount_pow
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal) (degree : Nat) :
    Integrable
      (fun x : iota → kappa → Nat × Nat =>
        (nestedPairedTotalCount x : Real) ^ degree)
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
  let rates := nestedPairedPoissonRates lambda₁ lambda₂
  let S : (NestedPairedPoissonIndex iota kappa → Nat) → Real :=
    fun z => ∑ p, (z p : Real)
  have hpos : Integrable (fun z => Real.exp (1 * S z)) (poissonPi rates) := by
    have hcoord : ∀ p, Integrable (fun n : Nat => Real.exp (n : Real))
        (poissonMeasure (rates p)) := by
      intro p
      rw [integrable_poissonMeasure_iff]
      have h :=
        (Real.summable_pow_div_factorial
          ((rates p : Real) * Real.exp 1)).mul_left
            (Real.exp (-(rates p : Real)))
      simpa [Real.norm_eq_abs, Real.abs_exp, Real.exp_nat_mul, mul_pow, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using h
    change Integrable _ (Measure.pi fun p => poissonMeasure (rates p))
    simpa [S, one_mul, Real.exp_sum] using
      (Integrable.fintype_prod (𝕜 := Real) hcoord)
  have hneg : Integrable (fun z => Real.exp (-1 * S z)) (poissonPi rates) := by
    change Integrable _ (Measure.pi fun p => poissonMeasure (rates p))
    refine Integrable.mono
      (integrable_const (μ := Measure.pi fun p => poissonMeasure (rates p))
        (c := (1 : Real)))
      (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [Real.norm_eq_abs, Real.abs_exp, norm_one]
    rw [Real.exp_le_one_iff]
    have hs : 0 ≤ ∑ p, (z p : Real) := by positivity
    dsimp [S]
    linarith
  have hflat : Integrable (fun z => (S z) ^ degree) (poissonPi rates) :=
    integrable_pow_of_integrable_exp_mul (t := 1) (by norm_num) hpos hneg degree
  have hcomp :=
    (measurePreserving_nestedPairedPoissonFlattening lambda₁ lambda₂)
      |>.integrable_comp_of_integrable hflat
  convert hcomp using 1
  funext x
  congr 1
  simp only [nestedPairedTotalCount, S, Nat.cast_sum, Nat.cast_add]
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_sigma]
  simp [Fin.sum_univ_two]

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂), a
[measurable real-valued nested-array statistic](hyp:F,hF), a
[nonnegative growth constant](hyp:C,hC), and a [polynomial degree](hyp:degree) whose
[absolute value obeys the stated total-count growth bound](hyp:hbound) give
[a square-integrable statistic under the nested paired-count law](goal). -/
theorem memLp_nestedPairedPoisson_of_polynomial_bound
    {iota kappa : Type*}
    [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (F : (iota → kappa → Nat × Nat) → Real)
    (hF : Measurable F) (C : Real) (degree : Nat)
    (hC : 0 ≤ C)
    (hbound : ∀ x, |F x| ≤ C * (1 + (nestedPairedTotalCount x : Real)) ^ degree) :
    MemLp F 2 (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
  let T : (iota → kappa → Nat × Nat) → Real :=
    fun x => (nestedPairedTotalCount x : Real)
  have hmoment : Integrable (fun x => (T x) ^ (2 * degree))
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
    simpa [T] using
      integrable_nestedPairedTotalCount_pow lambda₁ lambda₂ (2 * degree)
  have hone : Integrable (fun _ : iota → kappa → Nat × Nat => (1 : Real))
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
    simpa using integrable_nestedPairedTotalCount_pow lambda₁ lambda₂ 0
  have hshift : Integrable (fun x => (1 + T x) ^ (2 * degree))
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
    refine Integrable.mono
      ((hone.add hmoment).const_mul ((2 : Real) ^ (2 * degree - 1)))
      (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (add_nonneg (by positivity) (pow_nonneg (by positivity) _)))]
    simpa only [Pi.add_apply, one_pow] using
      (add_pow_le (a := (1 : Real)) (b := T x) (by positivity) (by positivity)
        (2 * degree))
  refine (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 ?_
  refine Integrable.mono (hshift.const_mul (C ^ 2))
    (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (pow_nonneg (by positivity) _))]
  calc
    F x ^ 2 = |F x| ^ 2 := (sq_abs (F x)).symm
    _ ≤ (C * (1 + T x) ^ degree) ^ 2 := by gcongr; exact hbound x
    _ = C ^ 2 * (1 + T x) ^ (2 * degree) := by
      simp [mul_pow, ← pow_mul, Nat.mul_comm]

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂), a
[measurable real-valued nested-array statistic](hyp:F,hF), a
[nonnegative growth constant](hyp:C,hC), a [polynomial degree](hyp:degree), its
[total-count growth bound](hyp:hbound), and a [selected cell](hyp:i,j) give
[a square-integrable first-count add-one increment](goal). -/
theorem memLp_nestedPairAddOneFst_of_polynomial_bound
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (F : (iota → kappa → Nat × Nat) → Real)
    (hF : Measurable F) (C : Real) (degree : Nat)
    (hC : 0 ≤ C)
    (hbound : ∀ x, |F x| ≤ C * (1 + (nestedPairedTotalCount x : Real)) ^ degree)
    (i : iota) (j : kappa) :
    MemLp (nestedPairAddOneFst i j F) 2
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
  let upd : (iota → kappa → Nat × Nat) → (iota → kappa → Nat × Nat) :=
    fun x => Function.update x i
      (Function.update (x i) j ((x i j).1 + 1, (x i j).2))
  apply memLp_nestedPairedPoisson_of_polynomial_bound lambda₁ lambda₂
    (nestedPairAddOneFst i j F) (measurable_of_countable _)
    (2 * C * 2 ^ degree) degree (by positivity)
  intro x
  change |F (upd x) - F x| ≤
    (2 * C * 2 ^ degree) * (1 + (nestedPairedTotalCount x : Real)) ^ degree
  have hcount : nestedPairedTotalCount (upd x) = nestedPairedTotalCount x + 1 := by
    exact nestedPairedTotalCount_update_fst x i j
  have hbase_update :
      1 + (nestedPairedTotalCount (upd x) : Real) ≤
        2 * (1 + (nestedPairedTotalCount x : Real)) := by
    rw [hcount, Nat.cast_add, Nat.cast_one]
    have ht : 0 ≤ (nestedPairedTotalCount x : Real) := by positivity
    linarith
  have hbase_old :
      1 + (nestedPairedTotalCount x : Real) ≤
        2 * (1 + (nestedPairedTotalCount x : Real)) := by
    have ht : 0 ≤ (nestedPairedTotalCount x : Real) := by positivity
    linarith
  calc
    |F (upd x) - F x| ≤ |F (upd x)| + |F x| := abs_sub _ _
    _ ≤ C * (1 + (nestedPairedTotalCount (upd x) : Real)) ^ degree +
        C * (1 + (nestedPairedTotalCount x : Real)) ^ degree :=
      add_le_add (hbound (upd x)) (hbound x)
    _ ≤ C * (2 * (1 + (nestedPairedTotalCount x : Real))) ^ degree +
        C * (2 * (1 + (nestedPairedTotalCount x : Real))) ^ degree := by
      gcongr
    _ = (2 * C * 2 ^ degree) *
        (1 + (nestedPairedTotalCount x : Real)) ^ degree := by
      simp [mul_pow]
      ring

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂), a
[measurable real-valued nested-array statistic](hyp:F,hF), a
[nonnegative growth constant](hyp:C,hC), a [polynomial degree](hyp:degree), its
[total-count growth bound](hyp:hbound), and a [selected cell](hyp:i,j) give
[a square-integrable second-count add-one increment](goal). -/
theorem memLp_nestedPairAddOneSnd_of_polynomial_bound
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (F : (iota → kappa → Nat × Nat) → Real)
    (hF : Measurable F) (C : Real) (degree : Nat)
    (hC : 0 ≤ C)
    (hbound : ∀ x, |F x| ≤ C * (1 + (nestedPairedTotalCount x : Real)) ^ degree)
    (i : iota) (j : kappa) :
    MemLp (nestedPairAddOneSnd i j F) 2
      (nestedPairedPoissonMeasure lambda₁ lambda₂) := by
  let upd : (iota → kappa → Nat × Nat) → (iota → kappa → Nat × Nat) :=
    fun x => Function.update x i
      (Function.update (x i) j ((x i j).1, (x i j).2 + 1))
  apply memLp_nestedPairedPoisson_of_polynomial_bound lambda₁ lambda₂
    (nestedPairAddOneSnd i j F) (measurable_of_countable _)
    (2 * C * 2 ^ degree) degree (by positivity)
  intro x
  change |F (upd x) - F x| ≤
    (2 * C * 2 ^ degree) * (1 + (nestedPairedTotalCount x : Real)) ^ degree
  have hcount : nestedPairedTotalCount (upd x) = nestedPairedTotalCount x + 1 := by
    exact nestedPairedTotalCount_update_snd x i j
  have hbase_update :
      1 + (nestedPairedTotalCount (upd x) : Real) ≤
        2 * (1 + (nestedPairedTotalCount x : Real)) := by
    rw [hcount, Nat.cast_add, Nat.cast_one]
    have ht : 0 ≤ (nestedPairedTotalCount x : Real) := by positivity
    linarith
  have hbase_old :
      1 + (nestedPairedTotalCount x : Real) ≤
        2 * (1 + (nestedPairedTotalCount x : Real)) := by
    have ht : 0 ≤ (nestedPairedTotalCount x : Real) := by positivity
    linarith
  calc
    |F (upd x) - F x| ≤ |F (upd x)| + |F x| := abs_sub _ _
    _ ≤ C * (1 + (nestedPairedTotalCount (upd x) : Real)) ^ degree +
        C * (1 + (nestedPairedTotalCount x : Real)) ^ degree :=
      add_le_add (hbound (upd x)) (hbound x)
    _ ≤ C * (2 * (1 + (nestedPairedTotalCount x : Real))) ^ degree +
        C * (2 * (1 + (nestedPairedTotalCount x : Real))) ^ degree := by
      gcongr
    _ = (2 * C * 2 ^ degree) *
        (1 + (nestedPairedTotalCount x : Real)) ^ degree := by
      simp [mul_pow]
      ring

/-- Two [arrays of nonnegative Poisson rates](hyp:lambda₁,lambda₂), a
[measurable real-valued nested-array statistic](hyp:F,hF), a
[nonnegative growth constant](hyp:C,hC), a [polynomial degree](hyp:degree), and its
[total-count growth bound](hyp:hbound) give
[all square-integrability premises for the nested paired-Poisson Poincaré inequality](goal). -/
theorem memLp_nestedPairedPoisson_and_addOne_of_polynomial_bound
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (F : (iota → kappa → Nat × Nat) → Real)
    (hF : Measurable F) (C : Real) (degree : Nat)
    (hC : 0 ≤ C)
    (hbound : ∀ x, |F x| ≤ C * (1 + (nestedPairedTotalCount x : Real)) ^ degree) :
    MemLp F 2 (nestedPairedPoissonMeasure lambda₁ lambda₂) ∧
      (∀ i j, MemLp (nestedPairAddOneFst i j F) 2
        (nestedPairedPoissonMeasure lambda₁ lambda₂)) ∧
      (∀ i j, MemLp (nestedPairAddOneSnd i j F) 2
        (nestedPairedPoissonMeasure lambda₁ lambda₂)) := by
  refine ⟨memLp_nestedPairedPoisson_of_polynomial_bound lambda₁ lambda₂ F hF C degree hC
    hbound, ?_, ?_⟩
  · intro i j
    exact memLp_nestedPairAddOneFst_of_polynomial_bound lambda₁ lambda₂ F hF C degree hC
      hbound i j
  · intro i j
    exact memLp_nestedPairAddOneSnd_of_polynomial_bound lambda₁ lambda₂ F hF C degree hC
      hbound i j

end

end Causalean.Mathlib.Probability.PoissonAddOnePoincare.NestedPairedProductMoments
