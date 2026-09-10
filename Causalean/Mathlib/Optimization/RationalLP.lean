/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Aesop
import Mathlib.Tactic.Positivity

/-! # Exact certificates for rational linear programs

This module proves attainment and strong duality for a finite linear program
whose variables and coefficients are rational.  The proof uses certified
Fourier--Motzkin elimination: primal variables are eliminated while the
objective coordinate is retained, and every generated inequality records its
nonnegative rational combination of the original rows.  The lower endpoint of
the resulting one-dimensional rational polyhedron is rational; elimination
back-substitution gives a rational primal optimizer, while the recorded
combination gives rational nonnegative dual multipliers of the same value.

The standard form minimizes `c · x` subject to `A i · x ≤ b i`.  Variables are
unrestricted in sign.  Equalities and nonnegative variables are represented by
pairs of inequalities, so this form faithfully covers arbitrary finite
rational LPs.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Optimization.RationalLP

noncomputable section

/-- Given [a common finite number of coordinates and two rational coordinate
vectors](hyp:n,a,x), the [rational dot product](goal) is the sum, over all coordinates,
of the product of their corresponding entries.

The finite dot product of two rational coordinate vectors. -/
def dot {n : ℕ} (a x : Fin n → ℚ) : ℚ := ∑ j, a j * x j

/-- A linear inequality in ordinary variables `x` and a retained objective
coordinate `t`, written `a · x + s * t ≤ b`. -/
structure AugmentedIneq (n : ℕ) where
  /-- Coefficients of the ordinary variables. -/
  coeff : Fin n → ℚ
  /-- Coefficient of the retained objective coordinate. -/
  objCoeff : ℚ
  /-- Right-hand side. -/
  rhs : ℚ

/-- Given [a number of ordinary coordinates, an augmented rational inequality, a rational
ordinary-variable vector, and a retained rational objective coordinate](hyp:n,r,x,t), the
[inequality-satisfaction condition](goal) holds exactly when the dot product of the ordinary
coefficients and vector plus the objective coefficient times the retained coordinate is no
greater than the right-hand side.

Satisfaction of an augmented rational linear inequality. -/
def AugmentedIneq.Holds {n : ℕ} (r : AugmentedIneq n) (x : Fin n → ℚ) (t : ℚ) : Prop :=
  dot r.coeff x + r.objCoeff * t ≤ r.rhs

/-- Given [an augmented rational inequality with one more ordinary coordinate](hyp:n,r), the
[tail inequality](goal) removes its first ordinary coefficient while retaining its objective
coefficient and right-hand side.

Remove the first, zero-coefficient variable from an augmented inequality. -/
def AugmentedIneq.tail (r : AugmentedIneq (n + 1)) : AugmentedIneq n where
  coeff := Fin.tail r.coeff
  objCoeff := r.objCoeff
  rhs := r.rhs

/-- Given [two augmented rational inequalities with one more ordinary coordinate](hyp:n,p,q),
the [cancellation inequality](goal) has each remaining coefficient, its objective coefficient,
and its right-hand side equal to the negative first coefficient of the second inequality times
the corresponding quantity of the first, plus the first coefficient of the first inequality
times the corresponding quantity of the second.

Combine a positive-head and negative-head inequality so their first
ordinary-variable coefficients cancel. -/
def AugmentedIneq.cancel (p q : AugmentedIneq (n + 1)) : AugmentedIneq n where
  coeff j := (-q.coeff 0) * p.coeff j.succ + p.coeff 0 * q.coeff j.succ
  objCoeff := (-q.coeff 0) * p.objCoeff + p.coeff 0 * q.objCoeff
  rhs := (-q.coeff 0) * p.rhs + p.coeff 0 * q.rhs

/-- Given [a list of augmented rational inequalities with one more ordinary coordinate](hyp:n,rows),
the [one-step Fourier--Motzkin elimination output](goal) contains the tails of all rows whose
first coefficient is zero and, for every row with negative first coefficient and every row
with positive first coefficient, their cancellation inequality.

One Fourier--Motzkin step, eliminating the first ordinary variable. -/
def eliminateOne (rows : List (AugmentedIneq (n + 1))) : List (AugmentedIneq n) :=
  (rows.filter (fun r => r.coeff 0 = 0)).map AugmentedIneq.tail ++
    (rows.filter (fun r => r.coeff 0 < 0)).flatMap fun q =>
      (rows.filter (fun r => 0 < r.coeff 0)).map fun p => p.cancel q

private lemma dot_cons (a x : Fin (n + 1) → ℚ) :
    dot a x = a 0 * x 0 + dot (Fin.tail a) (Fin.tail x) := by
  rw [dot, Fin.sum_univ_succ]
  rfl

private lemma dot_cancel (p q : AugmentedIneq (n + 1)) (x : Fin n → ℚ) :
    dot (p.cancel q).coeff x =
      (-q.coeff 0) * dot (Fin.tail p.coeff) x +
        p.coeff 0 * dot (Fin.tail q.coeff) x := by
  simp only [dot, AugmentedIneq.cancel, Fin.tail, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

private lemma cancel_holds {p q : AugmentedIneq (n + 1)} {x : Fin (n + 1) → ℚ} {t : ℚ}
    (hp : 0 < p.coeff 0) (hq : q.coeff 0 < 0)
    (hP : p.Holds x t) (hQ : q.Holds x t) :
    (p.cancel q).Holds (Fin.tail x) t := by
  simp only [AugmentedIneq.Holds, dot_cons] at hP hQ
  rw [AugmentedIneq.Holds, dot_cancel]
  dsimp [AugmentedIneq.cancel]
  have hqn : 0 ≤ -q.coeff 0 := by linarith
  have hpn : 0 ≤ p.coeff 0 := hp.le
  have h1 := mul_le_mul_of_nonneg_left hP hqn
  have h2 := mul_le_mul_of_nonneg_left hQ hpn
  linarith

private lemma mem_eliminateOne_of_holds
    {rows : List (AugmentedIneq (n + 1))} {x : Fin (n + 1) → ℚ} {t : ℚ}
    (hx : ∀ r ∈ rows, r.Holds x t) :
    ∀ r ∈ eliminateOne rows, r.Holds (Fin.tail x) t := by
  intro r hr
  simp only [eliminateOne, List.mem_append, List.mem_map, List.mem_filter,
    List.mem_flatMap] at hr
  rcases hr with ⟨z, ⟨hzmem, hz0⟩, rfl⟩ | ⟨q, ⟨hqmem, hqneg⟩, hr⟩
  · have hz0' : z.coeff 0 = 0 := of_decide_eq_true hz0
    simpa [AugmentedIneq.Holds, AugmentedIneq.tail, dot_cons, hz0'] using hx z hzmem
  · obtain ⟨p, ⟨⟨hpmem, hppos⟩, rfl⟩⟩ := hr
    exact cancel_holds (of_decide_eq_true hppos) (of_decide_eq_true hqneg)
      (hx p hpmem) (hx q hqmem)

private lemma exists_head_of_eliminateOne
    {rows : List (AugmentedIneq (n + 1))} {x : Fin n → ℚ} {t : ℚ}
    (hx : ∀ r ∈ eliminateOne rows, r.Holds x t) :
    ∃ z : ℚ, ∀ r ∈ rows, r.Holds (Fin.cons z x) t := by
  let lower : List ℚ :=
    (rows.filter (fun r => r.coeff 0 < 0)).map fun r =>
      (r.rhs - (dot (Fin.tail r.coeff) x + r.objCoeff * t)) / r.coeff 0
  let upper : List ℚ :=
    (rows.filter (fun r => 0 < r.coeff 0)).map fun r =>
      (r.rhs - (dot (Fin.tail r.coeff) x + r.objCoeff * t)) / r.coeff 0
  have hcross : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by
    intro l hl u hu
    simp only [lower, upper, List.mem_map, List.mem_filter] at hl hu
    obtain ⟨q, ⟨hqmem, hqneg⟩, rfl⟩ := hl
    obtain ⟨p, ⟨hpmem, hppos⟩, rfl⟩ := hu
    have hqneg' : q.coeff 0 < 0 := of_decide_eq_true hqneg
    have hppos' : 0 < p.coeff 0 := of_decide_eq_true hppos
    have hcan : (p.cancel q).Holds x t := by
      apply hx
      simp only [eliminateOne, List.mem_append, List.mem_map, List.mem_filter,
        List.mem_flatMap]
      right
      exact ⟨q, ⟨hqmem, hqneg⟩, p, ⟨⟨hpmem, hppos⟩, rfl⟩⟩
    rw [AugmentedIneq.Holds, dot_cancel] at hcan
    dsimp [AugmentedIneq.cancel] at hcan
    rw [le_div_iff₀ hppos', div_mul_eq_mul_div, div_le_iff_of_neg hqneg']
    linarith
  obtain ⟨z, hzlower, hzupper⟩ :
      ∃ z : ℚ, (∀ l ∈ lower, l ≤ z) ∧ (∀ u ∈ upper, z ≤ u) := by
    cases hL : lower with
    | nil =>
        cases hU : upper with
        | nil => exact ⟨0, by simp [hL, hU]⟩
        | cons u us =>
            have hlen : 0 < (u :: us).length := by simp
            let z := (u :: us).minimum_of_length_pos hlen
            refine ⟨z, by simp [hL], ?_⟩
            intro v hv
            exact List.minimum_of_length_pos_le_of_mem hv hlen
    | cons l ls =>
        have hlen : 0 < (l :: ls).length := by simp
        let z := (l :: ls).maximum_of_length_pos hlen
        refine ⟨z, ?_, ?_⟩
        · intro v hv
          exact List.le_maximum_of_length_pos_of_mem hv hlen
        · intro u hu
          have hzmem : z ∈ l :: ls := List.maximum_of_length_pos_mem hlen
          exact hcross z (by simpa [hL] using hzmem) u hu
  refine ⟨z, ?_⟩
  intro r hr
  rw [AugmentedIneq.Holds, dot_cons]
  simp only [Fin.cons_zero, Fin.tail_cons]
  by_cases hzero : r.coeff 0 = 0
  · have ht : r.tail.Holds x t := hx _ (by
      simp only [eliminateOne, List.mem_append, List.mem_map, List.mem_filter,
        List.mem_flatMap]
      left
      exact ⟨r, ⟨hr, decide_eq_true hzero⟩, rfl⟩)
    simpa [AugmentedIneq.Holds, AugmentedIneq.tail, hzero] using ht
  rcases lt_or_gt_of_ne hzero with hneg | hpos
  · have hl := hzlower
        ((r.rhs - (dot (Fin.tail r.coeff) x + r.objCoeff * t)) / r.coeff 0)
        (by
          simp only [lower, List.mem_map, List.mem_filter]
          exact ⟨r, ⟨hr, decide_eq_true hneg⟩, rfl⟩)
    have hmul := (div_le_iff_of_neg hneg).mp hl
    linarith
  · have hu := hzupper
        ((r.rhs - (dot (Fin.tail r.coeff) x + r.objCoeff * t)) / r.coeff 0)
        (by
          simp only [upper, List.mem_map, List.mem_filter]
          exact ⟨r, ⟨hr, decide_eq_true hpos⟩, rfl⟩)
    have hmul := (le_div_iff₀ hpos).mp hu
    linarith

/-- [One Fourier–Motzkin elimination step preserves exactly the feasible
values of the retained objective coordinate](goal). -/
theorem eliminateOne_iff {rows : List (AugmentedIneq (n + 1))} {x : Fin n → ℚ} {t : ℚ} :
    (∃ z : ℚ, ∀ r ∈ rows, r.Holds (Fin.cons z x) t) ↔
      ∀ r ∈ eliminateOne rows, r.Holds x t := by
  constructor
  · rintro ⟨z, hz⟩
    simpa using mem_eliminateOne_of_holds (x := Fin.cons z x) hz
  · exact exists_head_of_eliminateOne

/-- For [a nonnegative number of ordinary coordinates and a list of augmented rational
inequalities in that many coordinates](hyp:n), the [complete Fourier--Motzkin
elimination output](goal) [is the original list when there are no ordinary coordinates](step:1)
and [otherwise is obtained by one first-coordinate elimination followed by complete
elimination of the remaining coordinates](step:2).

Repeated Fourier--Motzkin elimination of all ordinary variables, leaving
only inequalities in the retained objective coordinate. -/
def eliminateAll : (n : ℕ) → List (AugmentedIneq n) → List (AugmentedIneq 0)
  | 0, rows => rows
  | n + 1, rows => eliminateAll n (eliminateOne rows)

/-- [Eliminating all ordinary variables preserves exactly the feasible values
of the retained objective coordinate](goal). -/
theorem eliminateAll_iff {n : ℕ} {rows : List (AugmentedIneq n)} {t : ℚ} :
    (∃ x : Fin n → ℚ, ∀ r ∈ rows, r.Holds x t) ↔
      ∀ r ∈ eliminateAll n rows, r.Holds Fin.elim0 t := by
  induction n with
  | zero =>
      simp only [eliminateAll]
      constructor
      · rintro ⟨x, hx⟩
        simpa only [Subsingleton.elim x Fin.elim0] using hx
      · intro hx
        exact ⟨Fin.elim0, hx⟩
  | succ n ih =>
      rw [eliminateAll, ← ih]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨Fin.tail x, (eliminateOne_iff.mp ⟨x 0, by simpa using hx⟩)⟩
      · rintro ⟨x, hx⟩
        obtain ⟨z, hz⟩ := eliminateOne_iff.mpr hx
        exact ⟨Fin.cons z x, hz⟩

/-- A finite rational LP in inequality form: minimize `c · x` subject to
`A i · x ≤ b i`. -/
structure Program (ι : Type*) (n : ℕ) where
  /-- Constraint coefficient rows. -/
  A : ι → Fin n → ℚ
  /-- Constraint right-hand sides. -/
  b : ι → ℚ
  /-- Objective coefficient row. -/
  c : Fin n → ℚ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Given [a constraint-label set, a number of ordinary variables, a rational linear
program, and a rational vector of those variables](hyp:ι,n,P,x), the
[primal-feasibility condition](goal) holds exactly when, for every constraint, the dot
product of its coefficient row with the vector is no greater than its right-hand side.

A rational point satisfies every inequality of the program. -/
def Program.PrimalFeasible (P : Program ι n) (x : Fin n → ℚ) : Prop :=
  ∀ i, dot (P.A i) x ≤ P.b i

/-- Given [a constraint-label set, a number of ordinary variables, a rational linear
program, and a rational vector of those variables](hyp:ι,n,P,x), the [primal objective
value](goal) is the dot product of the program's objective coefficient vector with that
variable vector.

The rational objective value at a primal point. -/
def Program.objective (P : Program ι n) (x : Fin n → ℚ) : ℚ := dot P.c x

private def Program.augmentedRows (P : Program ι n) : List (AugmentedIneq n) :=
  (Finset.univ.toList.map fun i =>
    { coeff := P.A i, objCoeff := 0, rhs := P.b i }) ++
  [ { coeff := fun j => -P.c j, objCoeff := 1, rhs := 0 },
    { coeff := P.c, objCoeff := -1, rhs := 0 } ]

private lemma neg_dot (a x : Fin n → ℚ) : dot (fun j => -a j) x = -dot a x := by
  simp [dot, ← Finset.sum_neg_distrib]

private lemma augmentedRows_holds_iff (P : Program ι n) (x : Fin n → ℚ) (t : ℚ) :
    (∀ r ∈ P.augmentedRows, r.Holds x t) ↔
      P.PrimalFeasible x ∧ t = P.objective x := by
  simp only [Program.augmentedRows, List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, List.mem_cons, List.mem_singleton, AugmentedIneq.Holds]
  constructor
  · intro h
    have horig : ∀ i, dot (P.A i) x ≤ P.b i := by
      intro i
      have := h { coeff := P.A i, objCoeff := 0, rhs := P.b i }
        (Or.inl ⟨i, rfl⟩)
      simpa using this
    have h₁ := h { coeff := fun j => -P.c j, objCoeff := 1, rhs := 0 }
      (Or.inr (Or.inl rfl))
    have h₂ := h { coeff := P.c, objCoeff := -1, rhs := 0 }
      (Or.inr (Or.inr (Or.inl rfl)))
    simp only [neg_dot, Program.objective] at h₁ h₂
    constructor
    · exact horig
    · change t = dot P.c x
      linarith
  · rintro ⟨hx, rfl⟩ r hr
    rcases hr with ⟨i, rfl⟩ | hr
    · simpa using hx i
    · rcases hr with rfl | hr
      · simp [neg_dot, Program.objective]
      · rcases hr with rfl | hr
        · simp [Program.objective]
        · simp at hr

private def Program.objectiveRows (P : Program ι n) : List (AugmentedIneq 0) :=
  eliminateAll n P.augmentedRows

private lemma objectiveRows_iff (P : Program ι n) (t : ℚ) :
    (∃ x, P.PrimalFeasible x ∧ P.objective x = t) ↔
      ∀ r ∈ P.objectiveRows, r.Holds Fin.elim0 t := by
  rw [Program.objectiveRows, ← eliminateAll_iff]
  constructor
  · rintro ⟨x, hx, hxt⟩
    exact ⟨x, (augmentedRows_holds_iff P x t).2 ⟨hx, hxt.symm⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hfeas, ht⟩ := (augmentedRows_holds_iff P x t).1 hx
    exact ⟨x, hfeas, ht.symm⟩

private lemma holds_zero_iff (r : AugmentedIneq 0) (t : ℚ) :
    r.Holds Fin.elim0 t ↔ r.objCoeff * t ≤ r.rhs := by
  simp [AugmentedIneq.Holds, dot]

private lemma scalar_endpoint
    (rows : List (AugmentedIneq 0))
    (hne : ∃ t : ℚ, ∀ r ∈ rows, r.Holds Fin.elim0 t)
    (hbdd : ∃ l : ℚ, ∀ t : ℚ, (∀ r ∈ rows, r.Holds Fin.elim0 t) → l ≤ t) :
    ∃ v : ℚ, (∀ r ∈ rows, r.Holds Fin.elim0 v) ∧
      (∀ t : ℚ, (∀ r ∈ rows, r.Holds Fin.elim0 t) → v ≤ t) ∧
      ∃ r ∈ rows, r.objCoeff < 0 ∧ r.rhs / r.objCoeff = v := by
  let lowers : List ℚ :=
    (rows.filter (fun r => r.objCoeff < 0)).map fun r => r.rhs / r.objCoeff
  have hlower_ne : lowers ≠ [] := by
    intro hempty
    obtain ⟨t₀, ht₀⟩ := hne
    obtain ⟨l, hl⟩ := hbdd
    have hnone : ∀ r ∈ rows, ¬ r.objCoeff < 0 := by
      intro r hr hneg
      have : r.rhs / r.objCoeff ∈ lowers := by
        simp only [lowers, List.mem_map, List.mem_filter]
        exact ⟨r, ⟨hr, decide_eq_true hneg⟩, rfl⟩
      simpa [hempty] using this
    let t₁ := min t₀ (l - 1)
    have ht₁ : ∀ r ∈ rows, r.Holds Fin.elim0 t₁ := by
      intro r hr
      rw [holds_zero_iff]
      have hr₀ := (holds_zero_iff r t₀).1 (ht₀ r hr)
      have hcoeff : 0 ≤ r.objCoeff := le_of_not_gt (hnone r hr)
      exact (mul_le_mul_of_nonneg_left (min_le_left t₀ (l - 1)) hcoeff).trans hr₀
    have := hl t₁ ht₁
    dsimp [t₁] at this
    linarith [min_le_right t₀ (l - 1)]
  have hlen : 0 < lowers.length := List.length_pos_iff.mpr hlower_ne
  let v := lowers.maximum_of_length_pos hlen
  have hvmem : v ∈ lowers := List.maximum_of_length_pos_mem hlen
  refine ⟨v, ?_, ?_, ?_⟩
  · intro r hr
    rw [holds_zero_iff]
    by_cases hneg : r.objCoeff < 0
    · have hratio : r.rhs / r.objCoeff ∈ lowers := by
        simp only [lowers, List.mem_map, List.mem_filter]
        exact ⟨r, ⟨hr, decide_eq_true hneg⟩, rfl⟩
      have hle := List.le_maximum_of_length_pos_of_mem hratio hlen
      simpa [mul_comm] using (div_le_iff_of_neg hneg).1 hle
    · obtain ⟨t₀, ht₀⟩ := hne
      have hr₀ := (holds_zero_iff r t₀).1 (ht₀ r hr)
      have hc : 0 ≤ r.objCoeff := le_of_not_gt hneg
      have hvbound : v ≤ t₀ := by
        obtain ⟨q, hq, hqv⟩ := by
          simpa only [lowers, List.mem_map, List.mem_filter] using hvmem
        have hqneg : q.objCoeff < 0 := of_decide_eq_true hq.2
        have hq₀ := (holds_zero_iff q t₀).1 (ht₀ q hq.1)
        rw [← hqv]
        exact (div_le_iff_of_neg hqneg).2 (by simpa [mul_comm] using hq₀)
      exact (mul_le_mul_of_nonneg_left hvbound hc).trans hr₀
  · intro t ht
    obtain ⟨r, hr, hrv⟩ : ∃ r, (r ∈ rows ∧ r.objCoeff < 0) ∧ r.rhs / r.objCoeff = v := by
      simp only [lowers, List.mem_map, List.mem_filter] at hvmem
      obtain ⟨r, ⟨hrmem, hrneg⟩, hrv⟩ := hvmem
      exact ⟨r, ⟨hrmem, of_decide_eq_true hrneg⟩, hrv⟩
    rw [← hrv]
    exact (div_le_iff_of_neg hr.2).2 (by
      simpa [mul_comm] using (holds_zero_iff r t).1 (ht r hr.1))
  · simp only [lowers, List.mem_map, List.mem_filter] at hvmem
    obtain ⟨r, ⟨hrmem, hrneg⟩, hrv⟩ := hvmem
    exact ⟨r, hrmem, of_decide_eq_true hrneg, hrv⟩

/-- If [a finite rational linear program has a feasible rational point](hyp:hne)
and [its objective is bounded below on feasible rational points](hyp:hbdd), then
[it has a rational primal optimizer](goal). -/
theorem exists_rational_primal_optimizer (P : Program ι n)
    (hne : ∃ x, P.PrimalFeasible x)
    (hbdd : ∃ l : ℚ, ∀ x, P.PrimalFeasible x → l ≤ P.objective x) :
    ∃ xStar : Fin n → ℚ, P.PrimalFeasible xStar ∧
      ∀ x, P.PrimalFeasible x → P.objective xStar ≤ P.objective x := by
  have hobjne : ∃ t : ℚ, ∀ r ∈ P.objectiveRows, r.Holds Fin.elim0 t := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨P.objective x, (objectiveRows_iff P _).1 ⟨x, hx, rfl⟩⟩
  have hobjbdd : ∃ l : ℚ, ∀ t : ℚ,
      (∀ r ∈ P.objectiveRows, r.Holds Fin.elim0 t) → l ≤ t := by
    obtain ⟨l, hl⟩ := hbdd
    refine ⟨l, ?_⟩
    intro t ht
    obtain ⟨x, hx, hxt⟩ := (objectiveRows_iff P t).2 ht
    simpa [← hxt] using hl x hx
  obtain ⟨v, hvfeas, hvmin, _⟩ := scalar_endpoint P.objectiveRows hobjne hobjbdd
  obtain ⟨xStar, hxStar, hxval⟩ := (objectiveRows_iff P v).2 hvfeas
  refine ⟨xStar, hxStar, ?_⟩
  intro x hx
  rw [hxval]
  exact hvmin (P.objective x) ((objectiveRows_iff P _).1 ⟨x, hx, rfl⟩)

section CertifiedElimination

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- An augmented inequality together with nonnegative rational provenance from
a fixed finite family of original rows.  The coefficient identity is stated
through a common projection of the original variables; this makes repeated
elimination independent of coordinate-reassociation bookkeeping. -/
structure CertifiedIneq (base : κ → AugmentedIneq N)
    (project : (Fin N → ℚ) → (Fin n → ℚ)) where
  /-- The currently derived inequality. -/
  row : AugmentedIneq n
  /-- Nonnegative combination weights on the original rows. -/
  weight : κ → ℚ
  /-- The current coefficient row is the weighted original coefficient row. -/
  coeff_eq : ∀ x, dot row.coeff (project x) = ∑ k, weight k * dot (base k).coeff x
  /-- The objective-coordinate coefficient is the same weighted combination. -/
  objCoeff_eq : row.objCoeff = ∑ k, weight k * (base k).objCoeff
  /-- The right-hand side is the same weighted combination. -/
  rhs_eq : row.rhs = ∑ k, weight k * (base k).rhs

private def CertifiedIneq.atom {N : ℕ} (base : κ → AugmentedIneq N) (k : κ) :
    CertifiedIneq base id :=
  { row := base k
    weight := fun j => if j = k then 1 else 0
    coeff_eq := by
      intro x
      simp only [id_eq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ k]
      simp
    objCoeff_eq := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ k]
      simp
    rhs_eq := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ k]
      simp }

private def CertifiedIneq.dropHead
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin (n + 1) → ℚ)}
    (d : CertifiedIneq base project) (hzero : d.row.coeff 0 = 0) :
    CertifiedIneq base (fun x => Fin.tail (project x)) :=
  { row := d.row.tail
    weight := d.weight
    coeff_eq := by
      intro x
      rw [← d.coeff_eq x]
      rw [dot_cons (d.row.coeff) (project x), hzero]
      simp [AugmentedIneq.tail]
    objCoeff_eq := d.objCoeff_eq
    rhs_eq := d.rhs_eq }

private def CertifiedIneq.cancelRows
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin (n + 1) → ℚ)}
    (p q : CertifiedIneq base project) :
    CertifiedIneq base (fun x => Fin.tail (project x)) :=
  { row := p.row.cancel q.row
    weight := fun k => (-q.row.coeff 0) * p.weight k + p.row.coeff 0 * q.weight k
    coeff_eq := by
      intro x
      rw [dot_cancel]
      calc
        _ = (-q.row.coeff 0) * (∑ k, p.weight k * dot (base k).coeff x) +
              p.row.coeff 0 * (∑ k, q.weight k * dot (base k).coeff x) := by
            rw [← p.coeff_eq x, ← q.coeff_eq x, dot_cons, dot_cons]
            ring
        _ = _ := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    objCoeff_eq := by
      dsimp [AugmentedIneq.cancel]
      rw [p.objCoeff_eq, q.objCoeff_eq]
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rhs_eq := by
      dsimp [AugmentedIneq.cancel]
      rw [p.rhs_eq, q.rhs_eq]
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] }

private def eliminateCertifiedOne
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin (n + 1) → ℚ)}
    (rows : List (CertifiedIneq base project)) :
    List (CertifiedIneq base (fun x => Fin.tail (project x))) :=
  (rows.filterMap fun d =>
      if h : d.row.coeff 0 = 0 then some (d.dropHead h) else none) ++
    (rows.filter (fun d => d.row.coeff 0 < 0)).flatMap fun q =>
      (rows.filter (fun d => 0 < d.row.coeff 0)).map fun p => p.cancelRows q

private lemma rows_eliminateCertifiedOne
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin (n + 1) → ℚ)}
    (rows : List (CertifiedIneq base project)) :
    (eliminateCertifiedOne rows).map CertifiedIneq.row =
      eliminateOne (rows.map CertifiedIneq.row) := by
  simp only [eliminateCertifiedOne, eliminateOne, List.map_append,
    List.map_filterMap, List.filter_map, Function.comp_def]
  congr 1
  · induction rows with
    | nil => simp
    | cons d ds ih =>
        by_cases h : d.row.coeff 0 = 0
        · simp only [List.filterMap_cons]
          rw [dif_pos h]
          simp only [Option.map_some, List.map_cons]
          simp only [List.filter_cons]
          rw [if_pos (decide_eq_true h)]
          simp only [List.map_cons, CertifiedIneq.dropHead]
          exact congrArg (List.cons d.row.tail) ih
        · simp only [List.filterMap_cons]
          rw [dif_neg h]
          simp only [Option.map_none]
          simp only [List.filter_cons]
          rw [if_neg (by simp [h])]
          exact ih
  ·
    let posRows := rows.filter (fun d => 0 < d.row.coeff 0)
    have hinner (q : CertifiedIneq base project) :
        (posRows.map fun p => p.cancelRows q).map CertifiedIneq.row =
          (posRows.map CertifiedIneq.row).map fun p => p.cancel q.row := by
      induction posRows with
      | nil => simp
      | cons p ps ih => simp [CertifiedIneq.cancelRows, ih]
    induction (rows.filter (fun d => d.row.coeff 0 < 0)) with
    | nil => simp
    | cons q qs ih =>
        simp only [List.flatMap_cons, List.map_append, List.map_cons]
        rw [hinner, ih]

private def certifiedWeightNonnegative
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin n → ℚ)}
    (d : CertifiedIneq base project) : Prop := ∀ k, 0 ≤ d.weight k

private lemma weightNonnegative_eliminateCertifiedOne
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin (n + 1) → ℚ)}
    {rows : List (CertifiedIneq base project)}
    (hrows : ∀ d ∈ rows, certifiedWeightNonnegative d) :
    ∀ d ∈ eliminateCertifiedOne rows, certifiedWeightNonnegative d := by
  intro d hd
  simp only [eliminateCertifiedOne, List.mem_append, List.mem_filterMap,
    List.mem_flatMap, List.mem_map, List.mem_filter] at hd
  rcases hd with ⟨z, hzmem, hz⟩ | ⟨q, ⟨hqmem, hqneg⟩, p, ⟨⟨hpmem, hppos⟩, hpq⟩⟩
  · split at hz <;> simp_all [CertifiedIneq.dropHead, certifiedWeightNonnegative]
    subst d
    exact hrows z hzmem
  · subst d
    intro k
    dsimp [CertifiedIneq.cancelRows]
    exact add_nonneg
      (mul_nonneg (neg_nonneg.mpr (le_of_lt (of_decide_eq_true hqneg))) (hrows p hpmem k))
      (mul_nonneg (le_of_lt (of_decide_eq_true hppos)) (hrows q hqmem k))

private theorem eliminateCertifiedOne_iff
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin (n + 1) → ℚ)}
    {rows : List (CertifiedIneq base project)} {x : Fin n → ℚ} {t : ℚ} :
    (∃ z : ℚ, ∀ d ∈ rows, d.row.Holds (Fin.cons z x) t) ↔
      ∀ d ∈ eliminateCertifiedOne rows, d.row.Holds x t := by
  have hleft :
      (∃ z : ℚ, ∀ d ∈ rows, d.row.Holds (Fin.cons z x) t) ↔
        ∃ z : ℚ, ∀ r ∈ rows.map CertifiedIneq.row, r.Holds (Fin.cons z x) t := by
    simp only [List.mem_map]
    aesop
  have hright :
      (∀ d ∈ eliminateCertifiedOne rows, d.row.Holds x t) ↔
        ∀ r ∈ eliminateOne (rows.map CertifiedIneq.row), r.Holds x t := by
    rw [← rows_eliminateCertifiedOne]
    simp only [List.mem_map]
    aesop
  rw [hleft, hright]
  exact eliminateOne_iff

/-- A fully eliminated inequality with nonnegative provenance on the original
rows and with every original-variable coefficient certified to cancel. -/
structure FinalCertifiedIneq (base : κ → AugmentedIneq N) where
  /-- The scalar inequality in the retained objective coordinate. -/
  row : AugmentedIneq 0
  /-- Nonnegative weights on original rows. -/
  weight : κ → ℚ
  /-- Nonnegativity of every original-row weight. -/
  weight_nonneg : ∀ k, 0 ≤ weight k
  /-- All original-variable coefficients cancel. -/
  coeff_zero : ∀ x, ∑ k, weight k * dot (base k).coeff x = 0
  /-- Objective coefficient combination identity. -/
  objCoeff_eq : row.objCoeff = ∑ k, weight k * (base k).objCoeff
  /-- Right-hand-side combination identity. -/
  rhs_eq : row.rhs = ∑ k, weight k * (base k).rhs

private def CertifiedIneq.finish
    {N : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin 0 → ℚ)}
    (d : CertifiedIneq base project) (hnonneg : certifiedWeightNonnegative d) :
    FinalCertifiedIneq base :=
  { row := d.row
    weight := d.weight
    weight_nonneg := hnonneg
    coeff_zero := by
      intro x
      rw [← d.coeff_eq x]
      simp [dot]
    objCoeff_eq := d.objCoeff_eq
    rhs_eq := d.rhs_eq }

private def eliminateCertifiedAll
    {N : ℕ} {base : κ → AugmentedIneq N} :
    (n : ℕ) → {project : (Fin N → ℚ) → (Fin n → ℚ)} →
      (rows : List (CertifiedIneq base project)) →
      (∀ d ∈ rows, certifiedWeightNonnegative d) →
      List (FinalCertifiedIneq base)
  | 0, _, rows, hrows => rows.attach.map fun d => d.1.finish (hrows d.1 d.2)
  | n + 1, _, rows, hrows =>
      eliminateCertifiedAll n (eliminateCertifiedOne rows)
        (weightNonnegative_eliminateCertifiedOne hrows)

private lemma rows_eliminateCertifiedAll
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin n → ℚ)}
    (rows : List (CertifiedIneq base project))
    (hrows : ∀ d ∈ rows, certifiedWeightNonnegative d) :
    (eliminateCertifiedAll n rows hrows).map FinalCertifiedIneq.row =
      eliminateAll n (rows.map CertifiedIneq.row) := by
  induction n with
  | zero =>
      simp [eliminateCertifiedAll, eliminateAll, CertifiedIneq.finish]
  | succ n ih =>
      simp only [eliminateCertifiedAll, eliminateAll]
      rw [ih, rows_eliminateCertifiedOne]

private lemma eliminateCertifiedAll_iff
    {N n : ℕ} {base : κ → AugmentedIneq N}
    {project : (Fin N → ℚ) → (Fin n → ℚ)}
    {rows : List (CertifiedIneq base project)}
    (hrows : ∀ d ∈ rows, certifiedWeightNonnegative d) {t : ℚ} :
    (∃ x : Fin n → ℚ, ∀ d ∈ rows, d.row.Holds x t) ↔
      ∀ d ∈ eliminateCertifiedAll n rows hrows, d.row.Holds Fin.elim0 t := by
  have hleft :
      (∃ x : Fin n → ℚ, ∀ d ∈ rows, d.row.Holds x t) ↔
        ∃ x : Fin n → ℚ, ∀ r ∈ rows.map CertifiedIneq.row, r.Holds x t := by
    simp only [List.mem_map]
    aesop
  have hright :
      (∀ d ∈ eliminateCertifiedAll n rows hrows, d.row.Holds Fin.elim0 t) ↔
        ∀ r ∈ (eliminateCertifiedAll n rows hrows).map FinalCertifiedIneq.row,
          r.Holds Fin.elim0 t := by
    simp only [List.mem_map]
    aesop
  rw [hleft, hright, rows_eliminateCertifiedAll]
  exact eliminateAll_iff

end CertifiedElimination

private def Program.certificateBase (P : Program ι n) :
    Sum ι Bool → AugmentedIneq n
  | .inl i => { coeff := P.A i, objCoeff := 0, rhs := P.b i }
  | .inr false => { coeff := fun j => -P.c j, objCoeff := 1, rhs := 0 }
  | .inr true => { coeff := P.c, objCoeff := -1, rhs := 0 }

private def Program.initialCertifiedRows (P : Program ι n) :
    List (CertifiedIneq P.certificateBase id) :=
  Finset.univ.toList.map fun k => CertifiedIneq.atom P.certificateBase k

private lemma initialCertifiedRows_nonnegative (P : Program ι n) :
    ∀ d ∈ P.initialCertifiedRows, certifiedWeightNonnegative d := by
  intro d hd
  simp only [Program.initialCertifiedRows, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and] at hd
  obtain ⟨k, rfl⟩ := hd
  intro j
  by_cases h : j = k <;> simp [CertifiedIneq.atom, certifiedWeightNonnegative, h]

private lemma initialCertifiedRows_holds_iff (P : Program ι n) (x : Fin n → ℚ) (t : ℚ) :
    (∀ d ∈ P.initialCertifiedRows, d.row.Holds x t) ↔
      P.PrimalFeasible x ∧ t = P.objective x := by
  constructor
  · intro h
    have hbase : ∀ k : Sum ι Bool, (P.certificateBase k).Holds x t := by
      intro k
      apply h (CertifiedIneq.atom P.certificateBase k)
      simp [Program.initialCertifiedRows]
    have hfeas : P.PrimalFeasible x := by
      intro i
      simpa [Program.certificateBase, AugmentedIneq.Holds] using hbase (.inl i)
    have h₁ := hbase (.inr false)
    have h₂ := hbase (.inr true)
    simp only [Program.certificateBase, AugmentedIneq.Holds, neg_dot] at h₁ h₂
    refine ⟨hfeas, ?_⟩
    change t = dot P.c x
    linarith
  · rintro ⟨hx, rfl⟩ d hd
    simp only [Program.initialCertifiedRows, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hd
    obtain ⟨k, rfl⟩ := hd
    rcases k with i | b
    · simpa [CertifiedIneq.atom, Program.certificateBase, AugmentedIneq.Holds] using hx i
    · cases b <;> simp [CertifiedIneq.atom, Program.certificateBase,
        AugmentedIneq.Holds, neg_dot, Program.objective]

private def Program.finalCertifiedRows (P : Program ι n) :
    List (FinalCertifiedIneq P.certificateBase) :=
  eliminateCertifiedAll n P.initialCertifiedRows (initialCertifiedRows_nonnegative P)

private lemma finalCertifiedRows_iff (P : Program ι n) (t : ℚ) :
    (∃ x, P.PrimalFeasible x ∧ P.objective x = t) ↔
      ∀ d ∈ P.finalCertifiedRows, d.row.Holds Fin.elim0 t := by
  rw [Program.finalCertifiedRows, ← eliminateCertifiedAll_iff
    (initialCertifiedRows_nonnegative P)]
  constructor
  · rintro ⟨x, hx, hxt⟩
    exact ⟨x, (initialCertifiedRows_holds_iff P x t).2 ⟨hx, hxt.symm⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hfeas, ht⟩ := (initialCertifiedRows_holds_iff P x t).1 hx
    exact ⟨x, hfeas, ht.symm⟩

/-- Given [a finite set of constraint labels and number of ordinary variables, a finite
rational linear program, and rational multipliers for its constraints](hyp:ι,n,P,y), the
[dual-feasibility condition](goal) holds exactly when [every multiplier is nonnegative](step:1)
and, [for every ordinary coordinate, the multiplier-weighted sum of constraint coefficients
equals the negative objective coefficient](step:2).

A rational multiplier is dual feasible for the inequality-form minimization
problem when it is nonnegative and its weighted constraint normal equals the
negative objective normal. -/
def Program.DualFeasible (P : Program ι n) (y : ι → ℚ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, ∑ i, y i * P.A i j = -P.c j

/-- Given [a finite set of constraint labels and number of ordinary variables, a finite
rational linear program, and rational constraint multipliers](hyp:ι,n,P,y), the [dual
objective value](goal) is the negative of the multiplier-weighted sum of the constraint
right-hand sides.

The dual objective for `A x ≤ b` with stationarity `Σ yᵢ Aᵢ = -c` is
`-Σ yᵢ bᵢ`. -/
def Program.dualObjective (P : Program ι n) (y : ι → ℚ) : ℚ :=
  -(∑ i, y i * P.b i)

/-- **Exact rational LP attainment and strong duality.** If [a finite rational
linear program in inequality form has a feasible rational point](hyp:hne) and
[its objective is bounded below on feasible rational points](hyp:hbdd), then
[it has a rational optimal primal point and rational nonnegative dual
multipliers with the same objective value](goal). -/
theorem exists_rational_optimal_primal_dual (P : Program ι n)
    (hne : ∃ x, P.PrimalFeasible x)
    (hbdd : ∃ l : ℚ, ∀ x, P.PrimalFeasible x → l ≤ P.objective x) :
    ∃ (xStar : Fin n → ℚ) (yStar : ι → ℚ),
      P.PrimalFeasible xStar ∧ P.DualFeasible yStar ∧
      P.objective xStar = P.dualObjective yStar ∧
      ∀ x, P.PrimalFeasible x → P.objective xStar ≤ P.objective x := by
  let rows := P.finalCertifiedRows.map FinalCertifiedIneq.row
  have hrowsne : ∃ t : ℚ, ∀ r ∈ rows, r.Holds Fin.elim0 t := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨P.objective x, ?_⟩
    intro r hr
    simp only [rows, List.mem_map] at hr
    obtain ⟨d, hd, rfl⟩ := hr
    exact (finalCertifiedRows_iff P _).1 ⟨x, hx, rfl⟩ d hd
  have hrowsbdd : ∃ l : ℚ, ∀ t : ℚ,
      (∀ r ∈ rows, r.Holds Fin.elim0 t) → l ≤ t := by
    obtain ⟨l, hl⟩ := hbdd
    refine ⟨l, ?_⟩
    intro t ht
    have hfinal : ∀ d ∈ P.finalCertifiedRows, d.row.Holds Fin.elim0 t := by
      intro d hd
      exact ht d.row (by
        change d.row ∈ P.finalCertifiedRows.map FinalCertifiedIneq.row
        exact List.mem_map.mpr ⟨d, hd, rfl⟩)
    obtain ⟨x, hx, hxt⟩ := (finalCertifiedRows_iff P t).2 hfinal
    simpa [← hxt] using hl x hx
  obtain ⟨v, hvfeas, hvmin, r, hrrows, hrneg, hrv⟩ :=
    scalar_endpoint rows hrowsne hrowsbdd
  obtain ⟨d, hd, hdr⟩ : ∃ d ∈ P.finalCertifiedRows, d.row = r := by
    simpa only [rows, List.mem_map] using hrrows
  subst r
  obtain ⟨xStar, hxStar, hxval⟩ := (finalCertifiedRows_iff P v).2 (by
    intro e he
    exact hvfeas e.row (by
      change e.row ∈ P.finalCertifiedRows.map FinalCertifiedIneq.row
      exact List.mem_map.mpr ⟨e, he, rfl⟩))
  let denom : ℚ := -d.row.objCoeff
  have hdenom : 0 < denom := by dsimp [denom]; linarith
  let yStar : ι → ℚ := fun i => d.weight (.inl i) / denom
  have hobjcomb :
      d.row.objCoeff = d.weight (.inr false) - d.weight (.inr true) := by
    rw [d.objCoeff_eq]
    simp [Program.certificateBase, Fintype.sum_sum_type, Fintype.sum_bool,
      sub_eq_add_neg, add_comm]
  have hcoeff (x : Fin n → ℚ) :
      (∑ i, d.weight (.inl i) * dot (P.A i) x) -
          d.weight (.inr false) * dot P.c x +
          d.weight (.inr true) * dot P.c x = 0 := by
    have hc0 := d.coeff_zero x
    simp [Program.certificateBase, Fintype.sum_sum_type, Fintype.sum_bool,
      neg_dot] at hc0
    linarith
  have hrhs : d.row.rhs = ∑ i, d.weight (.inl i) * P.b i := by
    rw [d.rhs_eq]
    simp [Program.certificateBase, Fintype.sum_sum_type, Fintype.sum_bool]
  refine ⟨xStar, yStar, hxStar, ?_, ?_, ?_⟩
  · constructor
    · intro i
      exact div_nonneg (d.weight_nonneg (.inl i)) hdenom.le
    · intro j
      have hc := hcoeff (fun k => if k = j then 1 else 0)
      simp only [dot, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at hc
      dsimp [yStar]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
      apply (div_eq_iff hdenom.ne').2
      dsimp [denom]
      rw [hobjcomb]
      ring_nf at hc ⊢
      linarith
  · rw [hxval, ← hrv]
    dsimp [Program.dualObjective, yStar]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← hrhs]
    dsimp [denom]
    field_simp
  · intro x hx
    rw [hxval]
    apply hvmin (P.objective x)
    intro rr hrr
    simp only [rows, List.mem_map] at hrr
    obtain ⟨e, he, rfl⟩ := hrr
    exact (finalCertifiedRows_iff P _).1 ⟨x, hx, rfl⟩ e he

end

end Causalean.Mathlib.Optimization.RationalLP
