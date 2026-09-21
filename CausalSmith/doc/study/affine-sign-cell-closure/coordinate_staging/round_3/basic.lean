/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Finite affine sign cells

This module defines finite systems of real affine inequalities with individually weak or
strict comparisons, together with their strict cells and weak relaxations.  It proves that
the weak relaxation is a closed convex set.
-/

open scoped BigOperators Topology
open Set Filter

namespace Causalean.Mathlib.Optimization.AffineSignCellClosure

/-- Given [a finite number of coordinates](hyp:n), an affine real-valued function is specified
by [one coefficient for each coordinate](hyp:coeff) and [one constant term](hyp:constant).

An affine real-valued function on a finite real coordinate space. -/
structure AffineFn (n : ℕ) where
  /-- The coefficient of each coordinate. -/
  coeff : Fin n → ℝ
  /-- The constant term. -/
  constant : ℝ

namespace AffineFn

/-- Given [an affine function](hyp:f) and [a coordinate vector](hyp:x), its [evaluated
real value](goal) is given by [the finite coefficient-weighted sum plus the constant](step:1).

Evaluation of an affine function. -/
def eval {n : ℕ} (f : AffineFn n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, f.coeff i * x i + f.constant

/-- Given [an affine function](hyp:f), [two coordinate vectors](hyp:x,y), and [a real
weight](hyp:t), [evaluation at their affine combination equals the same affine combination
of their evaluations](goal). -/
theorem eval_affineCombination {n : ℕ} (f : AffineFn n) (x y : Fin n → ℝ) (t : ℝ) :
    f.eval ((1 - t) • x + t • y) = (1 - t) * f.eval x + t * f.eval y := by
  simp only [eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, f.coeff i * ((1 - t) * x i + t * y i)) + f.constant =
        (1 - t) * (∑ i, f.coeff i * x i) +
          t * (∑ i, f.coeff i * y i) + f.constant := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply congrArg (fun z => z + f.constant)
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (1 - t) * ((∑ i, f.coeff i * x i) + f.constant) +
          t * ((∑ i, f.coeff i * y i) + f.constant) := by
      ring

/-- Given [an affine function](hyp:f), [its evaluation map is continuous](goal). -/
theorem continuous_eval {n : ℕ} (f : AffineFn n) : Continuous f.eval := by
  unfold eval
  fun_prop

end AffineFn

/-- A [constraint kind](goal) records whether its affine inequality is [weak](step:1) or
[strict](step:2). -/
inductive ConstraintKind where
  /-- The constraint is interpreted with a weak comparison. -/
  | weak
  /-- The constraint is interpreted with a strict comparison. -/
  | strict
  deriving DecidableEq, Repr

/-- Given [a finite number of coordinates](hyp:n), a marked affine constraint contains [its
normalized affine left-hand side](hyp:fn) and [its weak-or-strict mark](hyp:kind).

A marked real affine inequality normalized against zero. -/
structure Constraint (n : ℕ) where
  /-- The affine left-hand side, normalized against zero. -/
  fn : AffineFn n
  /-- Whether the normalized inequality is weak or strict. -/
  kind : ConstraintKind

/-- Given [a finite number of coordinates](hyp:n), an [affine constraint system](goal) is
given by [a finite list of marked affine constraints](step:1). -/
abbrev AffineSystem (n : ℕ) := List (Constraint n)

namespace Constraint

/-- Given [a marked affine constraint](hyp:c) and [a coordinate vector](hyp:x), the [original
constraint-satisfaction condition](goal) uses [the comparison selected by the constraint's mark](step:1).

A point satisfies a marked constraint using its original weak or strict comparison. -/
def strictHolds {n : ℕ} (c : Constraint n) (x : Fin n → ℝ) : Prop :=
  match c.kind with
  | .weak => c.fn.eval x ≤ 0
  | .strict => c.fn.eval x < 0

/-- Given [a marked affine constraint](hyp:c) and [a coordinate vector](hyp:x), the [weak
constraint-satisfaction condition](goal) is given by [the nonpositive affine evaluation](step:1).

A point weakly satisfies a marked constraint, irrespective of its original mark. -/
def weakHolds {n : ℕ} (c : Constraint n) (x : Fin n → ℝ) : Prop :=
  c.fn.eval x ≤ 0

end Constraint

/-- Given [an affine constraint system](hyp:Γ), its [strict cell](goal) is given by [the
points satisfying every listed constraint using its original comparison](step:1).

The strict cell of a finite mixed affine system. -/
def strictCell {n : ℕ} (Γ : AffineSystem n) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, c.strictHolds x}

/-- Given [an affine constraint system](hyp:Γ), its [weak relaxation](goal) is given by [the
points weakly satisfying every listed constraint](step:1).

The weak relaxation of a finite mixed affine system. -/
def weakCell {n : ℕ} (Γ : AffineSystem n) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, c.weakHolds x}

/-- Given [a point](hyp:x), [membership in the strict cell](goal) is equivalent to [satisfying
every listed constraint with its original comparison](step:1). -/
@[simp] theorem mem_strictCell {n : ℕ} {Γ : AffineSystem n} {x : Fin n → ℝ} :
    x ∈ strictCell Γ ↔ ∀ c ∈ Γ, c.strictHolds x := Iff.rfl

/-- Given [a point](hyp:x), [membership in the weak relaxation](goal) is equivalent to
[weakly satisfying every listed constraint](step:1). -/
@[simp] theorem mem_weakCell {n : ℕ} {Γ : AffineSystem n} {x : Fin n → ℝ} :
    x ∈ weakCell Γ ↔ ∀ c ∈ Γ, c.weakHolds x := Iff.rfl

/-- Given [an affine constraint system](hyp:Γ), [every strictly feasible point belongs to its
weak relaxation](goal). -/
theorem strictCell_subset_weakCell {n : ℕ} (Γ : AffineSystem n) :
    strictCell Γ ⊆ weakCell Γ := by
  intro x hx c hc
  have h := hx c hc
  cases hkind : c.kind with
  | weak => simpa [Constraint.strictHolds, Constraint.weakHolds, hkind] using h
  | strict => exact le_of_lt (by simpa [Constraint.strictHolds, hkind] using h)

/-- Given [an affine constraint system](hyp:Γ), [its weak relaxation is closed](goal). -/
theorem isClosed_weakCell {n : ℕ} (Γ : AffineSystem n) : IsClosed (weakCell Γ) := by
  induction Γ with
  | nil => simp [weakCell]
  | cons c Γ ih =>
      rw [show weakCell (c :: Γ) = {x | c.fn.eval x ≤ 0} ∩ weakCell Γ by
        ext x
        simp [weakCell, Constraint.weakHolds]]
      exact (isClosed_le c.fn.continuous_eval continuous_const).inter ih

/-- Given [an affine constraint system](hyp:Γ), [its weak relaxation is convex](goal). -/
theorem convex_weakCell {n : ℕ} (Γ : AffineSystem n) : Convex ℝ (weakCell Γ) := by
  intro x hx y hy a b ha hb hab c hc
  have hxc := hx c hc
  have hyc := hy c hc
  unfold Constraint.weakHolds at hxc hyc ⊢
  have hab' : a = 1 - b := by linarith
  rw [hab', AffineFn.eval_affineCombination]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (by linarith) hxc)
    (mul_nonpos_of_nonneg_of_nonpos hb hyc)

end Causalean.Mathlib.Optimization.AffineSignCellClosure
