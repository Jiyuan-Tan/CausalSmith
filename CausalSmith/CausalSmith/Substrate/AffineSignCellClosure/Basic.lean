import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite affine sign cells

This module defines finite systems of real affine inequalities, their mixed strict/weak
solution cells, and the elementary closedness and convexity facts for the weak relaxation.
-/

open scoped BigOperators Topology
open Set Filter

namespace CausalSmith.Substrate.AffineSignCellClosure

/-- An affine real-valued function on `Fin n → ℝ`, stored as a coefficient vector and a
constant term. -/
structure AffineFn (n : ℕ) where
  /-- The coefficient of each coordinate. -/
  coeff : Fin n → ℝ
  /-- The constant term. -/
  constant : ℝ

namespace AffineFn

/-- Evaluation of an affine function is its finite dot product plus its constant term. -/
def eval {n : ℕ} (f : AffineFn n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, f.coeff i * x i + f.constant

/-- Evaluation at an affine combination is the corresponding affine combination of the
two evaluations when the scalar weights sum to one. -/
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

/-- Every finitely supported coordinate affine function is continuous. -/
theorem continuous_eval {n : ℕ} (f : AffineFn n) : Continuous f.eval := by
  unfold eval
  fun_prop

end AffineFn

/-- A constraint is either weak, interpreted as `f x ≤ 0`, or strict, interpreted as
`f x < 0`. -/
inductive ConstraintKind where
  | weak
  | strict
  deriving DecidableEq, Repr

/-- A marked affine constraint consists of an affine function and its weak/strict kind. -/
structure Constraint (n : ℕ) where
  /-- The affine left-hand side, normalized against zero. -/
  fn : AffineFn n
  /-- Whether the normalized inequality is weak or strict. -/
  kind : ConstraintKind

/-- A finite affine constraint system is a list of marked affine constraints. -/
abbrev AffineSystem (n : ℕ) := List (Constraint n)

namespace Constraint

/-- A point strictly satisfies a marked constraint when it satisfies the indicated weak
or strict comparison. -/
def strictHolds {n : ℕ} (c : Constraint n) (x : Fin n → ℝ) : Prop :=
  match c.kind with
  | .weak => c.fn.eval x ≤ 0
  | .strict => c.fn.eval x < 0

/-- A point weakly satisfies a marked constraint when it satisfies the weak comparison,
regardless of the original mark. -/
def weakHolds {n : ℕ} (c : Constraint n) (x : Fin n → ℝ) : Prop :=
  c.fn.eval x ≤ 0

end Constraint

/-- The strict cell of a finite system contains the points satisfying every constraint
with its original weak or strict comparison. -/
def strictCell {n : ℕ} (Γ : AffineSystem n) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, c.strictHolds x}

/-- The weak relaxation of a finite system replaces every strict comparison by a weak one. -/
def weakCell {n : ℕ} (Γ : AffineSystem n) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, c.weakHolds x}

/-- Membership in the strict cell unfolds to satisfaction of every listed marked
constraint. -/
@[simp] theorem mem_strictCell {n : ℕ} {Γ : AffineSystem n} {x : Fin n → ℝ} :
    x ∈ strictCell Γ ↔ ∀ c ∈ Γ, c.strictHolds x :=
  Iff.rfl

/-- Membership in the weak cell unfolds to weak satisfaction of every listed constraint. -/
@[simp] theorem mem_weakCell {n : ℕ} {Γ : AffineSystem n} {x : Fin n → ℝ} :
    x ∈ weakCell Γ ↔ ∀ c ∈ Γ, c.weakHolds x :=
  Iff.rfl

/-- Every point of the strict cell belongs to its weak relaxation. -/
theorem strictCell_subset_weakCell {n : ℕ} (Γ : AffineSystem n) :
    strictCell Γ ⊆ weakCell Γ := by
  intro x hx c hc
  have h := hx c hc
  cases hkind : c.kind with
  | weak =>
      simpa [Constraint.strictHolds, Constraint.weakHolds, hkind] using h
  | strict =>
      exact le_of_lt (by
        simpa [Constraint.strictHolds, hkind] using h)

/-- The weak relaxation of a finite affine constraint system is closed. -/
theorem isClosed_weakCell {n : ℕ} (Γ : AffineSystem n) : IsClosed (weakCell Γ) := by
  induction Γ with
  | nil =>
      simp [weakCell]
  | cons c Γ ih =>
      rw [show weakCell (c :: Γ) =
          {x | c.fn.eval x ≤ 0} ∩ weakCell Γ by
        ext x
        simp [weakCell, Constraint.weakHolds]]
      exact (isClosed_le c.fn.continuous_eval continuous_const).inter ih

/-- The weak relaxation of a finite affine constraint system is convex. -/
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

end CausalSmith.Substrate.AffineSignCellClosure
