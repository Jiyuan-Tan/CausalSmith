/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform polynomial approximation on a compact real interval

This module defines the compact-interval supremum norm, the uniform error of a
real polynomial against a target, and the best error under a degree bound.
The definitions are shared by the Markov and alternation developments.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- The compact-interval supremum norm of a real function is the supremum of
its absolute values on the indicated closed interval. [the stated inputs](hyp:g,r,s) establish [the defined object](goal). -/
noncomputable def intervalSupNorm (g : ℝ → ℝ) (r s : ℝ) : ℝ :=
  sSup ((fun x => |g x|) '' Set.Icc r s)

/-- The uniform error of a polynomial against a real target on a closed
interval is the compact-interval supremum norm of their residual. [the stated inputs](hyp:f,r,s,Q) establish [the defined object](goal). -/
noncomputable def uniformApproxError
    (f : ℝ → ℝ) (r s : ℝ) (Q : Polynomial ℝ) : ℝ :=
  intervalSupNorm (fun x => f x - Q.eval x) r s

/-- The best degree-`L` uniform polynomial-approximation error is the infimum
of the uniform errors of all real polynomials of degree at most `L`. [the stated inputs](hyp:f,r,s,L) establish [the defined object](goal). -/
noncomputable def bestUniformApproxError
    (f : ℝ → ℝ) (r s : ℝ) (L : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ Q : Polynomial ℝ,
    Q.natDegree ≤ L ∧ e = uniformApproxError f r s Q}

/-- For a continuous function on a nonempty closed interval, its interval
supremum norm is at most `C` exactly when every pointwise absolute value is at
most `C`. [the stated inputs](hyp:g,r,s,C,hg,hrs) establish [the stated conclusion](goal). -/
theorem intervalSupNorm_le_iff {g : ℝ → ℝ} {r s C : ℝ}
    (hg : ContinuousOn g (Set.Icc r s)) (hrs : r ≤ s) :
    intervalSupNorm g r s ≤ C ↔ ∀ x ∈ Set.Icc r s, |g x| ≤ C := by
  -- Proof plan: apply `IsCompact.exists_sSup_image_eq_and_ge` to `x ↦ |g x|`,
  -- then unfold the image in `intervalSupNorm`.
  unfold intervalSupNorm
  constructor
  · intro h x hx
    exact (le_csSup (isCompact_Icc.bddAbove_image hg.abs) ⟨x, hx, rfl⟩).trans h
  · intro h
    apply csSup_le
    · exact ⟨|g r|, ⟨r, ⟨le_rfl, hrs⟩, rfl⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      exact h x hx

/-- On a nonempty interval, the uniform approximation error is nonnegative. [the stated inputs](hyp:f,r,s,hrs,Q) establish [the stated conclusion](goal). -/
theorem uniformApproxError_nonneg {f : ℝ → ℝ} {r s : ℝ}
    (hrs : r ≤ s) (Q : Polynomial ℝ) :
    0 ≤ uniformApproxError f r s Q := by
  -- Proof plan: split on boundedness of the residual image.  In the bounded
  -- case compare the supremum with the residual at `r`; in the unbounded case
  -- use the convention for `sSup` of an unbounded real set.
  unfold uniformApproxError intervalSupNorm
  apply Real.sSup_nonneg
  rintro y ⟨x, hx, rfl⟩
  exact abs_nonneg _

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
