/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Quadratic Variance Form

This file provides the deterministic layer for finite covariance quadratic-form
comparisons. The definition `quadVar S w = w ⬝ᵥ S *ᵥ w` is the
weight-covariance-weight variance functional for a finite linear estimator, and
`SphericalErrors S σ` records the scalar-identity covariance condition
`S = σ² • I`.

The main reusable facts are `quadVar_nonneg`, nonnegativity under a
positive-semidefinite covariance matrix, and `quadVar_spherical`, the reduction
`quadVar S w = σ² * (w ⬝ᵥ w)` under spherical errors.  The probability-theoretic
bridge to actual random variables is in `GaussMarkov/Variance.lean`; the
quadratic-form ordering theorems are in `GaussMarkov/LeastNorm.lean`. -/

@[expose] public section

namespace Causalean.Stat.GaussMarkov

open Matrix

variable {Obs : Type*} [Fintype Obs]

/-- For [a finite observation index set](hyp:Obs), [a real covariance matrix indexed by
that set](hyp:S), and [a real weight assigned to each observation](hyp:w), the
[quadratic variance form](goal) is $w^\mathsf{T} S w$.

This is the deterministic algebraic object; the bridge to
`ProbabilityTheory.variance` of an actual random linear combination is
`variance_linearCombination` in `Variance.lean`. -/
def quadVar (S : Matrix Obs Obs ℝ) (w : Obs → ℝ) : ℝ := w ⬝ᵥ S *ᵥ w

/-- The quadratic variance form unfolds to the weight-covariance-weight product. -/
lemma quadVar_def (S : Matrix Obs Obs ℝ) (w : Obs → ℝ) :
    quadVar S w = w ⬝ᵥ S *ᵥ w := rfl

/-- A positive-semidefinite covariance matrix gives a nonnegative variance for
every linear weight. -/
lemma quadVar_nonneg {S : Matrix Obs Obs ℝ} (hS : S.PosSemidef) (w : Obs → ℝ) :
    0 ≤ quadVar S w := by
  have h := hS.dotProduct_mulVec_nonneg w
  simpa [quadVar] using h

variable [DecidableEq Obs]

/-- For [an observation index set in which equality can be decided](hyp:Obs), [a
real square matrix indexed by those observations](hyp:S), and [a real scale
parameter](hyp:σ), the [spherical-errors condition](goal) holds exactly when the
matrix equals $σ^2$ times the identity matrix. -/
def SphericalErrors (S : Matrix Obs Obs ℝ) (σ : ℝ) : Prop :=
  S = σ ^ 2 • (1 : Matrix Obs Obs ℝ)

/-- [Under spherical errors, i.e. when the error covariance matrix `S` equals `σ²` times
the identity](hyp:h), [the linear-estimator variance functional at weight vector `w` reduces
to the common variance `σ²` times the squared Euclidean length of `w`](goal). -/
lemma quadVar_spherical {S : Matrix Obs Obs ℝ} {σ : ℝ} (h : SphericalErrors S σ)
    (w : Obs → ℝ) : quadVar S w = σ ^ 2 * (w ⬝ᵥ w) := by
  subst h
  rw [quadVar, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

end Causalean.Stat.GaussMarkov
