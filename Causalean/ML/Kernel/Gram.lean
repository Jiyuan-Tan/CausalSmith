/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! # Gram matrices of a kernel

The file defines the Gram matrix `gram k x`, the positive-semidefinite-kernel
predicate `IsPSDkernel`, and the regularized-Gram positive-definiteness theorem
`gram_add_lambda_posDef`: if `k` is positive semidefinite and `λ > 0`, then
`K + λI ≻ 0`.  This is the finite-sample invertibility fact used by kernel ridge
regression.
-/

namespace Causalean.ML

open Matrix

/-- For [an input space](hyp:X), [a sample size](hyp:n), [a real-valued kernel on that
space](hyp:k), and [a sample of that size](hyp:x), the [Gram matrix](goal) is the matrix whose
row-$i$, column-$j$ entry is the kernel evaluated at the $i$th and $j$th sample points. -/
def gram {X : Type*} {n : ℕ} (k : X → X → ℝ) (x : Fin n → X) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => k (x i) (x j)

/-- For [an input space](hyp:X) and [a real-valued kernel on that space](hyp:k), the
[positive-semidefinite-kernel property](goal) holds exactly when, for every finite sample,
its Gram matrix is positive semidefinite. -/
def IsPSDkernel {X : Type*} (k : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X), (gram k x).PosSemidef

/-- For a finite sample `x` and kernel `k`, if [`k` is positive semidefinite, i.e. every
Gram matrix it produces is PSD](hyp:hk) and [the regularization level `lam` is strictly
positive](hyp:hlam), then [the regularized Gram matrix `gram k x + lam·I` is positive
definite, hence invertible](goal). -/
theorem gram_add_lambda_posDef {X : Type*} {n : ℕ} {k : X → X → ℝ}
    (hk : IsPSDkernel k) (x : Fin n → X) {lam : ℝ} (hlam : 0 < lam) :
    (gram k x + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hpsd : (gram k x).PosSemidef := hk n x
  have hI : (lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    exact Matrix.PosDef.smul Matrix.PosDef.one hlam
  exact Matrix.PosDef.posSemidef_add hpsd hI

end Causalean.ML
