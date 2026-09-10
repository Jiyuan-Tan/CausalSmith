/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge vector (K-regressor) TWFE normal equation

The scalar `ScalarTWFEProblem` is the `K = Fin 1` specialization of the
K-vector TWFE problem, whose full-rank condition is the nonsingularity of the
residualized Gram matrix `Q_{\ddot X} ∈ R^{K×K}`. We build the matrix normal equation, prove
existence and uniqueness of the closed-form coefficient under matrix
invertibility, and show the scalar problem embeds as the singleton-`K` case.

The vector double-demeaned array is component-wise scalar double demeaning, so
all the uniform-panel orthogonality infrastructure is reused.
-/

import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.TWFE
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul

/-! # Wooldridge Vector TWFE

This file defines the finite-dimensional vector-regressor version of
Wooldridge's two-way fixed effects normal equation on a balanced panel. It
constructs the componentwise residual `ddotVec`, residualized Gram matrix
`gram`, numerator `numer`, and `VectorTWFEProblem.betaTWFE`.  It proves
`vecNormalEq_iff_mulVec`, `VectorTWFEProblem.betaTWFE_normalEq`, and
`VectorTWFEProblem.betaTWFE_unique`, then relates the scalar problem to the
one-coordinate case with `ScalarTWFEProblem.toVector` and
`ScalarTWFEProblem.toVector_betaTWFE`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open Finset
open UniformTwoWayPanel

variable {Unit Time : Type*} [Fintype Unit] [Fintype Time]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- For [finite unit, time-period, and regressor-coordinate sets](hyp:Unit,Time,K), [a vector-valued regressor array](hyp:X), [a unit](hyp:i), [a time period](hyp:t),
and [a regressor coordinate](hyp:k), the [componentwise double-demeaned regressor](goal) is
the scalar double demean of that coordinate over the finite balanced panel. -/
noncomputable def ddotVec (X : Unit → Time → K → ℝ) (i : Unit) (t : Time) (k : K) : ℝ :=
  ddot (fun i t => X i t k) i t

/-- For [finite unit, time-period, and regressor-coordinate sets](hyp:Unit,Time,K) and [a vector-valued regressor array](hyp:X), the [residualized Gram matrix](goal) has
entry $(j,k)$ equal to the finite sum, over units and time periods, of the product of the
double-demeaned $j$-th and $k$-th regressor coordinates. -/
noncomputable def gram (X : Unit → Time → K → ℝ) : Matrix K K ℝ :=
  fun j k => ∑ i, ∑ t, ddotVec X i t j * ddotVec X i t k

/-- For [finite unit, time-period, and regressor-coordinate sets](hyp:Unit,Time,K), [a vector-valued regressor array](hyp:X), and [an outcome array](hyp:Y), the
[residualized numerator vector](goal) has coordinate $k$ equal to the finite sum of the
product of the double-demeaned $k$-th regressor and the double-demeaned outcome. -/
noncomputable def numer (X : Unit → Time → K → ℝ) (Y : Unit → Time → ℝ) : K → ℝ :=
  fun k => ∑ i, ∑ t, ddotVec X i t k * ddot Y i t

/-- A K-vector two-way-fixed-effects regression problem on [a finite balanced panel of units and
time periods](hyp:panel), given [a scalar outcome](hyp:Y) and [a K-vector of
regressors](hyp:X), where [the residualized Gram matrix of the double-demeaned regressors is
nonsingular — the vector full-rank condition ensuring the two-way within estimator is well
defined](hyp:gram_unit). -/
structure VectorTWFEProblem (Unit Time : Type*) [Fintype Unit] [Fintype Time]
    (K : Type*) [Fintype K] [DecidableEq K] where
  panel : BalancedPanel Unit Time
  Y : Unit → Time → ℝ
  X : Unit → Time → K → ℝ
  gram_unit : IsUnit (gram X).det

namespace VectorTWFEProblem

/-- For [finite unit, time-period, and regressor-coordinate sets](hyp:Unit,Time,K) and [a vector two-way-fixed-effects problem](hyp:P), the [closed-form vector TWFE
coefficient](goal) is the inverse residualized Gram matrix multiplied by the residualized
outcome-regressor numerator vector. -/
noncomputable def betaTWFE (P : VectorTWFEProblem Unit Time K) : K → ℝ :=
  (gram P.X)⁻¹.mulVec (numer P.X P.Y)

/-- For [finite unit, time-period, and regressor-coordinate sets](hyp:Unit,Time,K), [a vector two-way-fixed-effects problem](hyp:P), and [a candidate coefficient
vector](hyp:β), the [vector TWFE normal-equation condition](goal) requires that, for every
regressor coordinate, the finite inner product of its double-demeaned regressor with the
double-demeaned outcome residual is zero. -/
def vecTwfeNormalEq (P : VectorTWFEProblem Unit Time K) (β : K → ℝ) : Prop :=
  ∀ k, ∑ i, ∑ t,
    ddotVec P.X i t k * (ddot P.Y i t - ∑ j, ddotVec P.X i t j * β j) = 0

end VectorTWFEProblem

omit [DecidableEq K] in
/-- The coordinate-wise normal equation is equivalent to the matrix normal
equation `Q_{\ddot X} β = Σ_it ddot X ddot Y`. -/
theorem vecNormalEq_iff_mulVec (X : Unit → Time → K → ℝ) (Y : Unit → Time → ℝ)
    (β : K → ℝ) :
    (∀ k, ∑ i, ∑ t,
        ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j) = 0)
      ↔ (gram X).mulVec β = numer X Y := by
  have key : ∀ k, ∑ i, ∑ t,
      ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j)
        = numer X Y k - (gram X).mulVec β k := by
    intro k
    have hmv : (gram X).mulVec β k
        = ∑ j, (∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j) * β j := by
      simp only [Matrix.mulVec, dotProduct, gram]
    rw [hmv]
    change ∑ i, ∑ t, ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j)
      = (∑ i, ∑ t, ddotVec X i t k * ddot Y i t)
        - ∑ j, (∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j) * β j
    -- split off the regressor term and swap the `j` sum outward
    have hsplit : ∑ i, ∑ t, ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j)
        = (∑ i, ∑ t, ddotVec X i t k * ddot Y i t)
          - ∑ i, ∑ t, ∑ j, ddotVec X i t k * ddotVec X i t j * β j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsplit]
    congr 1
    -- reorder ∑ i ∑ t ∑ j → ∑ j ∑ i ∑ t and pull `β j` out of the i,t sums
    calc ∑ i, ∑ t, ∑ j, ddotVec X i t k * ddotVec X i t j * β j
        = ∑ i, ∑ j, ∑ t, ddotVec X i t k * ddotVec X i t j * β j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j * β j := by
          rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j) * β j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
  constructor
  · intro h
    funext k
    have := key k
    rw [h k] at this
    -- 0 = numer k - mulVec k  ⇒ mulVec k = numer k
    linarith [this]
  · intro h k
    rw [key k, h]
    ring

namespace VectorTWFEProblem

/-- **Existence of a TWFE solution.** For [a vector two-way-fixed-effects problem, whose
residualized Gram matrix is nonsingular by assumption](hyp:P), [the closed-form coefficient
`P.betaTWFE` solves the matrix normal equation defining the TWFE coefficient](goal). -/
theorem betaTWFE_normalEq (P : VectorTWFEProblem Unit Time K) :
    P.vecTwfeNormalEq P.betaTWFE := by
  rw [vecTwfeNormalEq, vecNormalEq_iff_mulVec]
  change (gram P.X).mulVec ((gram P.X)⁻¹.mulVec (numer P.X P.Y)) = numer P.X P.Y
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ P.gram_unit, Matrix.one_mulVec]

/-- **Full-rank uniqueness of the vector TWFE coefficient.** For a vector TWFE
problem `P` with nonsingular residualized Gram matrix, if [a coefficient vector
`β` satisfies the coordinate-wise TWFE normal equation — in every coordinate
the double-demeaned regressor is orthogonal to the double-demeaned
residual](hyp:hβ), then [`β` equals the closed-form vector TWFE coefficient
`P.betaTWFE`](goal). -/
theorem betaTWFE_unique (P : VectorTWFEProblem Unit Time K) {β : K → ℝ}
    (hβ : P.vecTwfeNormalEq β) :
    β = P.betaTWFE := by
  have h : (gram P.X).mulVec β = numer P.X P.Y :=
    (vecNormalEq_iff_mulVec P.X P.Y β).mp hβ
  change β = (gram P.X)⁻¹.mulVec (numer P.X P.Y)
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ P.gram_unit, Matrix.one_mulVec]

end VectorTWFEProblem

/-- For [finite unit and time-period sets](hyp:Unit,Time) and [a scalar two-way-fixed-effects problem](hyp:P), the [associated one-coordinate vector
two-way-fixed-effects problem](goal) has the same panel and outcome, uses the scalar regressor
as its sole coordinate, and has a nonsingular residualized Gram matrix because the scalar
double-demeaned regressor has a strictly positive sum of squares.

The scalar TWFE problem embeds as the singleton-`K = Fin 1` vector problem:
the regressor is the same scalar in the single coordinate and the matrix
full-rank condition reduces to the scalar `ddotX_ss_pos`. -/
noncomputable def ScalarTWFEProblem.toVector (P : ScalarTWFEProblem Unit Time) :
    VectorTWFEProblem Unit Time (Fin 1) where
  panel := P.panel
  Y := P.Y
  X := fun i t _ => P.X i t
  gram_unit := by
    have hval : (gram (fun i t (_ : Fin 1) => P.X i t)).det
        = ∑ i, ∑ t, (ddot P.X i t) ^ 2 := by
      rw [Matrix.det_fin_one]
      simp only [gram, ddotVec]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun t _ => ?_))
      rw [pow_two]
    rw [hval]
    exact (isUnit_iff_ne_zero).mpr (ne_of_gt P.ddotX_ss_pos)

/-- The singleton-coordinate vector TWFE coefficient recovers the scalar TWFE
coefficient, so the scalar theorem is the `K = Fin 1` case of the vector one. -/
theorem ScalarTWFEProblem.toVector_betaTWFE (P : ScalarTWFEProblem Unit Time) :
    P.toVector.betaTWFE 0 = P.betaTWFE := by
  have hsol : P.toVector.vecTwfeNormalEq (fun _ => P.betaTWFE) := by
    intro k
    have h := P.betaTWFE_normalEq
    rw [ScalarTWFEProblem.twfeNormalEq] at h
    simpa [VectorTWFEProblem.vecTwfeNormalEq, ScalarTWFEProblem.toVector, ddotVec,
      Fin.sum_univ_one] using h
  have heq := P.toVector.betaTWFE_unique hsol
  rw [← heq]

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
