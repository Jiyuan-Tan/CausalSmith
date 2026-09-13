/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Raw moments of a measure on the real line

This module fixes the single raw-moment notation shared by the `MomentProblems` developments: the
order-`k` raw moment of a measure on the real line is the Bochner integral of the `k`-th power.
Both the finite-moment near-Gaussian perturbation construction and the measure bridge for the
quadratic projection residual are stated in terms of it.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory

/-- Given [a real measure](hyp:ν) and [a nonnegative integer order](hyp:k), the [raw moment](goal)
is [given by integrating the corresponding power](step:1). This is the real-valued Bochner
integral, which is zero when the power is not integrable, so it is the moment only when the moment
exists. -/
noncomputable def rawMoment (ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, x ^ k ∂ν

/-- For [a real measure](hyp:ν) at [a nonnegative integer order](hyp:k), [the raw-moment
notation equals the integral of the corresponding power](goal). -/
@[simp] theorem rawMoment_eq_integral (ν : Measure ℝ) (k : ℕ) :
    rawMoment ν k = ∫ x, x ^ k ∂ν := rfl

end Causalean.Stat.MomentProblems
