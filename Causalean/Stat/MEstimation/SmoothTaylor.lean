/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Taylor bounds from locally Lipschitz derivatives

This module provides the Banach-space Taylor remainder bound shared by smooth
Z-estimation and smooth GMM. It turns a derivative Lipschitz bound on a closed
ball into a quadratic first-order remainder bound between the ball's center
and any comparison point in the ball.
-/

public section

namespace Causalean.Stat

open Set

variable {Θ V : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For [a Banach-space-valued function and its derivative field](hyp:f,D),
[a center and comparison point](hyp:θ₀,θ), suppose [the derivative field is the
Fréchet derivative everywhere](hyp:hD), [its changes on a closed ball are
bounded by a nonnegative Lipschitz constant](hyp:hLnonneg,hLbound), and [the
comparison point lies in that ball](hyp:hθ). Then [the first-order Taylor
remainder between the center and comparison point is bounded by the Lipschitz
constant times their squared distance](goal). -/
theorem norm_taylor_remainder_le_of_fderiv_lipschitz
    (f : Θ → V) (D : Θ → (Θ →L[ℝ] V)) (θ₀ θ : Θ)
    {L δ : ℝ}
    (hLnonneg : 0 ≤ L)
    (hLbound : ∀ η ∈ Metric.closedBall θ₀ δ,
      ∀ η' ∈ Metric.closedBall θ₀ δ,
        ‖D η - D η'‖ ≤ L * ‖η - η'‖)
    (hD : ∀ η, HasFDerivAt f (D η) η)
    (hθ : θ ∈ Metric.closedBall θ₀ δ) :
    ‖f θ - f θ₀ - D θ₀ (θ - θ₀)‖ ≤ L * ‖θ - θ₀‖ ^ 2 := by
  have hδ0 : (0 : ℝ) ≤ δ :=
    le_trans dist_nonneg (Metric.mem_closedBall.mp hθ)
  have hθ₀ : θ₀ ∈ Metric.closedBall θ₀ δ := Metric.mem_closedBall_self hδ0
  let s : Set Θ := segment ℝ θ₀ θ
  have hs : Convex ℝ s := convex_segment θ₀ θ
  have hsub : s ⊆ Metric.closedBall θ₀ δ :=
    (convex_closedBall θ₀ δ).segment_subset hθ₀ hθ
  have hderiv : ∀ η ∈ s, HasFDerivWithinAt f (D η) s η := by
    intro η _
    exact (hD η).hasFDerivWithinAt
  have hbound : ∀ η ∈ s, ‖D η - D θ₀‖ ≤ L * ‖θ - θ₀‖ := by
    intro η hη
    exact (hLbound η (hsub hη) θ₀ hθ₀).trans <|
      mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hη) hLnonneg
  have hmv := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    hderiv hbound (left_mem_segment ℝ θ₀ θ) (right_mem_segment ℝ θ₀ θ)
  calc
    ‖f θ - f θ₀ - D θ₀ (θ - θ₀)‖
        ≤ (L * ‖θ - θ₀‖) * ‖θ - θ₀‖ := hmv
    _ = L * ‖θ - θ₀‖ ^ 2 := by ring

end Causalean.Stat
