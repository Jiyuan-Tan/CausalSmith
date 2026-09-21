/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.TiltTangent

/-!
# Von Mises remainders imply bounded-tilt pathwise derivatives

This module packages the generic analytic step behind influence-function
calculations: a first-order von Mises expansion whose remainder is locally
quadratic along a bounded exponential tilt differentiates to the covariance
of the expansion's representer with the tilt score.

Reference: Kennedy (2024), *Semiparametric doubly robust targeted double
machine learning: a review*.
-/

public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Asymptotics Filter MeasureTheory Real Topology

variable {Z : Type*} [MeasurableSpace Z]

/-- **Quadratic von Mises remainder recipe.** Given [a probability law `P`](hyp:P),
[a law functional `ψ`](hyp:ψ), [a square-integrable first-order representer `φ`](hyp:φ,hφ),
and [a measurable bounded mean-zero tilt score `g`](hyp:g,hg_meas,hgM,hg_mean), suppose
[the von Mises expansion error along that tilt is eventually bounded by `C t²`](hyp:hrem).
Then [`t ↦ ψ(tiltMeasure P g t)` has derivative `∫ φg dP` at zero](goal).

The signed-measure expression `∫ φ d(P_t-P)` is written as the equivalent difference
`∫ φ dP_t - ∫ φ dP`, since positive measures do not form an additive group in Lean. -/
theorem hasDerivAt_tilt_of_quadratic_vonMises_remainder
    (P : Measure Z) [IsProbabilityMeasure P]
    (ψ : Measure Z → ℝ) (φ g : Z → ℝ) (M C : ℝ)
    (hφ : MemLp φ 2 P)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0)
    (hrem : ∀ᶠ t in 𝓝 (0 : ℝ),
      |ψ (tiltMeasure P g t) - ψ P -
        ((∫ z, φ z ∂(tiltMeasure P g t)) - ∫ z, φ z ∂P)| ≤ C * t ^ 2) :
    HasDerivAt (fun t => ψ (tiltMeasure P g t)) (∫ z, φ z * g z ∂P) 0 := by
  let F : ℝ → ℝ := fun t => ψ (tiltMeasure P g t)
  let A : ℝ → ℝ := fun t =>
    (∫ z, φ z ∂(tiltMeasure P g t)) - ∫ z, φ z ∂P
  let R : ℝ → ℝ := fun t => F t - F 0 - A t
  have hR0 : R 0 = 0 := by
    simp [R, F, A, tiltMeasure_zero]
  have hquad : ∀ᶠ t in 𝓝 (0 : ℝ), |R t| ≤ C * t ^ 2 := by
    filter_upwards [hrem] with t ht
    simpa [R, F, A, tiltMeasure_zero] using ht
  have hbig : R =O[𝓝 (0 : ℝ)] fun t : ℝ => t ^ 2 := by
    refine IsBigO.of_bound (|C| + 1) ?_
    filter_upwards [hquad] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    exact ht.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_abs_self C) (le_add_of_nonneg_right zero_le_one)) (sq_nonneg t))
  have hsmall : R =o[𝓝 (0 : ℝ)] fun t : ℝ => t :=
    hbig.trans_isLittleO (isLittleO_pow_id (by norm_num : 1 < 2))
  have hRderiv : HasDerivAt R 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa [hR0] using hsmall
  have hAderiv : HasDerivAt A (∫ z, φ z * g z ∂P) 0 := by
    dsimp only [A]
    exact (hasDerivAt_integral_tiltMeasure_of_memLp hg_meas hgM hg_mean hφ).sub_const
      (∫ z, φ z ∂P)
  have hsum := (hRderiv.add_const (F 0)).add hAderiv
  have heq : F = fun t => R t + F 0 + A t := by
    funext t
    dsimp [R]
    ring
  rw [show (fun t => ψ (tiltMeasure P g t)) = F from rfl, heq]
  change HasDerivAt ((fun x => R x + F 0) + A) (∫ z, φ z * g z ∂P) 0
  simpa only [zero_add] using hsum

end Causalean.Estimation.Efficiency
