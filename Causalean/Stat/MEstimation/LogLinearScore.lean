/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The log-linear (Poisson) score is locally but not globally Lipschitz

This module is the worked counterexample motivating the neighbourhood form of the Lipschitz
hypotheses in `Stat/EmpiricalProcess/Equicontinuity/` and `Stat/MEstimation/SmoothZEstimator.lean`.

For Poisson regression with a log link the observationwise score is
`ψ(θ, (x,y)) = (y - exp (θ x)) x`, with parameter derivative `-(exp (θ x) x²)`.  Two facts about
that derivative are proved here:

* on any ball around a target it is Lipschitz in the parameter, with the explicit envelope
  `|x|³ exp ((|θ₀| + δ) |x|)`, which is integrable under a standard exponential-moment condition
  on the regressor;
* there is **no** global Lipschitz envelope at all — already for the single observation with
  regressor and outcome one, the requirement is contradicted, because `exp` outgrows every
  linear function.

Together these say the neighbourhood hypothesis is satisfiable exactly where the global one is
not, so localizing it is what admits Poisson regression, exponential-mean GMM and nonlinear
least squares with an exponential link.
-/

@[expose] public section

namespace Causalean.Stat

open Set

/-- For [a parameter](hyp:θ) and [an observation consisting of a regressor and an
outcome](hyp:z), the [log-link Poisson score](goal) is the regressor times the outcome's
deviation from the modeled mean `exp (θ x)`. -/
noncomputable def logLinearScore (θ : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.2 - Real.exp (θ * z.1)) * z.1

/-- For [a parameter](hyp:θ) and [an observation](hyp:z), the [parameter derivative of the
log-link Poisson score](goal) is minus the modeled mean times the squared regressor. -/
noncomputable def logLinearScoreDeriv (θ : ℝ) (z : ℝ × ℝ) : ℝ :=
  -(Real.exp (θ * z.1) * z.1 ^ 2)

/-- For [a parameter](hyp:θ) and [an observation](hyp:z), [the log-link Poisson score is
differentiable in the parameter with the stated derivative](goal). -/
theorem hasDerivAt_logLinearScore (θ : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun s => logLinearScore s z) (logLinearScoreDeriv θ z) θ := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * z.1)) (Real.exp (θ * z.1) * z.1) θ := by
    simpa using ((hasDerivAt_id θ).mul_const z.1).exp
  have h : HasDerivAt (fun s : ℝ => (z.2 - Real.exp (s * z.1)) * z.1)
      ((0 - Real.exp (θ * z.1) * z.1) * z.1) θ :=
    ((hasDerivAt_const θ z.2).sub hexp).mul_const z.1
  have hval : logLinearScoreDeriv θ z = (0 - Real.exp (θ * z.1) * z.1) * z.1 := by
    simp only [logLinearScoreDeriv]
    ring
  rw [hval]
  exact h

/-- For [an observation](hyp:z), [a target](hyp:θ₀), and [two parameters in the ball of radius
`δ` around it](hyp:θ,hθ,θ',hθ'), [the score derivative moves by at most the exponential-moment
envelope times the parameter distance](goal).

The envelope `|x|³ exp ((|θ₀| + δ) |x|)` depends on the radius, which is the point: it is finite
for each fixed `δ` and integrable under an exponential-moment condition on the regressor, whereas
no radius-free envelope exists — see `logLinearScoreDeriv_not_globally_lipschitz`. -/
theorem logLinearScoreDeriv_lipschitz_on_ball
    (z : ℝ × ℝ) (θ₀ : ℝ) {δ : ℝ}
    {θ : ℝ} (hθ : θ ∈ Metric.closedBall θ₀ δ)
    {θ' : ℝ} (hθ' : θ' ∈ Metric.closedBall θ₀ δ) :
    |logLinearScoreDeriv θ z - logLinearScoreDeriv θ' z| ≤
      (|z.1| ^ 3 * Real.exp ((|θ₀| + δ) * |z.1|)) * |θ - θ'| := by
  -- Every parameter in the ball has modulus at most `|θ₀| + δ`.
  have hball : ∀ s ∈ Metric.closedBall θ₀ δ, |s| ≤ |θ₀| + δ := by
    intro s hs
    have hs' : |s - θ₀| ≤ δ := by simpa [Real.dist_eq] using Metric.mem_closedBall.mp hs
    calc |s| = |θ₀ + (s - θ₀)| := by ring_nf
      _ ≤ |θ₀| + |s - θ₀| := abs_add_le _ _
      _ ≤ |θ₀| + δ := by linarith
  have hsub : uIcc θ' θ ⊆ Metric.closedBall θ₀ δ :=
    (convex_closedBall θ₀ δ).ordConnected.uIcc_subset hθ' hθ
  set f : ℝ → ℝ := fun s => Real.exp (s * z.1) with hf
  have hderiv : ∀ s ∈ uIcc θ' θ,
      HasDerivWithinAt f (Real.exp (s * z.1) * z.1) (uIcc θ' θ) s := by
    intro s _
    have : HasDerivAt f (Real.exp (s * z.1) * z.1) s := by
      simpa [hf] using ((hasDerivAt_id s).mul_const z.1).exp
    exact this.hasDerivWithinAt
  have hbound : ∀ s ∈ uIcc θ' θ,
      ‖Real.exp (s * z.1) * z.1‖ ≤ Real.exp ((|θ₀| + δ) * |z.1|) * |z.1| := by
    intro s hs
    have hle : s * z.1 ≤ (|θ₀| + δ) * |z.1| := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hball s (hsub hs)) (abs_nonneg _)
    have hexp : Real.exp (s * z.1) ≤ Real.exp ((|θ₀| + δ) * |z.1|) := Real.exp_le_exp.2 hle
    calc ‖Real.exp (s * z.1) * z.1‖ = Real.exp (s * z.1) * |z.1| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp ((|θ₀| + δ) * |z.1|) * |z.1| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
  have hmv := (convex_uIcc θ' θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound left_mem_uIcc right_mem_uIcc
  have hstep : |f θ - f θ'| ≤ Real.exp ((|θ₀| + δ) * |z.1|) * |z.1| * |θ - θ'| := by
    simpa [Real.norm_eq_abs] using hmv
  -- The derivative differs from `f` by the factor `x²`.
  have hfactor : |logLinearScoreDeriv θ z - logLinearScoreDeriv θ' z|
      = |f θ - f θ'| * z.1 ^ 2 := by
    simp only [logLinearScoreDeriv, hf]
    rw [show -(Real.exp (θ * z.1) * z.1 ^ 2) - -(Real.exp (θ' * z.1) * z.1 ^ 2)
        = -((Real.exp (θ * z.1) - Real.exp (θ' * z.1)) * z.1 ^ 2) by ring]
    rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg z.1)]
  rw [hfactor]
  calc |f θ - f θ'| * z.1 ^ 2
      ≤ (Real.exp ((|θ₀| + δ) * |z.1|) * |z.1| * |θ - θ'|) * z.1 ^ 2 :=
        mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    _ = (|z.1| ^ 3 * Real.exp ((|θ₀| + δ) * |z.1|)) * |θ - θ'| := by
        rw [show z.1 ^ 2 = |z.1| ^ 2 from (sq_abs z.1).symm]
        ring

/-- [No radius-free Lipschitz envelope exists for the log-link Poisson score
derivative](goal), already at the single observation whose regressor and outcome are one.

This is why the Lipschitz hypotheses in the equicontinuity and smooth Z-estimator developments
ask for a bound on a ball around the target rather than on the whole parameter space: for this
score the global requirement is not merely hard to verify, it is false. -/
theorem logLinearScoreDeriv_not_globally_lipschitz :
    ¬ ∃ L : ℝ, ∀ θ θ' : ℝ,
        |logLinearScoreDeriv θ ((1 : ℝ), (1 : ℝ))
          - logLinearScoreDeriv θ' ((1 : ℝ), (1 : ℝ))| ≤ L * |θ - θ'| := by
  rintro ⟨L, hL⟩
  have hd : ∀ t : ℝ, logLinearScoreDeriv t ((1 : ℝ), (1 : ℝ)) = -Real.exp t := by
    intro t
    simp [logLinearScoreDeriv]
  -- Comparing `θ` with `θ + 1` forces `exp θ (e - 1) ≤ L` for every `θ`.
  have key : ∀ θ : ℝ, Real.exp θ * (Real.exp 1 - 1) ≤ L := by
    intro θ
    have h := hL (θ + 1) θ
    rw [hd, hd] at h
    have hlt : Real.exp θ < Real.exp (θ + 1) := Real.exp_lt_exp.2 (by linarith)
    have habs : |(-Real.exp (θ + 1)) - (-Real.exp θ)| = Real.exp (θ + 1) - Real.exp θ := by
      rw [show (-Real.exp (θ + 1)) - (-Real.exp θ)
          = -(Real.exp (θ + 1) - Real.exp θ) by ring, abs_neg,
        abs_of_pos (by linarith)]
    rw [habs, show |θ + 1 - θ| = 1 by norm_num, mul_one, Real.exp_add] at h
    nlinarith [Real.exp_pos θ]
  -- But `exp` is unbounded above.
  have he : (0 : ℝ) < Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  -- `x + 1 ≤ exp x` already outruns any bound, no logarithm needed.
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, L / (Real.exp 1 - 1) < Real.exp θ := by
    refine ⟨L / (Real.exp 1 - 1), ?_⟩
    linarith [Real.add_one_le_exp (L / (Real.exp 1 - 1))]
  have hcontra := key θ
  rw [← le_div_iff₀ he] at hcontra
  exact absurd hcontra (not_le.2 hθ)

end Causalean.Stat
