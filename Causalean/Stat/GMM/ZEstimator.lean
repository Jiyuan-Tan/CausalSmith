/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.GMM.Setup
public import Causalean.Stat.MEstimation.ZEstimator

/-! # GMM as a Z-estimation problem

This module constructs the regularity package for the combined GMM score. The
population derivative is derived from the GMM moment derivative, so downstream
GMM theorems do not need a separate equality identifying two inverse Jacobians.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ContinuousLinearMap Filter Topology
open scoped RealInnerProductSpace

variable {E F X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace X]

namespace ZEstimatorRegularity

/-- Given [a GMM problem](hyp:prob), [measurability of its moment at every nearby
parameter](hyp:hMeas), and [local integrability of those moments within a positive
radius](hyp:δ,hδ,hInt), the
[combined GMM score has Z-estimator regularity with Jacobian `GᵀWG` and the
problem's bread inverse](goal).

The derivative identification is derived from `prob.jac_spec` by commuting the
fixed continuous linear map `GᵀW` with the Bochner integral. -/
noncomputable def ofGMMProblem
    {P : Measure X} (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E,
      ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P) :
    ZEstimatorRegularity prob.score prob.θ₀ P := by
  let A : F →L[ℝ] E := adjoint prob.G ∘L prob.W
  have hScoreMeas (θ : E) : Measurable (prob.score θ) := by
    exact A.continuous.measurable.comp (hMeas θ)
  have hScoreVar : Integrable (fun x => ‖prob.score prob.θ₀ x‖ ^ 2) P := by
    have hbound : ∀ x, ‖prob.score prob.θ₀ x‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by
      intro x
      have hop := A.le_opNorm (prob.g prob.θ₀ x)
      have hleft : 0 ≤ ‖A (prob.g prob.θ₀ x)‖ := norm_nonneg _
      have hright : 0 ≤ ‖A‖ * ‖prob.g prob.θ₀ x‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      change ‖A (prob.g prob.θ₀ x)‖ ^ 2 ≤ _
      nlinarith
    refine (prob.finite_var.const_mul (‖A‖ ^ 2)).mono' ?_ ?_
    · exact (hScoreMeas prob.θ₀).norm.pow_const 2 |>.aestronglyMeasurable
    · filter_upwards with x
      have hx : 0 ≤ ‖prob.score prob.θ₀ x‖ ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hbound x
  have hScoreInt (θ : E) (hθ : ‖θ - prob.θ₀‖ < δ) :
      Integrable (prob.score θ) P := by
    exact A.integrable_comp (hInt θ hθ)
  have hIntegralEq : ∀ᶠ θ in 𝓝 prob.θ₀,
      (∫ x, prob.score θ x ∂P) =
        (A ∘ fun η => ∫ x, prob.g η x ∂P) θ := by
    filter_upwards [Metric.ball_mem_nhds prob.θ₀ hδ] with θ hθ
    rw [Metric.mem_ball, dist_eq_norm] at hθ
    exact A.integral_comp_comm (hInt θ hθ)
  have hDeriv : HasFDerivAt
      (A ∘ fun θ => ∫ x, prob.g θ x ∂P)
      (A ∘L prob.G) prob.θ₀ := by
    exact A.hasFDerivAt.comp prob.θ₀ prob.jac_spec
  exact
    { identification := by
        rw [hIntegralEq.self_of_nhds]
        simp [prob.identification]
      J₀ := gmmBread prob.G prob.W
      J₀_inv := prob.breadInv
      J₀_inverse := prob.breadInv_right
      J₀_spec := by
        change HasFDerivAt (fun θ => ∫ x, prob.score θ x ∂P)
          (A ∘L prob.G) prob.θ₀
        exact hDeriv.congr_of_eventuallyEq hIntegralEq
      finite_var := hScoreVar
      psi_meas := hScoreMeas
      psi_int_neighborhood := ⟨δ, hδ, hScoreInt⟩ }

end ZEstimatorRegularity

/-- Given [a GMM problem](hyp:prob), [a positive neighborhood radius](hyp:δ,hδ), and moments
[integrable near the target](hyp:hInt),
the [population moment increment equals its Jacobian-linear term up to a remainder that is
little-o of the parameter distance](goal).

This is the population differentiability condition in Newey--McFadden (1994), Theorem 7.2,
restated in the scalar-norm form used by stochastic-absorption arguments. -/
theorem GMMProblem.populationMomentDiff_isLittleO
    {P : Measure X} (prob : GMMProblem (E := E) (F := F) P)
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P) :
    (fun θ => ∫ z, (prob.g θ z - prob.g prob.θ₀ z) ∂P
        - prob.G (θ - prob.θ₀))
      =o[𝓝 prob.θ₀] fun θ => ‖θ - prob.θ₀‖ := by
  have hg₀ : Integrable (prob.g prob.θ₀) P := hInt prob.θ₀ (by simpa using hδ)
  have hbase :
      (fun θ => (∫ z, prob.g θ z ∂P) - (∫ z, prob.g prob.θ₀ z ∂P)
          - prob.G (θ - prob.θ₀))
        =o[𝓝 prob.θ₀] fun θ => θ - prob.θ₀ :=
    prob.jac_spec.isLittleO
  have hbaseNorm :
      (fun θ => (∫ z, prob.g θ z ∂P) - (∫ z, prob.g prob.θ₀ z ∂P)
          - prob.G (θ - prob.θ₀))
        =o[𝓝 prob.θ₀] fun θ => ‖θ - prob.θ₀‖ :=
    (Asymptotics.isLittleO_norm_right).mpr hbase
  refine hbaseNorm.congr' ?_ EventuallyEq.rfl
  filter_upwards [Metric.ball_mem_nhds prob.θ₀ hδ] with θ hθ
  rw [Metric.mem_ball, dist_eq_norm] at hθ
  rw [MeasureTheory.integral_sub (hInt θ hθ) hg₀]

end Causalean.Stat
