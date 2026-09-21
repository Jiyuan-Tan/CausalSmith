/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Z- / M-estimator asymptotic linearity (parametric inference theorem layer)

Asymptotic linearity and normality for an estimator `θ̂_n` approximately solving an
estimating equation, with `(1/n) Σ_{i<n} ψ(Z_i; θ̂_n) = o_P(n⁻¹/²)`.  This is the
generic Z-estimation core used by OLS, MLE, IV-2SLS, and GMM through different
choices of `ψ`. The normal-limit theorem applies the library's concrete
multivariate iid CLT to the linear representation.

Reference: Newey & McFadden (1994), Theorem 7.2; Andrews (1994).
Spec: `def:par-smoothness`, `thm:par-z-clt` in
`doc/basic_concepts/Semi-parametric Inference/parametric_inference.tex`.

The proof first derives the root-sample-size rate by stochastic absorption, then uses
`localStochasticExpansion` from `Causalean/Stat/MEstimation/EmpiricalExpansion.lean` and
a structural rearrangement with
Slutsky-style algebra.  All three `IsAsymLinearVec` fields are
discharged: `mean_zero` (push `−J₀⁻¹` through the Bochner integral using
`identification`), `finite_var` (operator-norm bound via `J₀_inv` +
`finite_var`), and `remainder` (combine `localStochasticExpansion` with
`hMoment`, then bound the rescaled remainder by applying `J₀_inv` and using
the finite-dimensional left-inverse derived from `J₀_inverse`).  The
remaining empirical-process content is exposed as hypotheses upstream,
especially `StochEquicontAt`, rather than proved from a Donsker or chaining
theorem in this file.

The regularity structure lives in
`Causalean/Stat/MEstimation/ZEstimator.lean`; keeping it separate from this
theorem layer avoids an import cycle because the proof
imports `EmpiricalExpansion.lean`, which itself imports `ZEstimator.lean` for
the structure.
-/

module
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.CLT.AsymptoticLinearityVec
public import Causalean.Stat.CLT.GaussianLimit
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.MEstimation.EmpiricalExpansion
public import Causalean.Stat.MEstimation.InfluenceFunction
public import Causalean.Stat.MEstimation.ZEstimator
public import Causalean.Stat.MEstimation.ZEstimatorRate
public import Causalean.Stat.Sample
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-! # Z-estimator Asymptotic Linearity

This file establishes asymptotic linearity and normality for parametric estimators defined by
empirical estimating equations. It turns a local stochastic expansion into an
influence-function representation and then applies the concrete multivariate central limit
theorem to obtain the centered Gaussian limit with the influence-function covariance.

Use this high-level route when stochastic equicontinuity is supplied directly,
as in Newey--McFadden (1994), Theorem 7.2, or Andrews (1994); it is the route
intended for nonsmooth scores. For observationwise smooth scores use
`SmoothZEstimator`, and for scores with a square-integrable Lipschitz envelope
use `LipschitzZEstimator` (van der Vaart 1998, Theorem 5.21).
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For [a Z-estimation score, target, population law, and regularity
package](hyp:ψ,θ₀,P,reg), the [negative inverse-Jacobian score satisfies the
common influence-function regularity interface](goal). -/
theorem ZEstimatorRegularity.influenceFunction
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P) :
    InfluenceFunction P (fun z => -(reg.J₀_inv (ψ θ₀ z))) := by
  have hmeas : Measurable (fun z => -(reg.J₀_inv (ψ θ₀ z))) :=
    reg.J₀_inv.continuous.measurable.comp (reg.psi_meas θ₀) |>.neg
  have hbound : ∀ z, ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2 ≤
      ‖reg.J₀_inv‖ ^ 2 * ‖ψ θ₀ z‖ ^ 2 := by
    intro z
    have hnorm : ‖reg.J₀_inv (ψ θ₀ z)‖ ≤ ‖reg.J₀_inv‖ * ‖ψ θ₀ z‖ :=
      reg.J₀_inv.le_opNorm (ψ θ₀ z)
    have hleft_nonneg : 0 ≤ ‖reg.J₀_inv (ψ θ₀ z)‖ := norm_nonneg _
    have hop_nonneg : 0 ≤ ‖reg.J₀_inv‖ := norm_nonneg _
    have hψ_nonneg : 0 ≤ ‖ψ θ₀ z‖ := norm_nonneg _
    calc
      ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2 = ‖reg.J₀_inv (ψ θ₀ z)‖ ^ 2 := by
        rw [norm_neg]
      _ ≤ ‖reg.J₀_inv‖ ^ 2 * ‖ψ θ₀ z‖ ^ 2 := by
        nlinarith
  have hvar : Integrable (fun z => ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2) P := by
    refine (reg.finite_var.const_mul (‖reg.J₀_inv‖ ^ 2)).mono' ?_ ?_
    · exact hmeas.norm.pow_const 2 |>.aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      have hz_nonneg : 0 ≤ ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hz_nonneg] using hbound z
  have hmean : ∫ z, -(reg.J₀_inv (ψ θ₀ z)) ∂P = 0 := by
    rcases reg.psi_int_neighborhood with ⟨δ, hδ_pos, hδ_int⟩
    have hψ₀ : Integrable (ψ θ₀) P := hδ_int θ₀ (by simpa using hδ_pos)
    calc
      ∫ z, -(reg.J₀_inv (ψ θ₀ z)) ∂P
          = -(∫ z, reg.J₀_inv (ψ θ₀ z) ∂P) := by
            rw [MeasureTheory.integral_neg]
      _ = -(reg.J₀_inv (∫ z, ψ θ₀ z ∂P)) := by
            rw [ContinuousLinearMap.integral_comp_comm reg.J₀_inv hψ₀]
      _ = 0 := by simp [reg.identification]
  exact ⟨hmeas, hmean, hvar⟩

omit [FiniteDimensional ℝ E] in
/-- For [a Z-estimation score, target, population law, and regularity
package](hyp:ψ,θ₀,P,reg), [the resulting influence function is measurable](goal).

This compatibility projection is retained for callers that have not yet
switched to `ZEstimatorRegularity.influenceFunction`. -/
@[fun_prop]
theorem zEstimatorInfluence_measurable
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P) :
    Measurable (fun z => -(reg.J₀_inv (ψ θ₀ z))) :=
  reg.J₀_inv.continuous.measurable.comp (reg.psi_meas θ₀) |>.neg

omit [FiniteDimensional ℝ E] in
/-- For [a Z-estimation score, target, population law, and regularity
package](hyp:ψ,θ₀,P,reg), [the squared norm of the resulting influence function is
integrable](goal).

This compatibility projection is retained for callers that have not yet
switched to `ZEstimatorRegularity.influenceFunction`. -/
@[fun_prop]
theorem integrable_sq_zEstimatorInfluence
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P) :
    Integrable (fun z => ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2) P := by
  have hbound : ∀ z, ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2 ≤
      ‖reg.J₀_inv‖ ^ 2 * ‖ψ θ₀ z‖ ^ 2 := by
    intro z
    have hnorm : ‖reg.J₀_inv (ψ θ₀ z)‖ ≤ ‖reg.J₀_inv‖ * ‖ψ θ₀ z‖ :=
      reg.J₀_inv.le_opNorm (ψ θ₀ z)
    have hleft_nonneg : 0 ≤ ‖reg.J₀_inv (ψ θ₀ z)‖ := norm_nonneg _
    have hop_nonneg : 0 ≤ ‖reg.J₀_inv‖ := norm_nonneg _
    have hψ_nonneg : 0 ≤ ‖ψ θ₀ z‖ := norm_nonneg _
    calc
      ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2 = ‖reg.J₀_inv (ψ θ₀ z)‖ ^ 2 := by
        rw [norm_neg]
      _ ≤ ‖reg.J₀_inv‖ ^ 2 * ‖ψ θ₀ z‖ ^ 2 := by
        nlinarith
  refine (reg.finite_var.const_mul (‖reg.J₀_inv‖ ^ 2)).mono' ?_ ?_
  · exact (zEstimatorInfluence_measurable ψ θ₀ P reg).norm.pow_const 2
      |>.aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    have hz_nonneg : 0 ≤ ‖-(reg.J₀_inv (ψ θ₀ z))‖ ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hz_nonneg] using hbound z

/-- **Z-estimator asymptotic linearity.** For [a score, target, population law, and regularity
package](hyp:ψ,θ₀,P,reg), [an iid sample and estimator sequence](hyp:S,θn), if [the estimator is
consistent](hyp:hConsistent), [the centered score process is stochastically equicontinuous along
the estimator](hyp:hStochEquicont), and [the normalized empirical score at the estimator is
negligible in probability](hyp:hMoment), then [the estimator has the influence-function
representation obtained by applying the negative inverse Jacobian to the target score](goal).

The estimating-equation condition is the approximate-root requirement
`Pₙ ψ(θ̂ₙ) = o_P(n⁻¹/²)`.  The proof first derives the root-sample-size
rate by stochastic absorption and then applies the local stochastic expansion.
This is the high-level stochastic-equicontinuity route of Newey--McFadden
(1994), Theorem 7.2, and Andrews (1994); it also covers nonsmooth scores for
which an exact empirical root need not exist. -/
theorem zEstimator_asymLinear
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec
      (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z)))
      S
      (fun n => Finset.range n) := by
  refine ⟨(reg.influenceFunction ψ θ₀ P).mean_zero,
    (reg.influenceFunction ψ θ₀ P).finite_var, ?_⟩
  · have hRootRate := zEstimator_rootRate ψ θ₀ P reg S θn
      hConsistent hStochEquicont hMoment
    have hRate := inverseRootRate_of_rootRate θn θ₀ hRootRate
    have hA :
        IsLittleOp
          (fun n ω =>
            ‖(Real.sqrt (n : ℝ))⁻¹ •
                ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
              - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)‖)
          (fun _ => (1 : ℝ)) μ :=
      localStochasticExpansion ψ θ₀ P reg S θn hConsistent hStochEquicont hRate
    let A : ℕ → Ω → E := fun n ω =>
      (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
        - Real.sqrt (n : ℝ) • reg.J₀ (θn n ω - θ₀)
    let R : ℕ → Ω → E := fun n ω =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)
    let B : ℕ → Ω → E := fun n ω =>
      Real.sqrt (n : ℝ) • (θn n ω - θ₀)
        - (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, -reg.J₀_inv (ψ θ₀ (S.Z i ω))
    have hA' : IsLittleOp (fun n ω => ‖A n ω‖) (fun _ => (1 : ℝ)) μ := by
      simpa [A] using hA
    have hJ_left : ∀ x : E, reg.J₀_inv (reg.J₀ x) = x := by
      have hJ_surj : Function.Surjective reg.J₀ := fun y =>
        ⟨reg.J₀_inv y, by
          have := congrArg (fun T : E →L[ℝ] E => T y) reg.J₀_inverse
          simpa using this⟩
      have hJ_inj : Function.Injective reg.J₀ := by
        exact (LinearMap.injective_iff_surjective (f := (reg.J₀ : E →ₗ[ℝ] E))).mpr hJ_surj
      intro x
      apply hJ_inj
      have := congrArg (fun T : E →L[ℝ] E => T (reg.J₀ x)) reg.J₀_inverse
      simpa using this
    let C : ℝ := ‖reg.J₀_inv‖ + 1
    have hC : 0 < C := by dsimp [C]; linarith [norm_nonneg reg.J₀_inv]
    have mapLittle : ∀ (V : ℕ → Ω → E),
        IsLittleOp (fun n ω => ‖V n ω‖) (fun _ => (1 : ℝ)) μ →
        IsLittleOp (fun n ω => ‖reg.J₀_inv (V n ω)‖) (fun _ => (1 : ℝ)) μ := by
      intro V hV
      exact IsLittleOp.of_abs_le_const_mul_one hC hV (fun n ω => by
        simp only [abs_of_nonneg (norm_nonneg _)]
        exact (reg.J₀_inv.le_opNorm (V n ω)).trans
          (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hJInvA := mapLittle A hA'
    have hJInvR := mapLittle R (by simpa [R] using hMoment)
    have hsum := hJInvA.add_one hJInvR
    have hB : IsLittleOp (fun n ω => ‖B n ω‖) (fun _ => (1 : ℝ)) μ := by
      refine IsLittleOp.of_abs_le_const_mul_one (C := 1) zero_lt_one hsum ?_
      intro n ω
      simp only [abs_of_nonneg (norm_nonneg _), one_mul]
      have hBident : B n ω = -reg.J₀_inv (A n ω) + reg.J₀_inv (R n ω) := by
        simp [A, B, R, Finset.sum_sub_distrib, map_sub, map_smul, map_sum,
          hJ_left]
        module
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [hBident]
      simpa only [norm_neg] using
        norm_add_le (-reg.J₀_inv (A n ω)) (reg.J₀_inv (R n ω))
    simpa [B, Finset.card_range] using hB

/-- **Z-estimator asymptotic normality.** For [a score, target, population law, and regularity
package](hyp:ψ,θ₀,P,reg), if [an estimator based on an iid sample](hyp:S,θn) [is
consistent](hyp:hConsistent), its score [is stochastically equicontinuous along the
estimator](hyp:hStochEquicont), [its normalized estimating-equation residual is negligible in
probability](hyp:hMoment), and [its rescaled version is measurable](hyp:hθn_meas), then [its
rescaled laws converge to the concrete centered Gaussian generated by the inverse-Jacobian
influence function](goal).

The root-sample-size rate is derived internally.  The theorem combines the
Newey--McFadden (1994), Theorem 7.2, representation in
`zEstimator_asymLinear` with the library's multivariate iid CLT. -/
theorem zEstimator_tendsto_normal
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθn_meas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit
          (reg.influenceFunction ψ θ₀ P).measurable
          (reg.influenceFunction ψ θ₀ P).finite_var, inferInstance⟩) := by
  have hAL := zEstimator_asymLinear ψ θ₀ P reg S θn hConsistent
    hStochEquicont hMoment
  exact hAL.tendsto_normal_vec_clt
    (reg.influenceFunction ψ θ₀ P).measurable
    (gaussianLimit
      (reg.influenceFunction ψ θ₀ P).measurable
      (reg.influenceFunction ψ θ₀ P).finite_var)
    (gaussianLimit_charFun
      (reg.influenceFunction ψ θ₀ P).measurable
      (reg.influenceFunction ψ θ₀ P).finite_var)
    hθn_meas

end Causalean.Stat
