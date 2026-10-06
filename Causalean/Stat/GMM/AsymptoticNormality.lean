/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# GMM asymptotic linearity via the combined-score Z-estimator

The asymptotic-linear representation of the GMM estimator is obtained from the
Z-estimator approximately solving the combined estimating equation
`GᵀW ḡ_n(θ) = o_P(n⁻¹/²)` (Newey & McFadden 1994, Theorem 7.2): the
approximate empirical first-order condition of the GMM
criterion `ḡ_n(θ)ᵀ W ḡ_n(θ)`, after fixing the Jacobian weight at its population
value `G`.  Thus GMM asymptotic linearity is a direct corollary of the parametric
Z-estimator linearization theorem `zEstimator_asymLinear`
(`Causalean/Stat/MEstimation/ZEstimatorCLT.lean`)
applied to the combined score `ψ(θ,x) = GᵀW g(θ,x)` (`GMMProblem.score`).

`oracleGMM_asymLinear` instantiates that linearization, derives the
root-sample-size rate internally, and identifies the influence function as
`gmmIF = −(GᵀWG)⁻¹GᵀW g(θ₀,·)`. The separate corollary
`oracleGMM_tendsto_normal` applies the concrete multivariate iid CLT and proves
convergence to the centered Gaussian whose covariance is the usual GMM
sandwich operator `GMMProblem.asympVar`.

`ZEstimatorRegularity.ofGMMProblem` derives the combined-score derivative
`D[θ ↦ ∫ GᵀW g(θ) dP] = GᵀWG` from `prob.jac_spec`, so the GMM theorems use
`prob.breadInv` directly and require no separate inverse-Jacobian equality.

Use this high-level equicontinuity route for nonsmooth GMM moments
(Newey--McFadden 1994, Theorem 7.2; Andrews 1994). For observationwise smooth
moments and a feasible estimated weight, use the `SmoothFeasibleGeneral`
family, corresponding to Newey--McFadden (1994), Theorem 3.2.
-/

module
public import Causalean.Stat.GMM.ZEstimator
public import Causalean.Stat.MEstimation.ExtremumConsistency
public import Causalean.Stat.MEstimation.ZEstimatorCLT

/-! # GMM Asymptotic Linearity and Normality

This file derives asymptotic linearity for generalized method of moments
estimators from the central limit theorem for parametric estimating equations.
The theorem `oracleGMM_asymLinear` applies Z-estimator linearization to the
combined GMM score and identifies the influence function
`-(G^T W G)^{-1} G^T W g(θ₀, z)`.  The corollary `oracleGMM_tendsto_normal`
proves convergence to the concrete centered Gaussian limit and identifies its
covariance with the GMM sandwich operator. The estimator here is defined through
the first-order condition using the population Jacobian `G` and population
weight `W`; feasible GMM is a separate layer. -/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped RealInnerProductSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

section

/-- For [a bundled GMM problem](hyp:prob), [its canonical influence function
satisfies the common influence-function regularity interface](goal). -/
theorem GMMProblem.influenceFunction
    [IsFiniteMeasure P] (prob : GMMProblem (E := E) (F := F) P) :
    InfluenceFunction P prob.influence := by
  have hmeas : Measurable prob.influence := by
    unfold GMMProblem.influence gmmIF
    exact (prob.breadInv.continuous.measurable.comp
      ((adjoint prob.G).continuous.measurable.comp
        (prob.W.continuous.measurable.comp prob.g_meas))).neg
  let L : F →L[ℝ] E := prob.breadInv ∘L adjoint prob.G ∘L prob.W
  have hbound : ∀ x, ‖prob.influence x‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by
    intro x
    have hnorm : ‖L (prob.g prob.θ₀ x)‖ ≤ ‖L‖ * ‖prob.g prob.θ₀ x‖ :=
      L.le_opNorm (prob.g prob.θ₀ x)
    have hleft_nonneg : 0 ≤ ‖L (prob.g prob.θ₀ x)‖ := norm_nonneg _
    have hop_nonneg : 0 ≤ ‖L‖ := norm_nonneg _
    have hg_nonneg : 0 ≤ ‖prob.g prob.θ₀ x‖ := norm_nonneg _
    calc
      ‖prob.influence x‖ ^ 2 = ‖L (prob.g prob.θ₀ x)‖ ^ 2 := by
        simp only [GMMProblem.influence, gmmIF, L, comp_apply, norm_neg]
      _ ≤ ‖L‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by
        nlinarith
  have hvar : Integrable (fun x => ‖prob.influence x‖ ^ 2) P := by
    refine (prob.finite_var.const_mul (‖L‖ ^ 2)).mono' ?_ ?_
    · exact hmeas.norm.pow_const 2 |>.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      have hx_nonneg : 0 ≤ ‖prob.influence x‖ ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg] using hbound x
  have hgint : Integrable (prob.g prob.θ₀) P :=
    ((memLp_two_iff_integrable_sq_norm prob.g_meas.aestronglyMeasurable).2
      prob.finite_var).integrable (by norm_num)
  have hmean : ∫ x, prob.influence x ∂P = 0 := by
    unfold GMMProblem.influence gmmIF
    have hWint := prob.W.integrable_comp hgint
    have hGWint := (adjoint prob.G).integrable_comp hWint
    calc
      ∫ x, -(prob.breadInv ((adjoint prob.G) (prob.W (prob.g prob.θ₀ x)))) ∂P =
          -(∫ x, prob.breadInv
            ((adjoint prob.G) (prob.W (prob.g prob.θ₀ x))) ∂P) := by
        rw [integral_neg]
      _ = -(prob.breadInv
          (∫ x, (adjoint prob.G) (prob.W (prob.g prob.θ₀ x)) ∂P)) := by
        rw [ContinuousLinearMap.integral_comp_comm prob.breadInv hGWint]
      _ = -(prob.breadInv ((adjoint prob.G)
          (∫ x, prob.W (prob.g prob.θ₀ x) ∂P))) := by
        rw [ContinuousLinearMap.integral_comp_comm (adjoint prob.G) hWint]
      _ = -(prob.breadInv ((adjoint prob.G)
          (prob.W (∫ x, prob.g prob.θ₀ x ∂P)))) := by
        rw [ContinuousLinearMap.integral_comp_comm prob.W hgint]
      _ = 0 := by simp [prob.identification]
  exact ⟨hmeas, hmean, hvar⟩

/-- For [a bundled GMM problem](hyp:prob), [its influence function is measurable](goal).

This compatibility projection is retained for callers that have not yet
switched to `GMMProblem.influenceFunction`. -/
@[fun_prop]
theorem GMMProblem.influence_measurable
    (prob : GMMProblem (E := E) (F := F) P) :
    Measurable prob.influence := by
  unfold GMMProblem.influence gmmIF
  exact (prob.breadInv.continuous.measurable.comp
    ((adjoint prob.G).continuous.measurable.comp
      (prob.W.continuous.measurable.comp prob.g_meas))).neg

/-- For [a bundled GMM problem](hyp:prob), [the squared norm of its influence function is
integrable under the population law](goal).

This compatibility projection is retained for callers that have not yet
switched to `GMMProblem.influenceFunction`. -/
@[fun_prop]
theorem GMMProblem.influence_integrable_sq
    (prob : GMMProblem (E := E) (F := F) P) :
    Integrable (fun x => ‖prob.influence x‖ ^ 2) P := by
  let L : F →L[ℝ] E := prob.breadInv ∘L adjoint prob.G ∘L prob.W
  have hbound : ∀ x, ‖prob.influence x‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by
    intro x
    have hnorm : ‖L (prob.g prob.θ₀ x)‖ ≤ ‖L‖ * ‖prob.g prob.θ₀ x‖ :=
      L.le_opNorm (prob.g prob.θ₀ x)
    have hleft_nonneg : 0 ≤ ‖L (prob.g prob.θ₀ x)‖ := norm_nonneg _
    have hop_nonneg : 0 ≤ ‖L‖ := norm_nonneg _
    have hg_nonneg : 0 ≤ ‖prob.g prob.θ₀ x‖ := norm_nonneg _
    calc
      ‖prob.influence x‖ ^ 2 = ‖L (prob.g prob.θ₀ x)‖ ^ 2 := by
        simp only [GMMProblem.influence, gmmIF, L, comp_apply, norm_neg]
      _ ≤ ‖L‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by
        nlinarith
  refine (prob.finite_var.const_mul (‖L‖ ^ 2)).mono' ?_ ?_
  · exact prob.influence_measurable.norm.pow_const 2 |>.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hx_nonneg : 0 ≤ ‖prob.influence x‖ ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg] using hbound x

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- For [a bundled GMM problem](hyp:prob) and [two parameter-space directions](hyp:s,t), the
[second moment of its influence function equals the bilinear form induced by the GMM sandwich
covariance operator](goal). -/
theorem GMMProblem.influence_secondMoment_eq_asympVar
    (prob : GMMProblem (E := E) (F := F) P) (s t : E) :
    ∫ x, ⟪s, prob.influence x⟫ * ⟪t, prob.influence x⟫ ∂P
      = ⟪prob.asympVar s, t⟫ := by
  have hBreadSa : adjoint (gmmBread prob.G prob.W) = gmmBread prob.G prob.W := by
    unfold gmmBread
    simp only [adjoint_comp, adjoint_adjoint, prob.hWsa, comp_assoc]
  have hA : adjoint prob.breadInv = prob.breadInv :=
    adjoint_inv_self hBreadSa prob.breadInv_right
  have hinfluence : ∀ (u : E) (x : X),
      ⟪u, prob.influence x⟫ =
        -⟪prob.W (prob.G (prob.breadInv u)), prob.g prob.θ₀ x⟫ := by
    intro u x
    unfold GMMProblem.influence gmmIF
    rw [inner_neg_right, ← hA, adjoint_inner_right, adjoint_inner_right,
      ← prob.hWsa, adjoint_inner_right]
    simp only [hA, prob.hWsa]
  calc
    ∫ x, ⟪s, prob.influence x⟫ * ⟪t, prob.influence x⟫ ∂P =
        ∫ x, ⟪prob.W (prob.G (prob.breadInv s)), prob.g prob.θ₀ x⟫ *
          ⟪prob.W (prob.G (prob.breadInv t)), prob.g prob.θ₀ x⟫ ∂P := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hinfluence s x, hinfluence t x]
            ring
    _ = ⟪prob.Cov (prob.W (prob.G (prob.breadInv s))),
          prob.W (prob.G (prob.breadInv t))⟫ := by
            rw [prob.hCov]
    _ = ⟪prob.asympVar s, t⟫ := by
      unfold GMMProblem.asympVar gmmSandwich
      simp only [comp_apply]
      rw [show ⟪prob.breadInv
          ((adjoint prob.G)
            (prob.W (prob.Cov (prob.W (prob.G (prob.breadInv s)))))), t⟫ =
          ⟪t, prob.breadInv
            ((adjoint prob.G)
              (prob.W (prob.Cov (prob.W (prob.G (prob.breadInv s))))))⟫ by
            exact real_inner_comm _ _]
      rw [← hA, adjoint_inner_right, adjoint_inner_right,
        ← prob.hWsa, adjoint_inner_right, real_inner_comm]
      simp only [hA, prob.hWsa]

/-- For [a bundled GMM problem](hyp:prob) and [two parameter-space directions](hyp:s,t), [the
concrete Gaussian limit built from its influence function has covariance bilinear form equal to
the GMM sandwich operator](goal). -/
theorem GMMProblem.gaussianLimit_covarianceBilin
    (prob : GMMProblem (E := E) (F := F) P) (s t : E) :
    covarianceBilin
        (gaussianLimit prob.influence_measurable prob.influence_integrable_sq) s t
      = ⟪prob.asympVar s, t⟫ := by
  rw [Causalean.Stat.gaussianLimit_covarianceBilin]
  exact prob.influence_secondMoment_eq_asympVar s t

end

section

/-- For [a GMM problem](hyp:prob) with [measurable moments](hyp:hMeas) that are [integrable
on a positive-radius neighborhood](hyp:δ,hδ,hInt), an [iid sample and estimator](hyp:S,θn),
[consistency](hyp:hConsistent), [score-process stochastic equicontinuity](hyp:hStochEquicont),
and [an approximate oracle first-order condition](hyp:hMoment), [the estimator has the usual
GMM influence-function expansion](goal).

The influence function is

    influence(z) = −(GᵀWG)⁻¹ GᵀW g(θ₀, z).

This is the high-level equicontinuity route of Newey--McFadden (1994), Theorem 7.2,
and Andrews (1994), suitable for nonsmooth moments. For pointwise smooth moments use
`feasibleGMM_asymLinear_of_smoothMoment`; the Lipschitz-score route is
`zEstimator_asymLinear_of_lipschitz` (van der Vaart 1998, Theorem 5.21).
-/
theorem oracleGMM_asymLinear
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.score prob.θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) := by
  let reg := ZEstimatorRegularity.ofGMMProblem prob hMeas δ hδ hInt
  have h := zEstimator_asymLinear prob.score prob.θ₀ P reg S θn
    hConsistent hStochEquicont hMoment
  -- The Chernozhukov-form influence function of the combined score IS gmmIF.
  have hIF : prob.influence
      = fun z => -(reg.J₀_inv (prob.score prob.θ₀ z)) := by
    funext z
    change -(prob.breadInv (adjoint prob.G (prob.W (prob.g prob.θ₀ z)))) = _
    rfl
  rw [hIF]
  exact h

end

/-- For [a GMM problem](hyp:prob) with [measurable, locally integrable moments on a positive
neighborhood](hyp:hMeas,δ,hδ,hInt), an [iid sample and estimator](hyp:S,θn),
[consistency](hyp:hConsistent), [score stochastic equicontinuity](hyp:hStochEquicont),
[an approximate oracle first-order condition](hyp:hMoment), and [rescaled-estimator
measurability](hyp:hθn_meas), [the rescaled laws converge to the Gaussian with GMM sandwich
covariance](goal).

The Gaussian target is built from `prob.influence`; its covariance identification is
`GMMProblem.gaussianLimit_covarianceBilin`.  This derived-rate, approximate-root
normal limit follows Newey--McFadden (1994), Theorem 7.2. -/
theorem oracleGMM_tendsto_normal
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.score prob.θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθn_meas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit prob.influence_measurable prob.influence_integrable_sq,
        inferInstance⟩) := by
  let reg := ZEstimatorRegularity.ofGMMProblem prob hMeas δ hδ hInt
  have hIF : prob.influence =
      fun z => -(reg.J₀_inv (prob.score prob.θ₀ z)) := by
    funext z
    change -(prob.breadInv (adjoint prob.G (prob.W (prob.g prob.θ₀ z)))) = _
    rfl
  have hG : gaussianLimit prob.influence_measurable prob.influence_integrable_sq =
      gaussianLimit
        (reg.influenceFunction prob.score prob.θ₀ P).measurable
        (reg.influenceFunction prob.score prob.θ₀ P).finite_var := by
    have hcongr : ∀ {φ ψ : X → E}
        (hφ : Measurable φ) (hφvar : Integrable (fun x => ‖φ x‖ ^ 2) P)
        (hψ : Measurable ψ) (hψvar : Integrable (fun x => ‖ψ x‖ ^ 2) P),
        φ = ψ → gaussianLimit hφ hφvar = gaussianLimit hψ hψvar := by
      intro φ ψ hφ hφvar hψ hψvar h
      subst ψ
      rfl
    exact hcongr prob.influence_measurable prob.influence_integrable_sq
      (reg.influenceFunction prob.score prob.θ₀ P).measurable
      (reg.influenceFunction prob.score prob.θ₀ P).finite_var hIF
  have hQ :
      (⟨gaussianLimit prob.influence_measurable prob.influence_integrable_sq,
        inferInstance⟩ : ProbabilityMeasure E) =
      ⟨gaussianLimit
          (reg.influenceFunction prob.score prob.θ₀ P).measurable
          (reg.influenceFunction prob.score prob.θ₀ P).finite_var,
        inferInstance⟩ := by
    exact Subtype.ext hG
  rw [hQ]
  exact zEstimator_tendsto_normal prob.score prob.θ₀ P reg S θn hConsistent
    hStochEquicont hMoment hθn_meas

section

/-- **GMM asymptotic linearity from extremum primitives.**  The GMM analogue of
`zEstimator_asymLinear_of_extremum`: `oracleGMM_asymLinear` with the consistency
hypothesis discharged from a Glivenko–Cantelli GMM criterion `m` with a
well-separated population maximum at `θ₀` of which `θn` is a sample maximiser.
The classical instance is `m θ = −ḡ_n(θ)ᵀ W ḡ_n(θ)` (the GMM objective), whose
score is `prob.score`. -/
theorem gmm_asymLinear_of_extremum
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : WeakGlivenkoCantelli S m)
    (slack : ℕ → Ω → ℝ)
    (hSlack : Tendsto_inProb slack (fun _ => 0) μ)
    (hApprox : ∀ n ω,
      S.sampleMean (m prob.θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω + slack n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ prob.θ₀ →
        (∫ x, m θ x ∂P) + η ≤ ∫ x, m prob.θ₀ x ∂P)
    (hStochEquicont : StochEquicontAt prob.score prob.θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  oracleGMM_asymLinear prob hMeas δ hδ hInt S θn
    (consistent_lt_norm_of_le_dist θn prob.θ₀
      (mEstimator_consistent_of_glivenkoCantelli S m prob.θ₀ θn hGC
        slack hSlack hApprox hSep))
    hStochEquicont hMoment

/-- **GMM asymptotic linearity with the equicontinuity hypothesis discharged.** For
[a GMM problem with measurable moments](hyp:prob,hMeas),
[local moment integrability on a positive-radius neighborhood](hyp:δ,hδ,hInt),
[an iid sample and estimator](hyp:S,θn), [estimator consistency](hyp:hConsistent),
[local score-family asymptotic equicontinuity](hyp:hAEC), and
[an approximate oracle first-order condition](hyp:hMoment),
[the estimator has the usual GMM influence-function expansion](goal).

This is `oracleGMM_asymLinear` with the estimator-specific modulus
`hStochEquicont` reconstructed by `stochEquicontAt_of_asymptoticEquicont` from
`hAEC` and consistency. -/
theorem gmm_asymLinear_of_asymptoticEquicont
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hAEC : AsymptoticEquicont prob.score prob.θ₀ P μ S)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  oracleGMM_asymLinear prob hMeas δ hδ hInt S θn hConsistent
    (stochEquicontAt_of_asymptoticEquicont prob.score prob.θ₀ S θn hAEC hConsistent)
    hMoment

/-- **GMM asymptotic linearity from primitive conditions: both opaque hypotheses
discharged.** For [a GMM problem with measurable moments](hyp:prob,hMeas),
[local moment integrability on a positive-radius neighborhood](hyp:δ,hδ,hInt),
[an iid sample and estimator](hyp:S,θn), [a Glivenko–Cantelli criterion family](hyp:m,hGC),
[approximate maximization with vanishing slack](hyp:slack,hSlack,hApprox),
[a well-separated population maximum](hyp:hSep),
[local score-family asymptotic equicontinuity](hyp:hAEC), and
[an approximate oracle first-order condition](hyp:hMoment),
[the estimator has the usual GMM influence-function expansion](goal).

Neither `hConsistent` nor `hStochEquicont` is assumed. Consistency is derived
from the extremum conditions and used both in the linearization and in the
`StochEquicontAt` reduction. -/
theorem gmm_asymLinear_of_extremum_asymptoticEquicont
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : WeakGlivenkoCantelli S m)
    (slack : ℕ → Ω → ℝ)
    (hSlack : Tendsto_inProb slack (fun _ => 0) μ)
    (hApprox : ∀ n ω,
      S.sampleMean (m prob.θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω + slack n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ prob.θ₀ →
        (∫ x, m θ x ∂P) + η ≤ ∫ x, m prob.θ₀ x ∂P)
    (hAEC : AsymptoticEquicont prob.score prob.θ₀ P μ S)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  have hcons := consistent_lt_norm_of_le_dist θn prob.θ₀
    (mEstimator_consistent_of_glivenkoCantelli S m prob.θ₀ θn hGC
      slack hSlack hApprox hSep)
  oracleGMM_asymLinear prob hMeas δ hδ hInt S θn hcons
    (stochEquicontAt_of_asymptoticEquicont prob.score prob.θ₀ S θn hAEC hcons)
    hMoment

end

end Causalean.Stat
