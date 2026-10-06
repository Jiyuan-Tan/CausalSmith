/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.GMM.ResidualProjection
public import Causalean.Stat.GMM.SmoothFeasible
public import Causalean.Stat.Inference.ChiSquaredWald

/-! # Hansen's J-test limit

This module proves the feasible efficient-GMM over-identification test.  Smooth
moments and an asymptotically negligible empirical first-order condition yield the residual
expansion, inverse-covariance weighting whitens the moment CLT, and quadratic
continuous mapping identifies the literal sample J statistic with the
chi-squared law having number-of-moments minus number-of-parameters degrees of
freedom.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped RealInnerProductSpace

noncomputable section

local notation "stdGaussian" => Causalean.Mathlib.stdGaussian

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

/-- **Hansen's J-test limit (Hansen 1982, Lemma 4.2; Newey–McFadden 1994,
§9.5, derived there from the restriction-test theory around Theorem 9.2).** For
[a correctly specified nonsingular GMM problem with smooth
moments](hyp:prob,reg), [an iid sample, feasible estimator, and estimated
weights](hyp:S,θn,sampleW), suppose [the estimator is consistent](hyp:hConsistent),
[the weights converge in probability to the inverse moment covariance](hyp:hWeight),
and [the normalized empirical GMM first-order-condition residual is
`o_P(1)`](hyp:hApproxFOC). If [the normalized fitted moment and literal J
statistic are measurable](hyp:hMomentMeas,hJMeas), then [the literal Hansen J
statistic converges in distribution to chi-squared with `finrank F - finrank E`
degrees of freedom](goal). -/
theorem hansenJ_tendsto_chiSq
    [IsProbabilityMeasure μ]
    (prob : EfficientGMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob.toGMMProblem) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E) (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.CovInv‖) (fun _ => 0) μ)
    (hApproxFOC : IsLittleOp
      (fun n ω => ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L
        sampleW n ω) (gmmNormalizedMoment S prob.g (θn n ω) n ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hMomentMeas : ∀ n, AEMeasurable
      (fun ω => gmmNormalizedMoment S prob.g (θn n ω) n ω) μ)
    (hJMeas : ∀ n, AEMeasurable
      (hansenJStatistic S prob.g θn sampleW n) μ) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n => ⟨μ.map (hansenJStatistic S prob.g θn sampleW n),
        Measure.isProbabilityMeasure_map (hJMeas n)⟩)
      atTop
      (𝓝 ⟨chiSqDist (Module.finrank ℝ F - Module.finrank ℝ E), inferInstance⟩) := by
  let ψ : X → F := prob.g prob.θ₀
  have hCovEq : secondMomentLM prob.g_meas prob.finite_var = prob.Cov := by
    ext t
    apply ext_inner_right ℝ
    intro s
    rw [secondMomentLM_inner]
    change (∫ x, ⟪t, prob.g prob.θ₀ x⟫ * ⟪s, prob.g prob.θ₀ x⟫ ∂P) =
      ⟪prob.Cov t, s⟫
    exact (prob.hCov t s).symm
  have hCovInj : Function.Injective prob.Cov := by
    intro x y hxy
    have h := congrArg prob.CovInv hxy
    have hleft : ∀ z, prob.CovInv (prob.Cov z) = z := fun z => by
      rw [← comp_apply, prob.CovInv_left, id_apply]
    simpa [hleft] using h
  have hSigmaInj : Function.Injective (secondMomentLM prob.g_meas prob.finite_var) := by
    simpa [hCovEq] using hCovInj
  let sqrtEquiv : F ≃ₗ[ℝ] F :=
    posSqrtEquiv prob.g_meas prob.finite_var hSigmaInj
  let sqrtCov : F →L[ℝ] F :=
    (secondMomentLM_isPositive prob.g_meas prob.finite_var).posSqrtCLM
  let whiten : F →L[ℝ] F :=
    (sqrtEquiv.symm : F →ₗ[ℝ] F).toContinuousLinearMap
  have hsqrtEquiv : ∀ x,
      sqrtEquiv x = sqrtCov x := fun x => rfl
  have hwhiten_sqrt : whiten ∘L sqrtCov = ContinuousLinearMap.id ℝ F := by
    ext x
    change sqrtEquiv.symm (sqrtEquiv x) = x
    exact sqrtEquiv.symm_apply_apply x
  have hsqrt_whiten : sqrtCov ∘L whiten = ContinuousLinearMap.id ℝ F := by
    ext x
    change sqrtEquiv (sqrtEquiv.symm x) = x
    exact sqrtEquiv.apply_symm_apply x
  have hsqrt_sa : adjoint sqrtCov = sqrtCov :=
    (secondMomentLM_isPositive prob.g_meas prob.finite_var).posSqrtCLM_adjoint
  have hwhiten_sa : adjoint whiten = whiten :=
    adjoint_inv_self hsqrt_sa hsqrt_whiten
  have hInvEq : secondMomentInv prob.g_meas prob.finite_var hSigmaInj = prob.CovInv := by
    ext x
    have hcovright : prob.Cov (prob.CovInv x) = x := by
      rw [← comp_apply, prob.CovInv_right, id_apply]
    calc
      secondMomentInv prob.g_meas prob.finite_var hSigmaInj x =
          secondMomentInv prob.g_meas prob.finite_var hSigmaInj
            (prob.Cov (prob.CovInv x)) := by rw [hcovright]
      _ = prob.CovInv x := by
        have hinv := secondMomentInv_secondMomentLM
          prob.g_meas prob.finite_var hSigmaInj (prob.CovInv x)
        rw [hCovEq] at hinv
        exact hinv
  have hwhiten_sq : whiten ∘L whiten = prob.CovInv := by
    rw [← hInvEq]
    rfl
  have hwhiten_sq_apply (x : F) : whiten (whiten x) = prob.CovInv x := by
    have h := congrArg (fun L : F →L[ℝ] F => L x) hwhiten_sq
    simpa only [comp_apply] using h
  let Gw : E →L[ℝ] F := whiten ∘L prob.G
  let Mw : F →L[ℝ] F := gmmResidualMaker Gw prob.effInv
  have hBreadW : adjoint Gw ∘L Gw = gmmBread prob.G prob.CovInv := by
    ext x
    simp only [Gw, gmmBread, adjoint_comp, comp_apply, hwhiten_sa]
    rw [hwhiten_sq_apply]
  have heL : prob.effInv ∘L (adjoint Gw ∘L Gw) =
      ContinuousLinearMap.id ℝ E := by rw [hBreadW, prob.effInv_left]
  have heR : (adjoint Gw ∘L Gw) ∘L prob.effInv =
      ContinuousLinearMap.id ℝ E := by rw [hBreadW, prob.effInv_right]
  let U : ℕ → Ω → F :=
    IsAsymLinearVec.normalizedSum S (prob.g prob.θ₀) (fun n => Finset.range n)
  let T : ℕ → Ω → F := fun n ω => gmmNormalizedMoment S prob.g (θn n ω) n ω
  have hUeq (n : ℕ) (ω : Ω) :
      U n ω = gmmNormalizedMoment S prob.g prob.θ₀ n ω := by
    simp [U, gmmNormalizedMoment, IsAsymLinearVec.normalizedSum]
  have hUmeas : ∀ n, AEMeasurable (U n) μ := by
    intro n
    exact ((Finset.measurable_sum _
      (fun i _ => prob.g_meas.comp (S.meas i))).const_smul _).aemeasurable
  have hRes := feasibleGMM_residualExpansion_of_smoothMoment
    prob reg S θn sampleW hConsistent hWeight hApproxFOC
  have hWhiteRes : IsLittleOp
      (fun n ω => ‖whiten (T n ω) - Mw (whiten (U n ω))‖)
      (fun _ => (1 : ℝ)) μ := by
    let K : ℝ := ‖whiten‖ + 1
    have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg whiten]
    refine IsLittleOp.of_abs_le_const_mul_one hK hRes ?_
    intro n ω
    have halg : whiten (prob.efficientResidualMaker (U n ω)) =
        Mw (whiten (U n ω)) := by
      simp only [EfficientGMMProblem.efficientResidualMaker, gmmResidualMaker, gmmHatMatrix,
        Mw, Gw, sub_apply, id_apply, comp_apply, adjoint_comp, hwhiten_sa]
      rw [hwhiten_sq_apply]
      exact map_sub whiten _ _
    rw [← halg, ← map_sub]
    simp only [abs_of_nonneg (norm_nonneg _)]
    calc
      ‖whiten (T n ω - prob.efficientResidualMaker (U n ω))‖ ≤
          ‖whiten‖ * ‖T n ω - prob.efficientResidualMaker (U n ω)‖ :=
        whiten.le_opNorm _
      _ ≤ K * ‖T n ω - prob.efficientResidualMaker (U n ω)‖ := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp [K]; linarith [norm_nonneg whiten]) (norm_nonneg _)
      _ = K * ‖gmmNormalizedMoment S prob.g (θn n ω) n ω -
          prob.efficientResidualMaker
            (gmmNormalizedMoment S prob.g prob.θ₀ n ω)‖ := by
        rw [show T n ω = gmmNormalizedMoment S prob.g (θn n ω) n ω by rfl,
          hUeq n ω]
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit prob.g_meas prob.finite_var) μ hUmeas := by
    exact S.clt_normalizedSum_vec prob.g_meas prob.finite_var prob.identification
  have hGaussianWhiten :
      (gaussianLimit prob.g_meas prob.finite_var).map whiten = stdGaussian F := by
    rw [gaussianLimit,
      Measure.map_map whiten.continuous.measurable sqrtCov.continuous.measurable]
    rw [show (whiten : F → F) ∘ (sqrtCov : F → F) = id by
      funext x
      have h := congrArg (fun L : F →L[ℝ] F => L x) hwhiten_sqrt
      simpa only [Function.comp_apply, comp_apply, id_eq, id_apply] using h]
    exact Measure.map_id
  have hWhitenUmeas : ∀ n, AEMeasurable (fun ω => whiten (U n ω)) μ := fun n =>
    whiten.continuous.measurable.aemeasurable.comp_aemeasurable (hUmeas n)
  have hWhitenU : Tendsto_dist_vec (fun n ω => whiten (U n ω))
      (stdGaussian F) μ hWhitenUmeas := by
    exact (Tendsto_dist_vec_iff _ _ _ hWhitenUmeas).2
      (hUclt.map_continuous_of_map_eq whiten.continuous hUmeas hGaussianWhiten)
  have hMwUmeas : ∀ n, AEMeasurable (fun ω => Mw (whiten (U n ω))) μ := fun n =>
    Mw.continuous.measurable.aemeasurable.comp_aemeasurable (hWhitenUmeas n)
  letI : IsProbabilityMeasure ((stdGaussian F).map Mw) :=
    Measure.isProbabilityMeasure_map Mw.continuous.measurable.aemeasurable
  have hMwU : Tendsto_dist_vec (fun n ω => Mw (whiten (U n ω)))
      ((stdGaussian F).map Mw) μ hMwUmeas := by
    exact (Tendsto_dist_vec_iff _ _ _ hMwUmeas).2
      (hWhitenU.map_continuous Mw.continuous hWhitenUmeas)
  have hWhitenTmeas : ∀ n, AEMeasurable (fun ω => whiten (T n ω)) μ := fun n =>
    whiten.continuous.measurable.aemeasurable.comp_aemeasurable (hMomentMeas n)
  have hWhitenT : Tendsto_dist_vec (fun n ω => whiten (T n ω))
      ((stdGaussian F).map Mw) μ hWhitenTmeas :=
    Tendsto_dist_vec.add_isLittleOp_one hMwUmeas hWhitenTmeas hMwU hWhiteRes
  have hTfromWhite : ∀ n, (fun ω => sqrtCov (whiten (T n ω))) =ᵐ[μ] T n := by
    intro n
    filter_upwards with ω
    have h := congrArg (fun L : F →L[ℝ] F => L (T n ω)) hsqrt_whiten
    simpa only [comp_apply, id_apply] using h
  have hTmeas : ∀ n, AEMeasurable (T n) μ := hMomentMeas
  let Qres : Measure F := (stdGaussian F).map Mw
  let Qun : Measure F := Qres.map sqrtCov
  letI : IsProbabilityMeasure Qun :=
    Measure.isProbabilityMeasure_map sqrtCov.continuous.measurable.aemeasurable
  have hSqrtWhite : Tendsto_dist_vec
      (fun n ω => sqrtCov (whiten (T n ω))) Qun μ
      (fun n => sqrtCov.continuous.measurable.aemeasurable.comp_aemeasurable
        (hWhitenTmeas n)) := by
    exact (Tendsto_dist_vec_iff _ _ _ _).2
      (hWhitenT.map_continuous sqrtCov.continuous hWhitenTmeas)
  have hTdist : Tendsto_dist_vec T Qun μ hTmeas := by
    exact Tendsto_dist_vec.congr_ae
      (fun n => sqrtCov.continuous.measurable.aemeasurable.comp_aemeasurable
        (hWhitenTmeas n)) hTmeas hSqrtWhite (by
          filter_upwards with n
          change (fun ω => sqrtCov (whiten (T n ω))) =ᵐ[μ] T n
          exact hTfromWhite n)
  have hJidentity : ∀ n,
      (fun ω => ⟪sampleW n ω (T n ω), T n ω⟫) =
        hansenJStatistic S prob.g θn sampleW n := by
    intro n
    funext ω
    by_cases hn : n = 0
    · subst n
      simp [T, gmmNormalizedMoment, hansenJStatistic, gmmSampleMoment]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      let z : F := ∑ i ∈ Finset.range n, prob.g (θn n ω) (S.Z i ω)
      have hscale : (Real.sqrt (n : ℝ))⁻¹ • z =
          Real.sqrt (n : ℝ) • ((n : ℝ)⁻¹ • z) := by
        rw [smul_smul]
        apply congrArg (fun c : ℝ => c • z)
        field_simp [hsqrt.ne', ne_of_gt hnpos]
        rw [Real.sq_sqrt hnpos.le]
      change ⟪sampleW n ω ((Real.sqrt (n : ℝ))⁻¹ • z),
          (Real.sqrt (n : ℝ))⁻¹ • z⟫ =
        (n : ℝ) * ⟪sampleW n ω ((n : ℝ)⁻¹ • z),
          (n : ℝ)⁻¹ • z⟫
      rw [hscale, map_smul, inner_smul_left, inner_smul_right]
      simp only [conj_trivial]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt hnpos.le]
  have hQuadMeas : ∀ n, AEMeasurable
      (fun ω => ⟪sampleW n ω (T n ω), T n ω⟫) μ := by
    intro n
    rw [hJidentity n]
    exact hJMeas n
  have hQuad := hTdist.quadraticForm_of_operator_tendstoInProb
    hTmeas sampleW prob.CovInv hWeight hQuadMeas
  have hQuadTarget : Qun.map (fun x => ⟪prob.CovInv x, x⟫) =
      chiSqDist (Module.finrank ℝ F - Module.finrank ℝ E) := by
    have hq : Measurable (fun x : F => ⟪prob.CovInv x, x⟫) :=
      (prob.CovInv.continuous.inner continuous_id).measurable
    dsimp [Qun, Qres]
    rw [Measure.map_map hq sqrtCov.continuous.measurable]
    have hpoint : (fun x : F => ⟪prob.CovInv (sqrtCov x), sqrtCov x⟫) =
        fun x => ‖x‖ ^ 2 := by
      funext x
      have hx : whiten (sqrtCov x) = x := by
        have h := congrArg (fun L : F →L[ℝ] F => L x) hwhiten_sqrt
        simpa only [comp_apply, id_apply] using h
      calc
        ⟪prob.CovInv (sqrtCov x), sqrtCov x⟫ =
            ⟪whiten (whiten (sqrtCov x)), sqrtCov x⟫ := by
          rw [hwhiten_sq_apply]
        _ = ⟪(adjoint whiten) (whiten (sqrtCov x)), sqrtCov x⟫ := by
          rw [hwhiten_sa]
        _ = ⟪whiten (sqrtCov x), whiten (sqrtCov x)⟫ :=
          adjoint_inner_left whiten (sqrtCov x) (whiten (sqrtCov x))
        _ = ‖x‖ ^ 2 := by rw [hx, real_inner_self_eq_norm_sq]
    change Measure.map (fun x : F => ⟪prob.CovInv (sqrtCov x), sqrtCov x⟫)
      (Measure.map (Mw : F → F) (stdGaussian F)) = _
    rw [hpoint]
    rw [Measure.map_map (by fun_prop : Measurable (fun x : F => ‖x‖ ^ 2))
      Mw.continuous.measurable]
    change (stdGaussian F).map (fun x => ‖Mw x‖ ^ 2) = _
    exact gaussian_residualProjection_chiSq heL heR
  have hQuadTargetPM :
      (⟨Qun.map (fun x => ⟪prob.CovInv x, x⟫),
        Measure.isProbabilityMeasure_map
          ((prob.CovInv.continuous.inner continuous_id).measurable.aemeasurable)⟩ :
          ProbabilityMeasure ℝ) =
        ⟨chiSqDist (Module.finrank ℝ F - Module.finrank ℝ E), inferInstance⟩ := by
    apply Subtype.ext
    exact hQuadTarget
  rw [hQuadTargetPM] at hQuad
  simpa only [hJidentity] using hQuad

end

end Causalean.Stat
