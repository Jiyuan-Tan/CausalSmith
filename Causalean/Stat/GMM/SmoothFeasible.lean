/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.GMM.Feasible
public import Causalean.Stat.GMM.SmoothFeasibleGeneralRate
public import Causalean.Stat.GMM.SmoothMoment
public import Causalean.Stat.Limit.QuadraticForm

/-! # Smooth feasible GMM expansions

This module derives the parametric rate and efficient residual expansion for a
feasible GMM estimator directly from smooth observationwise moments, consistent
inverse-covariance weights, consistency of the estimator, and an approximate
sample first-order condition negligible at the root-sample-size scale.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped RealInnerProductSpace

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

/-- For [a bundled GMM problem](hyp:prob), the [efficient unwhitened residual
operator](goal) is `I - G (G'Ω⁻¹G)⁻¹ G'Ω⁻¹`; it removes the moment directions
fitted by efficient GMM. -/
noncomputable def EfficientGMMProblem.efficientResidualMaker
    (prob : EfficientGMMProblem (E := E) (F := F) P) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F -
    prob.G ∘L prob.effInv ∘L adjoint prob.G ∘L prob.CovInv

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- **Consistency of the feasible GMM combined operator.** For [smooth GMM
moments](hyp:reg), [an iid sample and consistent estimator](hyp:S,θn,hConsistent),
and [estimated weights converging in operator norm to the inverse moment
covariance](hyp:sampleW,hWeight), [the empirical Jacobian-adjoint times the
estimated weight converges in operator norm to `G'Ω⁻¹`](goal). -/
theorem feasibleGMMCombinedOperator_norm_sub_isLittleOp
    [IsProbabilityMeasure μ]
    {prob : EfficientGMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob.toGMMProblem) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E) (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.CovInv‖) (fun _ => 0) μ) :
    IsLittleOp
      (fun n ω => ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L
          sampleW n ω) - (adjoint prob.G ∘L prob.CovInv)‖)
      (fun _ => (1 : ℝ)) μ := by
  let Jdelta : ℕ → Ω → ℝ := fun n ω =>
    ‖gmmSampleJacobian reg S (θn n ω) n ω - prob.G‖
  let Wdelta : ℕ → Ω → ℝ := fun n ω => ‖sampleW n ω - prob.CovInv‖
  let Wnorm : ℕ → Ω → ℝ := fun n ω => ‖sampleW n ω‖
  have hJlittle : IsLittleOp Jdelta (fun _ => (1 : ℝ)) μ := by
    simpa [Jdelta] using
      gmmSampleJacobian_norm_sub_isLittleOp reg S θn hConsistent
  have hWlittle : IsLittleOp Wdelta (fun _ => (1 : ℝ)) μ := by
    simpa [Wdelta] using hWeight.isLittleOp_one
  have hWdeltaBig := hWlittle.isBigOp_one
  have hconstBig : IsBigOp (fun (_ : ℕ) (_ : Ω) => ‖prob.CovInv‖)
      (fun _ => (1 : ℝ)) μ := by
    intro δ hδ
    refine ⟨‖prob.CovInv‖ + 1, by positivity, ?_⟩
    filter_upwards with n
    have hempty :
        {ω : Ω | (‖prob.CovInv‖ + 1) * (1 : ℝ) ≤ ‖(‖prob.CovInv‖ : ℝ)‖} = ∅ := by
      ext ω
      simp
    rw [hempty, measure_empty]
    exact hδ.le
  have hWnormBig : IsBigOp Wnorm (fun _ => (1 : ℝ)) μ := by
    apply IsBigOp.of_abs_le (Yn := fun n ω => Wdelta n ω + ‖prob.CovInv‖)
    · intro n ω
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg
        (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc
        ‖sampleW n ω‖ = ‖(sampleW n ω - prob.CovInv) + prob.CovInv‖ := by
          congr 1
          abel
        _ ≤ ‖sampleW n ω - prob.CovInv‖ + ‖prob.CovInv‖ := norm_add_le _ _
    · exact hWdeltaBig.add hconstBig
  have hJW : IsLittleOp (fun n ω => Jdelta n ω * Wnorm n ω)
      (fun _ => (1 : ℝ)) μ := by
    simpa using hJlittle.mul_isBigOp
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one) hWnormBig
  have hGW : IsLittleOp (fun n ω => ‖prob.G‖ * Wdelta n ω)
      (fun _ => (1 : ℝ)) μ := by
    exact IsLittleOp.of_abs_le_const_mul_one
      (show 0 < ‖prob.G‖ + 1 by linarith [norm_nonneg prob.G]) hWlittle <| fun n ω => by
        simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_right
          (by linarith [norm_nonneg prob.G]) (abs_nonneg _)
  have hsum := hJW.add_one hGW
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) zero_lt_one hsum ?_
  intro n ω
  rw [one_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg <|
    add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hid :
      (adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L sampleW n ω) -
          (adjoint prob.G ∘L prob.CovInv) =
        ((adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
          sampleW n ω) +
        (adjoint prob.G ∘L (sampleW n ω - prob.CovInv)) := by
    ext x
    simp only [sub_apply, add_apply, comp_apply, map_sub]
    abel
  rw [hid]
  calc
    ‖((adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
          sampleW n ω) +
        (adjoint prob.G ∘L (sampleW n ω - prob.CovInv))‖
        ≤ ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
            sampleW n ω‖ +
          ‖adjoint prob.G ∘L (sampleW n ω - prob.CovInv)‖ := norm_add_le _ _
    _ ≤ Jdelta n ω * Wnorm n ω + ‖prob.G‖ * Wdelta n ω := by
      apply add_le_add
      · calc
          ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
              sampleW n ω‖
              ≤ ‖adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G‖ *
                  ‖sampleW n ω‖ := opNorm_comp_le _ _
          _ = Jdelta n ω * Wnorm n ω := by
            have hadj :
                ‖adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G‖ =
                  ‖gmmSampleJacobian reg S (θn n ω) n ω - prob.G‖ := by
              rw [← map_sub]
              exact ContinuousLinearMap.adjoint.norm_map _
            exact congrArg (fun r : ℝ => r * ‖sampleW n ω‖) hadj
      · calc
          ‖adjoint prob.G ∘L (sampleW n ω - prob.CovInv)‖
              ≤ ‖adjoint prob.G‖ * ‖sampleW n ω - prob.CovInv‖ := opNorm_comp_le _ _
          _ = ‖prob.G‖ * Wdelta n ω := by simp [Wdelta]

/-- **Root-sample-size rate from the smooth feasible GMM FOC.** For [a smooth
GMM problem](hyp:prob,reg), [an iid sample, estimator, and estimated
weights](hyp:S,θn,sampleW), if [the estimator is consistent](hyp:hConsistent),
[the estimated weights converge to the inverse moment covariance](hyp:hWeight),
and [the normalized empirical first-order-condition residual is
`o_P(1)`](hyp:hApproxFOC),
then [the root-sample-size parameter error is bounded in probability](goal). -/
theorem feasibleGMM_rootRate_of_smoothMoment
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
      (fun _ => (1 : ℝ)) μ) :
    IsBigOp (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - prob.θ₀‖)
      (fun _ => (1 : ℝ)) μ := by
  let regEff : SmoothGMomentRegularity prob.efficientProblem := reg.ofEfficientProblem
  simpa [EfficientGMMProblem.efficientProblem] using
    feasibleGMM_rootRate_of_smoothMoment_generalWeight
      prob.efficientProblem regEff S θn sampleW hConsistent hWeight hApproxFOC


/-- **Efficient feasible-GMM residual expansion.** Under [smooth GMM
regularity](hyp:prob,reg), [an iid sample, consistent estimator, and estimated
weights](hyp:S,θn,sampleW,hConsistent), [inverse-covariance weight
consistency](hyp:hWeight), and [an empirical first-order-condition residual
that is negligible after root-sample-size normalization](hyp:hApproxFOC),
[the normalized fitted sample moment differs by
`o_P(1)` from the efficient residual operator applied to the normalized true
sample moment](goal). -/
theorem feasibleGMM_residualExpansion_of_smoothMoment
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
      (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω => ‖gmmNormalizedMoment S prob.g (θn n ω) n ω -
        prob.efficientResidualMaker
          (gmmNormalizedMoment S prob.g prob.θ₀ n ω)‖)
      (fun _ => (1 : ℝ)) μ := by
  let U : ℕ → Ω → F :=
    IsAsymLinearVec.normalizedSum S (prob.g prob.θ₀) (fun n => Finset.range n)
  let T : ℕ → Ω → F := fun n ω => gmmNormalizedMoment S prob.g (θn n ω) n ω
  let V : ℕ → Ω → E := fun n ω =>
    Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)
  let An : ℕ → Ω → (F →L[ℝ] E) := fun n ω =>
    adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L sampleW n ω
  let A0 : F →L[ℝ] E := adjoint prob.G ∘L prob.CovInv
  let delta : ℕ → Ω → ℝ := fun n ω => ‖An n ω - A0‖
  let err : ℕ → Ω → F := fun n ω => T n ω - (U n ω + prob.G (V n ω))
  have hUeq (n : ℕ) (ω : Ω) :
      U n ω = gmmNormalizedMoment S prob.g prob.θ₀ n ω := by
    simp [U, gmmNormalizedMoment, IsAsymLinearVec.normalizedSum]
  have hRoot := feasibleGMM_rootRate_of_smoothMoment prob reg S θn sampleW
    hConsistent hWeight hApproxFOC
  have hVbig : IsBigOp (fun n ω => ‖V n ω‖) (fun _ => (1 : ℝ)) μ := by
    simpa [V, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hRoot
  have herr : IsLittleOp (fun n ω => ‖err n ω‖) (fun _ => (1 : ℝ)) μ := by
    simpa [err, T, V, hUeq] using
      gmmNormalizedMoment_expansion_isLittleOp reg S θn hConsistent hRoot
  have herrBig := herr.isBigOp_one
  have hdelta : IsLittleOp delta (fun _ => (1 : ℝ)) μ := by
    simpa [delta, An, A0] using
      feasibleGMMCombinedOperator_norm_sub_isLittleOp reg S θn sampleW
        hConsistent hWeight
  have hUmeas : ∀ n, AEMeasurable (U n) μ := by
    intro n
    exact ((Finset.measurable_sum _
      (fun i _ => prob.g_meas.comp (S.meas i))).const_smul _).aemeasurable
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit prob.g_meas prob.finite_var) μ hUmeas := by
    exact S.clt_normalizedSum_vec prob.g_meas prob.finite_var prob.identification
  have hNormUclt := hUclt.map_continuous continuous_norm hUmeas
  have hUbig : IsBigOp (fun n ω => ‖U n ω‖) (fun _ => (1 : ℝ)) μ := by
    letI : IsProbabilityMeasure
        ((gaussianLimit prob.g_meas prob.finite_var).map norm) :=
      Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
    exact Tendsto_dist.tightness
      (fun n => continuous_norm.measurable.comp_aemeasurable (hUmeas n))
      ((Tendsto_dist_iff _ _ _ _).2 hNormUclt)
  have hGVbig : IsBigOp (fun n ω => ‖prob.G‖ * ‖V n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    exact IsBigOp.const_mul ‖prob.G‖ hVbig
  have hTbig : IsBigOp (fun n ω => ‖T n ω‖) (fun _ => (1 : ℝ)) μ := by
    apply IsBigOp.of_abs_le (Yn := fun n ω => ‖U n ω‖ + ‖prob.G‖ * ‖V n ω‖ + ‖err n ω‖)
    · intro n ω
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg
        (add_nonneg (add_nonneg (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))]
      have hid : T n ω = U n ω + prob.G (V n ω) + err n ω := by
        dsimp [err]
        abel
      rw [hid]
      exact (norm_add_le _ _).trans <| add_le_add
        ((norm_add_le _ _).trans <| add_le_add_right (prob.G.le_opNorm _) _) le_rfl
    · exact (hUbig.add hGVbig).add herrBig
  have hdeltaT : IsLittleOp (fun n ω => delta n ω * ‖T n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa using hdelta.mul_isBigOp
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one) hTbig
  have hQ : IsLittleOp (fun n ω => ‖An n ω (T n ω)‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa [An, T] using hApproxFOC
  have hAerr : IsLittleOp (fun n ω => ‖A0‖ * ‖err n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    refine IsLittleOp.of_abs_le_const_mul_one
      (show 0 < ‖A0‖ + 1 by linarith [norm_nonneg A0]) herr ?_
    intro n ω
    simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by linarith [norm_nonneg A0]) (norm_nonneg _)
  let parRem : ℕ → Ω → E := fun n ω =>
    V n ω + prob.effInv (A0 (U n ω))
  have hPar' : IsLittleOp (fun n ω => ‖parRem n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    let K : ℝ := ‖prob.effInv‖ + 1
    have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg prob.effInv]
    refine IsLittleOp.of_abs_le_const_mul_one hK
      ((hdeltaT.add_one hQ).add_one hAerr) ?_
    intro n ω
    have hleft : prob.effInv (A0 (prob.G (V n ω))) = V n ω := by
      rw [show A0 (prob.G (V n ω)) = gmmBread prob.G prob.CovInv (V n ω) by rfl,
        ← comp_apply, prob.effInv_left, id_apply]
    have hid : parRem n ω = prob.effInv
        ((A0 - An n ω) (T n ω) + An n ω (T n ω) - A0 (err n ω)) := by
      dsimp [parRem]
      rw [← hleft, ← map_add]
      congr 1
      simp only [sub_apply, map_sub, map_add]
      dsimp [err]
      simp only [map_sub, map_add]
      abel
    rw [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (by positivity :
        0 ≤ delta n ω * ‖T n ω‖ + ‖An n ω (T n ω)‖ +
          ‖A0‖ * ‖err n ω‖), hid]
    calc
      ‖prob.effInv
          ((A0 - An n ω) (T n ω) + An n ω (T n ω) - A0 (err n ω))‖
          ≤ ‖prob.effInv‖ *
            ‖(A0 - An n ω) (T n ω) + An n ω (T n ω) - A0 (err n ω)‖ :=
        prob.effInv.le_opNorm _
      _ ≤ ‖prob.effInv‖ *
          (delta n ω * ‖T n ω‖ + ‖An n ω (T n ω)‖ +
            ‖A0‖ * ‖err n ω‖) := by
        gcongr
        exact (norm_sub_le _ _).trans <| add_le_add
          ((norm_add_le _ _).trans <| add_le_add
            (by simpa [delta, norm_sub_rev] using
              (A0 - An n ω).le_opNorm (T n ω)) le_rfl)
          (A0.le_opNorm (err n ω))
      _ ≤ K *
          (delta n ω * ‖T n ω‖ + ‖An n ω (T n ω)‖ +
            ‖A0‖ * ‖err n ω‖) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [K]
          linarith [norm_nonneg prob.effInv]
        · positivity
  have hGpar : IsLittleOp (fun n ω => ‖prob.G‖ * ‖parRem n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    refine IsLittleOp.of_abs_le_const_mul_one
      (show 0 < ‖prob.G‖ + 1 by linarith [norm_nonneg prob.G]) hPar' ?_
    intro n ω
    simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by linarith [norm_nonneg prob.G]) (norm_nonneg _)
  have hsum := herr.add_one hGpar
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) zero_lt_one hsum ?_
  intro n ω
  rw [one_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg <|
    add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hid : T n ω - prob.efficientResidualMaker (U n ω) =
      err n ω + prob.G (parRem n ω) := by
    have hTexp : T n ω = U n ω + prob.G (V n ω) + err n ω := by
      dsimp [err]
      abel
    rw [hTexp]
    simp only [EfficientGMMProblem.efficientResidualMaker, sub_apply, id_apply, comp_apply]
    dsimp [parRem, A0]
    simp only [map_add]
    abel
  rw [show gmmNormalizedMoment S prob.g (θn n ω) n ω = T n ω by rfl,
    show gmmNormalizedMoment S prob.g prob.θ₀ n ω = U n ω by
      exact (hUeq n ω).symm, hid]
  exact (norm_add_le _ _).trans <| add_le_add_right (prob.G.le_opNorm _) _

end

end Causalean.Stat
