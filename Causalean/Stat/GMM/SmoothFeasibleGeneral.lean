/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.GMM.SmoothFeasibleGeneralRate

/-! # Smooth feasible GMM asymptotics with a general weight

This module proves feasible-GMM asymptotic linearity and normality directly
from smooth observationwise moments, consistency, convergence of an arbitrary
estimated weight, and an approximate sample first-order condition.  Neither a
root-sample-size rate nor stochastic equicontinuity is assumed.

Use this smooth route for observationwise differentiable moments
(Newey--McFadden 1994, Theorem 3.2). Use the high-level `Feasible` route when
stochastic equicontinuity is established by a nonsmooth empirical-process
argument (Newey--McFadden 1994, Theorem 7.2; Andrews 1994).
-/

public section

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

/-- **Smooth feasible-GMM asymptotic linearity with a general weight.** For
[a GMM problem with an arbitrary population weight and smooth observationwise
moments](hyp:prob,reg), [an iid sample, estimator, and estimated
weights](hyp:S,θn,sampleW), if [the estimator is consistent](hyp:hConsistent),
[the estimated weights converge to the population weight](hyp:hWeight), and
[the normalized empirical first-order-condition residual is
`o_P(1)`](hyp:hApproxFOC), then [the estimator has the GMM influence-function
expansion with bread `(G'WG)⁻¹`](goal).

The root-sample-size rate and the smooth mean-value remainder are derived in
the proof; no rate or stochastic-equicontinuity premise is used. -/
theorem feasibleGMM_asymLinear_of_smoothMoment
    [IsProbabilityMeasure μ]
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E) (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.W‖) (fun _ => 0) μ)
    (hApproxFOC : IsLittleOp
      (fun n ω => ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L
        sampleW n ω) (gmmNormalizedMoment S prob.g (θn n ω) n ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S
      (fun n => Finset.range n) := by
  let : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  refine ⟨prob.influenceFunction.mean_zero,
    prob.influenceFunction.finite_var, ?_⟩
  · let U : ℕ → Ω → F :=
      IsAsymLinearVec.normalizedSum S (prob.g prob.θ₀) (fun n => Finset.range n)
    let T : ℕ → Ω → F := fun n ω =>
      gmmNormalizedMoment S prob.g (θn n ω) n ω
    let V : ℕ → Ω → E := fun n ω =>
      Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)
    let An : ℕ → Ω → (F →L[ℝ] E) := fun n ω =>
      adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L sampleW n ω
    let A0 : F →L[ℝ] E := adjoint prob.G ∘L prob.W
    let Q : ℕ → Ω → E := fun n ω => An n ω (T n ω)
    let delta : ℕ → Ω → ℝ := fun n ω => ‖An n ω - A0‖
    let err : ℕ → Ω → F := fun n ω =>
      T n ω - (U n ω + prob.G (V n ω))
    have hUeq (n : ℕ) (ω : Ω) :
        U n ω = gmmNormalizedMoment S prob.g prob.θ₀ n ω := by
      simp [U, gmmNormalizedMoment, IsAsymLinearVec.normalizedSum]
    have hRoot := feasibleGMM_rootRate_of_smoothMoment_generalWeight
      prob reg S θn sampleW hConsistent hWeight hApproxFOC
    have hVbig : IsBigOp (fun n ω => ‖V n ω‖) (fun _ => (1 : ℝ)) μ := by
      simpa [V, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hRoot
    have herr : IsLittleOp (fun n ω => ‖err n ω‖) (fun _ => (1 : ℝ)) μ := by
      simpa [err, T, V, hUeq] using
        gmmNormalizedMoment_expansion_isLittleOp reg S θn hConsistent hRoot
    have herrBig := herr.isBigOp_one
    have hdelta : IsLittleOp delta (fun _ => (1 : ℝ)) μ := by
      simpa [delta, An, A0] using
        feasibleGMMCombinedOperator_generalWeight_norm_sub_isLittleOp reg S θn sampleW
          hConsistent hWeight
    have hQlo : IsLittleOp (fun n ω => ‖Q n ω‖) (fun _ => (1 : ℝ)) μ := by
      simpa [Q, An, T] using hApproxFOC
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
      apply IsBigOp.of_abs_le
        (Yn := fun n ω => ‖U n ω‖ + ‖prob.G‖ * ‖V n ω‖ + ‖err n ω‖)
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
    have hAerr : IsLittleOp (fun n ω => ‖A0‖ * ‖err n ω‖)
        (fun _ => (1 : ℝ)) μ := by
      refine IsLittleOp.of_abs_le_const_mul_one
        (show 0 < ‖A0‖ + 1 by linarith [norm_nonneg A0]) herr ?_
      intro n ω
      simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by linarith [norm_nonneg A0]) (norm_nonneg _)
    let parRem : ℕ → Ω → E := fun n ω =>
      V n ω + prob.breadInv (A0 (U n ω))
    have hPar : IsLittleOp (fun n ω => ‖parRem n ω‖)
        (fun _ => (1 : ℝ)) μ := by
      let K : ℝ := ‖prob.breadInv‖ + 1
      have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg prob.breadInv]
      have hsmall := (hdeltaT.add_one hQlo).add_one hAerr
      refine IsLittleOp.of_abs_le_const_mul_one hK hsmall ?_
      intro n ω
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg <|
        add_nonneg (add_nonneg
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      have hleft : prob.breadInv (A0 (prob.G (V n ω))) = V n ω := by
        rw [show A0 (prob.G (V n ω)) = gmmBread prob.G prob.W (V n ω) by rfl,
          ← comp_apply, prob.breadInv_left, id_apply]
      have hid : parRem n ω = prob.breadInv
          ((A0 - An n ω) (T n ω) + Q n ω - A0 (err n ω)) := by
        dsimp [parRem]
        rw [← hleft, ← map_add]
        congr 1
        simp only [sub_apply]
        dsimp [Q, err]
        simp only [map_sub, map_add]
        abel
      rw [hid]
      calc
        ‖prob.breadInv ((A0 - An n ω) (T n ω) + Q n ω - A0 (err n ω))‖
            ≤ ‖prob.breadInv‖ *
                ‖(A0 - An n ω) (T n ω) + Q n ω - A0 (err n ω)‖ :=
              prob.breadInv.le_opNorm _
        _ ≤ ‖prob.breadInv‖ *
            (delta n ω * ‖T n ω‖ + ‖Q n ω‖ + ‖A0‖ * ‖err n ω‖) := by
          gcongr
          exact (norm_sub_le _ _).trans <| add_le_add
            ((norm_add_le _ _).trans <| add_le_add
              (by simpa [delta, norm_sub_rev] using
                (A0 - An n ω).le_opNorm (T n ω)) le_rfl)
            (A0.le_opNorm (err n ω))
        _ ≤ K *
            (delta n ω * ‖T n ω‖ + ‖Q n ω‖ + ‖A0‖ * ‖err n ω‖) := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [K]
            linarith [norm_nonneg prob.breadInv]
          · exact add_nonneg
              (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (norm_nonneg _))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa [parRem, V, U, A0, IsAsymLinearVec.normalizedSum,
      GMMProblem.influence, gmmIF, comp_apply, map_smul, map_sum] using hPar

/-- **Smooth feasible-GMM asymptotic normality with a general weight.** Under
[a general-weight GMM problem with smooth moments](hyp:prob,reg), [an iid
sample, estimator, and estimated weights](hyp:S,θn,sampleW), [consistency and
weight convergence](hyp:hConsistent,hWeight), [an `o_P(1)` normalized sample
first-order-condition residual](hyp:hApproxFOC), and [measurability of the
rescaled estimator](hyp:hθnMeas), [the rescaled estimator converges to the
centered Gaussian generated by the GMM influence function](goal).

Its covariance is the general sandwich operator `prob.asympVar`, as identified
by `GMMProblem.gaussianLimit_covarianceBilin`. -/
theorem feasibleGMM_tendsto_normal_of_smoothMoment
    [IsProbabilityMeasure μ]
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E) (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.W‖) (fun _ => 0) μ)
    (hApproxFOC : IsLittleOp
      (fun n ω => ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L
        sampleW n ω) (gmmNormalizedMoment S prob.g (θn n ω) n ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hθnMeas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθnMeas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit prob.influence_measurable prob.influence_integrable_sq,
        inferInstance⟩) := by
  have hAL := feasibleGMM_asymLinear_of_smoothMoment prob reg S θn sampleW
    hConsistent hWeight hApproxFOC
  exact hAL.tendsto_normal_vec_clt prob.influence_measurable
    (gaussianLimit prob.influence_measurable prob.influence_integrable_sq)
    (gaussianLimit_charFun prob.influence_measurable prob.influence_integrable_sq)
    hθnMeas

/-- **Sample-function smooth feasible-GMM asymptotic linearity.** If [a GMM
problem has smooth moments](hyp:prob,reg), [an estimator on each finite sample
vector and estimated weights are evaluated on an iid sample](hyp:est,S,sampleW),
and the induced estimator satisfies [consistency, general-weight convergence,
and the approximate sample FOC](hyp:hConsistent,hWeight,hApproxFOC), then [the
induced estimator has the GMM influence-function expansion](goal). -/
theorem feasibleGMM_asymLinear_of_smoothMoment_of_sampleFn
    [IsProbabilityMeasure μ]
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0, Tendsto (fun n =>
      μ {ω | ε < ‖est n (S.sampleVector n ω) - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.W‖) (fun _ => 0) μ)
    (hApproxFOC : IsLittleOp
      (fun n ω => ‖(adjoint
          (gmmSampleJacobian reg S (est n (S.sampleVector n ω)) n ω) ∘L
        sampleW n ω)
          (gmmNormalizedMoment S prob.g (est n (S.sampleVector n ω)) n ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) (fun n ω => est n (S.sampleVector n ω))
      prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  feasibleGMM_asymLinear_of_smoothMoment prob reg S
    (fun n ω => est n (S.sampleVector n ω)) sampleW
    hConsistent hWeight hApproxFOC

/-- **Sample-function smooth feasible-GMM asymptotic normality.** If [a GMM
problem has smooth moments](hyp:prob,reg), [an estimator on each finite sample
vector and estimated weights are evaluated on an iid sample](hyp:est,S,sampleW),
the induced estimator satisfies [consistency, general-weight convergence, and
the approximate sample FOC](hyp:hConsistent,hWeight,hApproxFOC), and [its
rescaled form is measurable](hyp:hEstMeas), then [its laws converge to the
centered Gaussian with the general GMM sandwich covariance](goal). -/
theorem feasibleGMM_tendsto_normal_of_smoothMoment_of_sampleFn
    [IsProbabilityMeasure μ]
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0, Tendsto (fun n =>
      μ {ω | ε < ‖est n (S.sampleVector n ω) - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.W‖) (fun _ => 0) μ)
    (hApproxFOC : IsLittleOp
      (fun n ω => ‖(adjoint
          (gmmSampleJacobian reg S (est n (S.sampleVector n ω)) n ω) ∘L
        sampleW n ω)
          (gmmNormalizedMoment S prob.g (est n (S.sampleVector n ω)) n ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hEstMeas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator
        (fun m ω => est m (S.sampleVector m ω)) prob.θ₀
        (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator
          (fun m ω => est m (S.sampleVector m ω)) prob.θ₀
          (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hEstMeas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit prob.influence_measurable prob.influence_integrable_sq,
        inferInstance⟩) :=
  feasibleGMM_tendsto_normal_of_smoothMoment prob reg S
    (fun n ω => est n (S.sampleVector n ω)) sampleW
    hConsistent hWeight hApproxFOC hEstMeas

end

end Causalean.Stat
