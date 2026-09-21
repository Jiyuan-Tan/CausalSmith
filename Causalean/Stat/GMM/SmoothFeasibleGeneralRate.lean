/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.GMM.Feasible
public import Causalean.Stat.GMM.SmoothMoment

/-! # General-weight smooth feasible GMM rate

This module derives the root-sample-size stochastic rate for smooth feasible
GMM with an arbitrary limiting weight.  The proof accepts an approximate sample
first-order condition and obtains the rate by stochastic absorption.
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

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- **Consistency of the general-weight feasible GMM combined operator.** For
[smooth moments](hyp:reg), [an iid sample and consistent estimator](hyp:S,θn,hConsistent),
and [estimated weights converging to the problem's general population
weight](hyp:sampleW,hWeight), [the empirical Jacobian-adjoint times the estimated
weight converges in probability to `G'W`](goal). -/
theorem feasibleGMMCombinedOperator_generalWeight_norm_sub_isLittleOp
    [IsProbabilityMeasure μ]
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E) (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hWeight : Tendsto_inProb
      (fun n ω => ‖sampleW n ω - prob.W‖) (fun _ => 0) μ) :
    IsLittleOp
      (fun n ω => ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L
          sampleW n ω) - (adjoint prob.G ∘L prob.W)‖)
      (fun _ => (1 : ℝ)) μ := by
  let Jdelta : ℕ → Ω → ℝ := fun n ω =>
    ‖gmmSampleJacobian reg S (θn n ω) n ω - prob.G‖
  let Wdelta : ℕ → Ω → ℝ := fun n ω => ‖sampleW n ω - prob.W‖
  let Wnorm : ℕ → Ω → ℝ := fun n ω => ‖sampleW n ω‖
  have hJlittle : IsLittleOp Jdelta (fun _ => (1 : ℝ)) μ := by
    simpa [Jdelta] using
      gmmSampleJacobian_norm_sub_isLittleOp reg S θn hConsistent
  have hWlittle : IsLittleOp Wdelta (fun _ => (1 : ℝ)) μ := by
    simpa [Wdelta] using hWeight.isLittleOp_one
  have hWdeltaBig := hWlittle.isBigOp_one
  have hconstBig : IsBigOp (fun (_ : ℕ) (_ : Ω) => ‖prob.W‖)
      (fun _ => (1 : ℝ)) μ := by
    intro δ hδ
    refine ⟨‖prob.W‖ + 1, by positivity, ?_⟩
    filter_upwards with n
    have hempty :
        {ω : Ω | (‖prob.W‖ + 1) * (1 : ℝ) ≤ ‖(‖prob.W‖ : ℝ)‖} = ∅ := by
      ext ω
      simp
    rw [hempty, measure_empty]
    exact hδ.le
  have hWnormBig : IsBigOp Wnorm (fun _ => (1 : ℝ)) μ := by
    apply IsBigOp.of_abs_le (Yn := fun n ω => Wdelta n ω + ‖prob.W‖)
    · intro n ω
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg
        (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc
        ‖sampleW n ω‖ = ‖(sampleW n ω - prob.W) + prob.W‖ := by
          congr 1
          abel
        _ ≤ ‖sampleW n ω - prob.W‖ + ‖prob.W‖ := norm_add_le _ _
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
          (adjoint prob.G ∘L prob.W) =
        ((adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
          sampleW n ω) +
        (adjoint prob.G ∘L (sampleW n ω - prob.W)) := by
    ext x
    simp only [sub_apply, add_apply, comp_apply, map_sub]
    abel
  rw [hid]
  calc
    ‖((adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
          sampleW n ω) +
        (adjoint prob.G ∘L (sampleW n ω - prob.W))‖
        ≤ ‖(adjoint (gmmSampleJacobian reg S (θn n ω) n ω) - adjoint prob.G) ∘L
            sampleW n ω‖ +
          ‖adjoint prob.G ∘L (sampleW n ω - prob.W)‖ := norm_add_le _ _
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
          ‖adjoint prob.G ∘L (sampleW n ω - prob.W)‖
              ≤ ‖adjoint prob.G‖ * ‖sampleW n ω - prob.W‖ := opNorm_comp_le _ _
          _ = ‖prob.G‖ * Wdelta n ω := by simp [Wdelta]

/-- **Root-sample-size rate for smooth feasible GMM with a general weight.** For
[a smooth GMM problem](hyp:prob,reg), [an iid sample, estimator, and estimated
weights](hyp:S,θn,sampleW), if [the estimator is consistent](hyp:hConsistent),
[the weights converge to the general population weight](hyp:hWeight), and [the
normalized sample first-order-condition residual is `o_P(1)`](hyp:hApproxFOC),
then [the root-sample-size parameter error is bounded in probability](goal). -/
theorem feasibleGMM_rootRate_of_smoothMoment_generalWeight
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
    IsBigOp (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - prob.θ₀‖)
      (fun _ => (1 : ℝ)) μ := by
  let U : ℕ → Ω → F :=
    IsAsymLinearVec.normalizedSum S (prob.g prob.θ₀) (fun n => Finset.range n)
  let T : ℕ → Ω → F := fun n ω =>
    gmmNormalizedMoment S prob.g (θn n ω) n ω
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)‖
  let An : ℕ → Ω → (F →L[ℝ] E) := fun n ω =>
    adjoint (gmmSampleJacobian reg S (θn n ω) n ω) ∘L sampleW n ω
  let A0 : F →L[ℝ] E := adjoint prob.G ∘L prob.W
  let Q : ℕ → Ω → E := fun n ω => An n ω (T n ω)
  let delta : ℕ → Ω → ℝ := fun n ω => ‖An n ω - A0‖
  have hUeq (n : ℕ) (ω : Ω) :
      U n ω = gmmNormalizedMoment S prob.g prob.θ₀ n ω := by
    simp [U, gmmNormalizedMoment, IsAsymLinearVec.normalizedSum]
  rcases exists_gmmNormalizedMoment_expansion_control reg S θn hConsistent with
    ⟨C, hClo, hCnonneg, hExpansion⟩
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
  have hCbig := hClo.isBigOp_one
  have hdeltabig := hdelta.isBigOp_one
  have hQbig := hQlo.isBigOp_one
  have hconstA : IsBigOp (fun (_ : ℕ) (_ : Ω) => ‖A0‖)
      (fun _ => (1 : ℝ)) μ := by
    intro δ hδ
    refine ⟨‖A0‖ + 1, by positivity, ?_⟩
    filter_upwards with n
    have hempty : {ω : Ω | (‖A0‖ + 1) * (1 : ℝ) ≤ ‖(‖A0‖ : ℝ)‖} = ∅ := by
      ext ω
      simp
    rw [hempty, measure_empty]
    exact hδ.le
  have hconstG : IsBigOp (fun (_ : ℕ) (_ : Ω) => ‖prob.G‖)
      (fun _ => (1 : ℝ)) μ := by
    intro δ hδ
    refine ⟨‖prob.G‖ + 1, by positivity, ?_⟩
    filter_upwards with n
    have hempty :
        {ω : Ω | (‖prob.G‖ + 1) * (1 : ℝ) ≤ ‖(‖prob.G‖ : ℝ)‖} = ∅ := by
      ext ω
      simp
    rw [hempty, measure_empty]
    exact hδ.le
  let V : ℕ → Ω → ℝ := fun n ω => delta n ω + ‖A0‖
  let Gc : ℕ → Ω → ℝ := fun n ω => ‖prob.G‖ + C n ω
  have hVbig : IsBigOp V (fun _ => (1 : ℝ)) μ := by
    simpa [V, add_comm] using
      hdeltabig.add hconstA
  have hGcbig : IsBigOp Gc (fun _ => (1 : ℝ)) μ := by
    simpa [Gc, add_comm] using
      hconstG.add hCbig
  have hdeltaGc : IsLittleOp (fun n ω => delta n ω * Gc n ω)
      (fun _ => (1 : ℝ)) μ := by
    simpa using hdelta.mul_isBigOp
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one) hGcbig
  have hA0C : IsLittleOp (fun n ω => ‖A0‖ * C n ω)
      (fun _ => (1 : ℝ)) μ := by
    refine IsLittleOp.of_abs_le_const_mul_one
      (show 0 < ‖A0‖ + 1 by linarith [norm_nonneg A0]) hClo ?_
    intro n ω
    simp only [abs_mul, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (hCnonneg n ω)]
    exact mul_le_mul_of_nonneg_right
      (by linarith [norm_nonneg A0]) (hCnonneg n ω)
  let K : ℝ := ‖prob.breadInv‖ + 1
  have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg prob.breadInv]
  let Ac : ℕ → Ω → ℝ := fun n ω =>
    K * (delta n ω * Gc n ω + ‖A0‖ * C n ω)
  let B : ℕ → Ω → ℝ := fun n ω =>
    K * (V n ω * ‖U n ω‖ + ‖Q n ω‖)
  have hAcLittle : IsLittleOp Ac (fun _ => (1 : ℝ)) μ := by
    have hsum := hdeltaGc.add_one hA0C
    refine IsLittleOp.of_abs_le_const_mul_one hK hsum ?_
    intro n ω
    simp [Ac, abs_mul, abs_of_pos hK]
  have hVUbig : IsBigOp (fun n ω => V n ω * ‖U n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa using IsBigOp.mul (fun _ => zero_le_one) (fun _ => zero_le_one)
      hVbig hUbig
  have hBbig : IsBigOp B (fun _ => (1 : ℝ)) μ := by
    simpa [B] using IsBigOp.const_mul K
      (hVUbig.add hQbig)
  have hAcNonneg : ∀ n ω, 0 ≤ Ac n ω := by
    intro n ω
    exact mul_nonneg hK.le <| add_nonneg
      (mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (hCnonneg n ω)))
      (mul_nonneg (norm_nonneg _) (hCnonneg n ω))
  have hBNonneg : ∀ n ω, 0 ≤ B n ω := by
    intro n ω
    exact mul_nonneg hK.le <| add_nonneg
      (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      (norm_nonneg _)
  have hYNonneg : ∀ n ω, 0 ≤ Y n ω := fun n ω => norm_nonneg _
  have hRateBound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
      Y n ω ≤ B n ω + Ac n ω * Y n ω := by
    filter_upwards [] with n
    filter_upwards [] with ω
    let v : E := Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)
    let err : F := T n ω - (U n ω + prob.G v)
    have hBread : A0 (prob.G v) = gmmBread prob.G prob.W v := by
      rfl
    have hleft : prob.breadInv (A0 (prob.G v)) = v := by
      rw [hBread, ← comp_apply, prob.breadInv_left, id_apply]
    have hvid : v = prob.breadInv
        ((A0 - An n ω) (T n ω) + Q n ω - A0 (U n ω) - A0 err) := by
      rw [show (A0 - An n ω) (T n ω) + Q n ω - A0 (U n ω) - A0 err =
          A0 (prob.G v) by
        simp only [sub_apply]
        dsimp [Q]
        dsimp [err]
        simp only [map_sub, map_add]
        abel]
      exact hleft.symm
    have hTbound : ‖T n ω‖ ≤ ‖U n ω‖ + Gc n ω * Y n ω := by
      have herr := hExpansion n ω
      rw [← hUeq n ω] at herr
      calc
        ‖T n ω‖ = ‖(U n ω + prob.G v) +
            (T n ω - (U n ω + prob.G v))‖ := by
          congr 1
          abel
        _ ≤ ‖U n ω + prob.G v‖ +
            ‖T n ω - (U n ω + prob.G v)‖ := norm_add_le _ _
        _ ≤ (‖U n ω‖ + ‖prob.G‖ * ‖v‖) + C n ω * ‖v‖ := by
          exact add_le_add
            ((norm_add_le _ _).trans <| add_le_add le_rfl (prob.G.le_opNorm v))
            (by simpa [T, v, Y] using herr)
        _ = ‖U n ω‖ + Gc n ω * Y n ω := by
          simp only [v, Y, Gc]
          ring
    calc
      Y n ω = ‖v‖ := rfl
      _ = ‖prob.breadInv
          ((A0 - An n ω) (T n ω) + Q n ω - A0 (U n ω) - A0 err)‖ := by
        rw [hvid]
      _ ≤ ‖prob.breadInv‖ *
          ‖(A0 - An n ω) (T n ω) + Q n ω - A0 (U n ω) - A0 err‖ :=
        prob.breadInv.le_opNorm _
      _ ≤ ‖prob.breadInv‖ *
          (delta n ω * ‖T n ω‖ + ‖Q n ω‖ +
            ‖A0‖ * ‖U n ω‖ + ‖A0‖ * ‖err‖) := by
        gcongr
        calc
          ‖(A0 - An n ω) (T n ω) + Q n ω - A0 (U n ω) - A0 err‖
              ≤ ‖(A0 - An n ω) (T n ω)‖ + ‖Q n ω‖ +
                  ‖A0 (U n ω)‖ + ‖A0 err‖ := by
                exact (norm_sub_le _ _).trans <|
                  add_le_add ((norm_sub_le _ _).trans <|
                    add_le_add (norm_add_le _ _) le_rfl) le_rfl
          _ ≤ delta n ω * ‖T n ω‖ + ‖Q n ω‖ +
                ‖A0‖ * ‖U n ω‖ + ‖A0‖ * ‖err‖ := by
              gcongr
              · simpa [delta, norm_sub_rev] using
                  (A0 - An n ω).le_opNorm (T n ω)
              · exact A0.le_opNorm (U n ω)
              · exact A0.le_opNorm err
      _ ≤ ‖prob.breadInv‖ *
          (delta n ω * (‖U n ω‖ + Gc n ω * Y n ω) + ‖Q n ω‖ +
            ‖A0‖ * ‖U n ω‖ + ‖A0‖ * (C n ω * Y n ω)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact add_le_add
          (add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hTbound (norm_nonneg _)) le_rfl)
            le_rfl)
          (mul_le_mul_of_nonneg_left (by
            have hexp := hExpansion n ω
            rw [← hUeq n ω] at hexp
            simpa [T, v, Y, err] using hexp) (norm_nonneg _))
      _ ≤ K *
          (delta n ω * (‖U n ω‖ + Gc n ω * Y n ω) + ‖Q n ω‖ +
            ‖A0‖ * ‖U n ω‖ + ‖A0‖ * (C n ω * Y n ω)) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [K]
          linarith [norm_nonneg prob.breadInv]
        · exact add_nonneg
            (add_nonneg
              (add_nonneg
                (mul_nonneg (norm_nonneg _) <|
                  add_nonneg (norm_nonneg _) <|
                    mul_nonneg (add_nonneg (norm_nonneg _) (hCnonneg n ω))
                      (norm_nonneg _))
                (norm_nonneg _))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            (mul_nonneg (norm_nonneg _) <|
              mul_nonneg (hCnonneg n ω) (norm_nonneg _))
      _ = B n ω + Ac n ω * Y n ω := by
        simp only [B, Ac, V]
        ring
  have hYbig := hAcLittle.isBigOp_of_absorption hBbig hAcNonneg hBNonneg
    hYNonneg hRateBound
  simpa [Y, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hYbig

end

end Causalean.Stat
