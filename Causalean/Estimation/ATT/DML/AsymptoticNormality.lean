/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATT.DML.Feasible

/-! # Asymptotic normality of feasible one-shot ATT DML

This file derives the true-standard-deviation Gaussian limit of the feasible
sample-treated-share ATT estimator from the primitive overlap, moment,
cross-fitting, and nuisance-rate assumptions of its asymptotic-linearity
theorem.
-/

public section

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open TreatedEstimationSystem
open Causalean.Estimation.OrthogonalMoments
open Causalean.Estimation.ATE.BackdoorEstimationSystem (indA)

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Standard-normal limit of feasible ATT DML.** For [a potential-outcomes
system](hyp:P), [a measurable covariate space](hyp:γ), [a treated estimation
system](hyp:S), [an overlap radius](hyp:ε), [truth-nuisance overlap membership](hyp:hη₀_mem), [a
nonnegative true propensity](hyp:h_e_lb), [one-sided overlap](hyp:h_overlap),
[the back-door ATT assumptions](hyp:hA), [a positive treated share](hyp:hπ_pos),
[factual- and untreated-outcome second moments](hyp:h_y2,h_y0_2), [integrable
truth IPW correction](hyp:hIPW), [an i.i.d. sample](hyp:sample), [a one-shot
split](hyp:split), [a limiting evaluation-fold share](hyp:c), [that share being
positive and below one](hyp:hc_pos,hc_lt), [convergence of the evaluation-fold
share](hyp:h_split_rate),
and [a complementary-fold nuisance sequence](hyp:η_hat), if [every fitted
nuisance lies in the overlap set](hyp:h_in_Hε), [every fitted propensity is
nonnegative](hyp:h_e_lb_hat), [both fitted nuisance errors are
square-integrable](hyp:h_mu_diff_memLp,h_e_diff_memLp), [each fitted IPW
correction is integrable](hyp:h_IPW_at), [the fitted score has the required
joint and training-fold measurability](hyp:h_m_meas,h_m_foldA,h_m_foldA_uncurry),
[the fitted score is integrable and square-integrable](hyp:h_m_int,h_m_sq_int),
[both nuisance errors are individually negligible](hyp:h_indiv_rate_ρ₁,h_indiv_rate_ρ₂),
[their product is negligible at the root-sample rate](hyp:h_product_rate),
[a true influence-function standard deviation](hyp:σ) [is positive and has its
defining second-moment identity](hyp:hσ_pos,hσ_sq), and [the rescaled estimator
and its standardized version are measurable](hyp:hNum_meas,hStud_meas), then
[the true-standard-deviation-normalized feasible ATT estimator converges to the
standard normal law](goal).

The influence function used in `hσ_sq` is equation (5.4) of Chernozhukov et
al. (2018) at the truth, including the `-D * θ₀ / p` treated-share term. -/
theorem dml_ATT_tendstoStandardNormal
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (h_e_lb : ∀ x, 0 ≤ S.e_val x)
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω =>
      (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω =>
      (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (hIPW : Integrable (fun ω =>
      (1 - S.toPOBackdoorSystem.dVar.indicator true ω) *
        (S.toPOBackdoorSystem.propScore true ω /
          (1 - S.toPOBackdoorSystem.propScore true ω)) *
        (S.toPOBackdoorSystem.factualY ω -
          S.toPOBackdoorSystem.adjustedCE false ω)) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε S ε)
    (h_e_lb_hat : ∀ n ω x, 0 ≤ (η_hat n ω).e_fn x)
    (h_mu_diff_memLp : ∀ n ω, MemLp
      (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X)
    (h_e_diff_memLp : ∀ n ω, MemLp
      (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_IPW_at : ∀ n ω, Integrable (fun z =>
      (1 - indA z) *
        ((η_hat n ω).e_fn
            (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z) /
          (1 - (η_hat n ω).e_fn
            (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z))) *
        (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z -
          (η_hat n ω).μ₀_fn
            (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z))) S.P_Z)
    (h_m_meas : ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
      aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_foldA : ∀ n,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀))
    (h_m_foldA_uncurry : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
        (fun (p : P.Ω × (γ × Bool × ℝ)) =>
          aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_int : ∀ n ω, Integrable
      (fun z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω, Integrable
      (fun z => (aipwMomentATTFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z)
    (h_indiv_rate_ρ₁ : IsLittleOp
      (fun n ω => (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
        (η_hat n ω) S.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) P.μ)
    (h_indiv_rate_ρ₂ : IsLittleOp
      (fun n ω => (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
        (η_hat n ω) S.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate : IsLittleOp
      (fun n ω => (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
          (η_hat n ω) S.η₀ : NNReal) : ℝ) *
        (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
          (η_hat n ω) S.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (σ : ℝ) (hσ_pos : 0 < σ)
    (hσ_sq : σ ^ 2 = ∫ z,
      ((1 / S.π_val) *
        aipwMomentATTFunctional S.η₀ z S.θ₀) ^ 2 ∂S.P_Z)
    (hNum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator_ATT S sample split η_hat) S.θ₀ split.foldB n) P.μ)
    (hStud_meas : ∀ n, AEMeasurable (fun ω =>
      IsAsymLinear.rescaledEstimator
        (dmlEstimator_ATT S sample split η_hat) S.θ₀ split.foldB n ω / σ) P.μ) :
    Tendsto_dist (fun n ω =>
      IsAsymLinear.rescaledEstimator
        (dmlEstimator_ATT S sample split η_hat) S.θ₀ split.foldB n ω / σ)
      (gaussianMeasure 0 1) P.μ hStud_meas := by
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  have hAL := dml_ATT_isAsymLinear S hη₀_mem h_e_lb h_overlap hA hπ_pos
    h_y2 h_y0_2 hIPW sample split hc_pos hc_lt h_split_rate η_hat
    h_in_Hε h_e_lb_hat h_mu_diff_memLp h_e_diff_memLp h_IPW_at
    h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
    h_indiv_rate_ρ₁ h_indiv_rate_ρ₂ h_product_rate
  have hψ_meas : Measurable (fun z =>
      (1 / S.π_val) * aipwMomentATTFunctional S.η₀ z S.θ₀) :=
    (measurable_aipwMomentATTFunctional S.η₀ S.θ₀).const_mul _
  have hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample
        (fun z => (1 / S.π_val) *
          aipwMomentATTFunctional S.η₀ z S.θ₀) split.foldB n) P.μ := by
    intro n
    unfold IsAsymLinear.normalizedSum
    exact ((Finset.measurable_sum _ (fun i _ =>
      hψ_meas.comp (sample.meas i))).const_mul _).aemeasurable
  have hNormal := hAL.tendsto_normal_foldB
    split hψ_meas hNum_meas hSum_meas
  rw [← hσ_sq] at hNormal
  have hScaled := Tendsto_dist.const_mul_tendsto_gaussian
    (Xn := IsAsymLinear.rescaledEstimator
      (dmlEstimator_ATT S sample split η_hat) S.θ₀ split.foldB)
    (a := fun _ : ℕ => 1 / σ) (a₀ := 1 / σ) (v := σ ^ 2)
    hNum_meas hNormal tendsto_const_nhds
  have hvar : (1 / σ) ^ 2 * σ ^ 2 = 1 := by
    field_simp [ne_of_gt hσ_pos]
  rw [hvar] at hScaled
  simpa [div_eq_mul_inv, mul_comm] using hScaled

end ATT
end Estimation
end Causalean
