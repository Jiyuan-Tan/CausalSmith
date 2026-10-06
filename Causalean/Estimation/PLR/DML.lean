/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Oracle one-step partially linear DML: asymptotic linearity and normality

Assembles two pointwise, one-shot/fold-B results for the partially linear
estimator of the structural slope `θ`, directly mirroring the AIPW back-door
development:

* `plr_oneStepOracleDML_isAsymLinear`  — the Robinson partialling-out DML estimator is
  asymptotically linear at `θ` with influence function
  `−J₀⁻¹ · ψ(η₀, ·, θ)`, derived from the abstract Chernozhukov engine
  `oneStepOracleDML_isAsymLinear_of_ae` fed with the three partially linear
  facts (`plr_meanZero`, `plr_finite_var`, `plr_remainder_bound`).
* `plr_oneStepOracleDML_tendstoNormal` — √|B(n)|-asymptotic normality of the rescaled
  estimator, obtained from the generic CLT bridge
  `IsAsymLinear.tendsto_normal_foldB`.

These statements concern one model and one sample split, scale by the fold-B
sample size, and use a population variance. They do not formalize the published
K-fold DML1/DML2 theorem, its uniform-over-model-class conclusion, estimated
variance, or confidence intervals.
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
public import Causalean.Estimation.PLR.MeanZero
public import Causalean.Estimation.PLR.RemainderBound
public import Causalean.Estimation.PLR.ScoreL2
public import Causalean.Stat.SampleSplit.PartialFoldCLT

/-! # Oracle one-step partially linear DML theorems

This file delivers pointwise asymptotic linearity and √|B|-asymptotic normality
for a one-shot, fold-B estimator of the structural slope in the partially linear
model. It composes the abstract one-shot engine with the three model-specific
analytic facts (mean zero, finite variance, and a second-order remainder) and
the generic asymptotic-linearity ⇒ normality bridge. It is not a K-fold DML1 or
DML2 limit theorem. -/

public section

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.Stat Causalean.PO
open Causalean.Estimation.OrthogonalMoments
open Filter Topology

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] [IsProbabilityMeasure P.μ]

/-- **Oracle one-step partially linear DML asymptotic-linearity theorem.**  Fix a
partially linear estimation system, an i.i.d. sample of covariate-treatment-outcome
triples, and a sample split whose evaluation-fold share [converges to a fixed
positive limit](hyp:hc_pos,h_split_rate). If [the model's integrability and
square-integrability conditions hold — the structural error, its product with the
treatment residual, the baseline-covariate term, and the treatment are integrable,
the true treatment residual is square-integrable, and the true score has finite
second moment](hyp:hU,hUV,hbX,hD,hV,hsq); [for the estimated nuisance sequence
`η_hat`, at every fold and draw the outcome- and treatment-regression errors are
square-integrable in the covariate law, with the resulting cross terms against the
structural error and the treatment residual integrable](hyp:hΔl,hΔm,hUΔm,hΔlV,hVΔm);
[the estimated score is jointly measurable, fold-A measurable, and
integrable/square-integrable at every
fold](hyp:h_m_meas,h_m_foldA,h_m_foldA_uncurry,h_m_int,h_m_sq_int); [the true residual
factors have finite fourth moments, the nuisance errors have finite fourth moments bounded
almost surely by a common nonnegative envelope, and both fourth-moment nuisance errors are
$o_p(1)$](hyp:hA_memLp,hv_memLp,B,hB,hΔl4_memLp,hΔm4_memLp,hΔl4_bound,hΔm4_bound,h_l_rate,h_m_rate);
and [the product of the two nuisance-error seminorms is
$o_p(n^{-1/2})$](hyp:h_product_rate); then [the one-step double-machine-learning
estimator of the structural slope is asymptotically linear at the true slope, with
influence function $-J_0^{-1}\psi(\eta_0,\cdot,\theta_0)$ — the
inverse-Jacobian-scaled Robinson partialling-out score at the truth](goal).

The result is obtained by feeding the abstract Chernozhukov double-machine-learning
engine the three partially linear analytic facts — the score is mean-zero at the
truth, has finite variance, and satisfies a second-order bound on its
population bias at any estimated nuisance — together with the engine's
measurability and rate bundle, all supplied by the caller exactly as in the
AIPW development. -/
theorem plr_oneStepOracleDML_isAsymLinear
    (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    -- Model-level integrability facts feeding the three PLR lemmas.
    (hU : Integrable S.U P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.toPOPartialLinearModel.resid ω) P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hD : Integrable S.factualD P.μ)
    (hV : MemLp S.resid 2 P.μ)
    (hsq : Integrable
      (fun ω => (plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀) ^ 2) P.μ)
    -- Per-`(n, ω)` second-order remainder regularity, so `plr_remainder_bound` applies at
    -- each estimated nuisance `η_hat n ω`.
    (hΔl : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X)
    (hUΔm : ∀ n ω, Integrable
      (fun ω' => S.U ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (hΔlV : ∀ n ω, Integrable
      (fun ω' => ((η_hat n ω).lFn (S.factualX ω') - S.lVal (S.factualX ω'))
        * S.resid ω') P.μ)
    (hVΔm : ∀ n ω, Integrable
      (fun ω' => S.resid ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    -- The abstract engine's measurability and rate bundle (copied verbatim from
    -- `oneStepOracleDML_isAsymLinear_of_ae` with `M := S.plrGeneralMoment`).
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
        S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × ℝ × ℝ))]
          (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
            S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z =>
        S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z =>
        (S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) ^ 2) S.P_Z)
    (hA_memLp : MemLp
      (fun z => z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) 4 S.P_Z)
    (hv_memLp : MemLp (fun z => z.2.1 - S.mVal z.1) 4 S.P_Z)
    {B : ℝ} (hB : 0 ≤ B)
    (hΔl4_memLp : ∀ n ω,
      MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X)
    (hΔm4_memLp : ∀ n ω,
      MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X)
    (hΔl4_bound : ∀ n, ∀ᵐ ω ∂P.μ,
      (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal ≤ B)
    (hΔm4_bound : ∀ n, ∀ᵐ ω ∂P.μ,
      (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal ≤ B)
    (h_l_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_m_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ) *
            ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (Causalean.Estimation.OrthogonalMoments.oneStepOracleDML
        S.plrGeneralMoment sample split η_hat)
      S.θ₀
      (fun z => -S.plrGeneralMoment.linScaleInv * plrMomentFunctional S.η₀ z S.θ₀)
      sample
      split.foldB := by
  set Crem : ℝ := 1 + |S.θ₀| with hCrem_def
  have hMZ := S.plr_meanZero hU hUV hbX hD
  have hFV := S.plr_finite_var hsq
  have hBR_at :
      ∀ n ω,
        |∫ z, plrMomentFunctional (η_hat n ω) z S.θ₀ ∂S.P_Z| ≤
          Crem * ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.η₀ : NNReal) : ℝ) *
                 ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.η₀ : NNReal) : ℝ) :=
    fun n ω =>
      S.plr_remainder_bound (η_hat n ω) hD hbX hU (hΔl n ω) (hΔm n ω) hV
        (hUΔm n ω) (hΔlV n ω) (hVΔm n ω) hUV
  have h_score_diff_rate := S.plr_score_diff_isLittleOp_one η_hat
    hA_memLp hv_memLp hB hΔl4_memLp hΔm4_memLp hΔl4_bound hΔm4_bound
    h_l_rate h_m_rate
  simpa [plrGeneralMoment] using
    (Causalean.Estimation.OrthogonalMoments.oneStepOracleDML_isAsymLinear_of_ae
      S.plrGeneralMoment hMZ hFV sample split hc_pos h_split_rate η_hat
      (Crem := Crem) (fun n => Eventually.of_forall (hBR_at n))
      h_m_meas h_m_foldA h_m_foldA_uncurry
      (fun n => Eventually.of_forall (h_m_int n))
      (fun n => Eventually.of_forall (h_m_sq_int n))
      h_score_diff_rate h_product_rate)

/-- **Oracle one-step partially linear DML asymptotic-normality theorem.**  Fix a partially linear
estimation system, an i.i.d. sample of covariate-treatment-outcome triples, and [a sample split
whose evaluation-fold share converges to a fixed positive limit](hyp:hc_pos,h_split_rate).
Suppose [the structural error, its product with the treatment residual, the baseline-covariate
term, and the treatment are integrable, the true treatment residual is square-integrable, and the
true score has finite second moment](hyp:hU,hUV,hbX,hD,hV,hsq); for the estimated nuisance
sequence `η_hat`, [the outcome- and treatment-regression errors are square-integrable in the
covariate law at every fold and draw, with the resulting cross terms against the structural error
and the treatment residual integrable](hyp:hΔl,hΔm,hUΔm,hΔlV,hVΔm); [the estimated score is
jointly measurable and measurable as a function of the nuisance-training fold alone and jointly
with the observation](hyp:h_m_meas,h_m_foldA,h_m_foldA_uncurry), and [integrable and
square-integrable at every fold and draw](hyp:h_m_int,h_m_sq_int);
[the residual factors have finite fourth moments](hyp:hA_memLp,hv_memLp),
[the nuisance errors have finite fourth moments](hyp:hΔl4_memLp,hΔm4_memLp),
[a common envelope is nonnegative](hyp:B,hB),
[that envelope bounds both fourth moments](hyp:hΔl4_bound,hΔm4_bound), and
[both fourth-moment errors are $o_p(1)$](hyp:h_l_rate,h_m_rate), implying L² score convergence;
[the product of the two nuisance-error
seminorms is $o_p(n^{-1/2})$](hyp:h_product_rate); and [the influence function,
the rescaled estimator at each `n`, and the normalized influence sum at each `n` are all
measurable](hyp:hψ_meas,hθn_meas,hSum_meas). Then [the rescaled double-machine-learning estimator
of the structural slope, recentered at the true slope and scaled by the square root of the fold-B
sample size, converges in distribution to a centered Gaussian whose variance is the second moment
of the inverse-Jacobian-scaled partialling-out score at the true regressions](goal).

This statement is pointwise in one model and one sample split, uses the fold-B
scale and population variance, and does not assert the K-fold DML1/DML2,
uniformity, estimated-variance, or confidence-interval conclusions of the
published DML theorem. The proof composes the asymptotic-linearity theorem with
the generic central-limit bridge for fold-B asymptotically linear estimators. -/
theorem plr_oneStepOracleDML_tendstoNormal
    (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    (hU : Integrable S.U P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.toPOPartialLinearModel.resid ω) P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hD : Integrable S.factualD P.μ)
    (hV : MemLp S.resid 2 P.μ)
    (hsq : Integrable
      (fun ω => (plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀) ^ 2) P.μ)
    (hΔl : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X)
    (hUΔm : ∀ n ω, Integrable
      (fun ω' => S.U ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (hΔlV : ∀ n ω, Integrable
      (fun ω' => ((η_hat n ω).lFn (S.factualX ω') - S.lVal (S.factualX ω'))
        * S.resid ω') P.μ)
    (hVΔm : ∀ n ω, Integrable
      (fun ω' => S.resid ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
        S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × ℝ × ℝ))]
          (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
            S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z =>
        S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z =>
        (S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) ^ 2) S.P_Z)
    (hA_memLp : MemLp
      (fun z => z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) 4 S.P_Z)
    (hv_memLp : MemLp (fun z => z.2.1 - S.mVal z.1) 4 S.P_Z)
    {B : ℝ} (hB : 0 ≤ B)
    (hΔl4_memLp : ∀ n ω,
      MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X)
    (hΔm4_memLp : ∀ n ω,
      MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X)
    (hΔl4_bound : ∀ n, ∀ᵐ ω ∂P.μ,
      (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal ≤ B)
    (hΔm4_bound : ∀ n, ∀ᵐ ω ∂P.μ,
      (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal ≤ B)
    (h_l_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_m_rate : IsLittleOp
      (fun n ω =>
        (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ) *
            ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hψ_meas :
      Measurable
        (fun z => -S.plrGeneralMoment.linScaleInv * plrMomentFunctional S.η₀ z S.θ₀))
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (oneStepOracleDML S.plrGeneralMoment sample split η_hat)
        S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample
        (fun z => -S.plrGeneralMoment.linScaleInv * plrMomentFunctional S.η₀ z S.θ₀)
        split.foldB n) P.μ) :
    Modes.TendstoInLaw (fun _ => P.μ)
      (IsAsymLinear.rescaledEstimator
        (oneStepOracleDML S.plrGeneralMoment sample split η_hat)
        S.θ₀ split.foldB)
      atTop (gaussianMeasure 0
        (∫ z, (-S.plrGeneralMoment.linScaleInv * plrMomentFunctional S.η₀ z S.θ₀) ^ 2
          ∂S.P_Z)) := by
  have hAL :=
    S.plr_oneStepOracleDML_isAsymLinear sample split hc_pos h_split_rate η_hat
      hU hUV hbX hD hV hsq hΔl hΔm hUΔm hΔlV hVΔm
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      hA_memLp hv_memLp hB hΔl4_memLp hΔm4_memLp hΔl4_bound hΔm4_bound
      h_l_rate h_m_rate h_product_rate
  exact hAL.tendsto_normal_foldB split hψ_meas hθn_meas hSum_meas

end PLRSystem

end PLR
end Estimation
end Causalean
