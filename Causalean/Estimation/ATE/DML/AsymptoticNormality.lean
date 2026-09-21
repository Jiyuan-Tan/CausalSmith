/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.DML.AsymptoticLinearity

/-! # Asymptotic normality for one-shot ATE DML

Proves `dml_ATE_tendstoNormal` for the all-realizations nuisance interface by
combining asymptotic linearity with the fold-level central limit theorem. This
file owns the normal-limit wrapper, not the estimator or linearity proof.
-/

public section

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-- **Asymptotic normality of the one-shot DML ATE** (`thm:est-dml-ate-al`,
"In particular ..." clause).  Under [the back-door identification
assumptions](hyp:hA) for `S`, with [strict overlap for the true
propensity](hyp:h_overlap) and [a.e. overlap for every learner
realization](hyp:h_e_overlap), [finite second moments of the observed and
potential outcomes](hyp:h_y2,h_yd2), and a one-shot sample split whose
evaluation-fold fraction [converges to some `c` with `0 < c <
1`](hyp:hc_pos,hc_lt,h_split_rate): suppose the learners `μ̂`, `ê` are
[measurable](hyp:h_mu_meas,h_e_meas), [in `L²(P_X)` at every
realization](hyp:h_mu_memLp,h_e_memLp), [depend only on the nuisance-training
fold, marginally and jointly with the
covariate](hyp:h_mu_foldA,h_e_foldA,h_mu_uncurry_foldA,h_e_uncurry_foldA), and
[converge individually at rate `o_p(1)`](hyp:h_mu_rate,h_e_rate) with [product
rate `o_p(n^{-1/2})`](hyp:h_product_rate). These are the all-realizations
nuisance hypotheses of the direct linearity compatibility result. Given in
addition [measurability of the AIPW influence function](hyp:hψ_meas), [a.e.
measurability of the rescaled estimator at every
horizon](hyp:hθn_meas), and [a.e. measurability of the normalized influence-sum at
every horizon](hyp:hSum_meas), then [the rescaled estimator `√|B(n)| (θ̂ⁿ − θ₀)`
converges in distribution to `N(0, ∫ ψ_AIPW² dP_Z)`](goal).

Together with `|B(n)|/n → c ∈ (0,1)`, Slutsky scaling gives the
`√n`-rate form `√n (θ̂ⁿ − θ₀) ⇒ N(0, σ²/c)` (variance inflated by the
sample-splitting cost `1/c`).  That last step is left to the caller. -/
theorem dml_ATE_tendstoNormal
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ∀ᵐ x ∂S.P_X, ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hψ_meas : Measurable (S.ψ_AIPW))
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum sample (S.ψ_AIPW) split.foldB n) P.μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0 (∫ x, (S.ψ_AIPW x) ^ 2 ∂S.P_Z))
      P.μ
      hθn_meas := by
  haveI : IsProbabilityMeasure P.μ := inferInstance
  have hAL :=
    dml_ATE_isAsymLinear S hA h_overlap h_y2 h_yd2 sample split
      hc_pos hc_lt h_split_rate μ_hat e_hat h_mu_meas h_e_meas
      h_mu_memLp h_e_memLp h_e_overlap
      h_mu_foldA h_e_foldA h_mu_uncurry_foldA h_e_uncurry_foldA
      h_mu_rate h_e_rate h_product_rate
  exact hAL.tendsto_normal_foldB split hψ_meas hθn_meas hSum_meas

end ATE
end Estimation
end Causalean
