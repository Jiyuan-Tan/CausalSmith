/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.DML.AsymptoticLinearity

/-! # Asymptotic normality for one-shot ATE DML

Proves `dml_ATE_tendstoNormal_on_highProbEvent`, the normal limit when the learner
square-integrability and overlap conditions hold on events of probability tending to
one, by combining good-set asymptotic linearity with the fold-level central limit
theorem. `dml_ATE_tendstoNormal` is its corollary for learners satisfying those
conditions at every realization. This file owns the normal-limit wrappers, not the
estimator or linearity proof.
-/

public section

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open BackdoorEstimationSystem
open scoped ENNReal

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-- **Asymptotic normality of the one-shot DML estimator of the average treatment effect, with
learner conditions on events of probability tending to one.** For [a back-door estimation
system](hyp:S) satisfying [the back-door identification assumptions](hyp:hA), with [an overlap
threshold ε](hyp:ε) such that [0 < ε ≤ 1/2 and the true propensity score lies between ε and
1 − ε almost surely](hyp:h_overlap), [a square-integrable observed outcome](hyp:h_y2) and [square-integrable
potential outcomes](hyp:h_yd2), let [an i.i.d. sample](hyp:sample) be [split once into a training
fold and an evaluation fold](hyp:split) whose [evaluation-fold share converges](hyp:h_split_rate)
to [a limit c](hyp:c) that is [positive](hyp:hc_pos), and let [μ̂_n and ê_n be the
outcome-regression and propensity learners](hyp:μ_hat,e_hat). Suppose there are [events
G_n](hyp:goodSet) whose [complements have probability at most Δ_n](hyp:hfail) for [a sequence
Δ_n](hyp:Δ) that [tends to zero](hyp:hΔ). Assume [(ω, x) ↦ μ̂_n(ω)(a, x) is jointly measurable
for each arm a](hyp:h_mu_meas) and [so is (ω, x) ↦ ê_n(ω)(x)](hyp:h_e_meas); on G_n [each
μ̂_n(a, ·) is square-integrable under the covariate law](hyp:h_mu_memLp), [ê_n is
square-integrable under the covariate law](hyp:h_e_memLp) and [ε ≤ ê_n ≤ 1 − ε almost everywhere
under the covariate law](hyp:h_e_overlap); [μ̂_n](hyp:h_mu_uncurry_foldA) and
[ê_n](hyp:h_e_uncurry_foldA) are measurable with respect to the product of the σ-algebra generated
by the training-fold observations and the covariate σ-algebra; [for each arm the L² error of μ̂_n
under the covariate law is o_p(1)](hyp:h_mu_rate), [the L² error of ê_n is o_p(1)](hyp:h_e_rate),
and [for each arm the product of these two L² errors is o_p(n^(−1/2))](hyp:h_product_rate). Given
in addition [measurability of the augmented inverse-probability-weighted influence
function](hyp:hψ_meas), [almost-everywhere measurability of the rescaled estimator at every sample
size](hyp:hθn_meas), and [almost-everywhere measurability of the normalized influence-function sum
at every sample size](hyp:hSum_meas), then [√|B(n)|·(θ̂_n − θ₀), where B(n) is the
evaluation fold, converges in distribution to the centered normal law whose variance is the second
moment of the augmented inverse-probability-weighted influence function under the observed-data
law](goal).

The learner square-integrability and overlap conditions are required only on the events `G_n`,
whose probability tends to one; outside `G_n` the learners are unrestricted. The proof combines
`dml_ATE_isAsymLinear_of_goodSet` with the fold-level central limit theorem and Slutsky's lemma.
Together with `|B(n)|/n → c > 0`, Slutsky scaling gives the `√n`-rate form
`√n (θ̂ⁿ − θ₀) ⇒ N(0, σ²/c)`; that last step is left to the caller. -/
theorem dml_ATE_tendstoNormal_on_highProbEvent
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (goodSet : ℕ → Set P.Ω)
    (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, P.μ (goodSet n)ᶜ ≤ Δ n)
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω, ω ∈ goodSet n → ∀ a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, ω ∈ goodSet n → MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ω ∈ goodSet n → ∀ᵐ x ∂S.P_X,
        ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
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
    Modes.TendstoInLaw (fun _ : ℕ => P.μ) (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB) atTop
            (gaussianMeasure 0 (∫ x, (S.ψ_AIPW x) ^ 2 ∂S.P_Z)) := by
  have hAL :=
    dml_ATE_isAsymLinear_of_goodSet S hA h_overlap h_y2 h_yd2 sample split
      hc_pos h_split_rate μ_hat e_hat goodSet Δ hΔ hfail h_mu_meas h_e_meas
      h_mu_memLp h_e_memLp h_e_overlap
      h_mu_uncurry_foldA h_e_uncurry_foldA
      h_mu_rate h_e_rate h_product_rate
  exact hAL.tendsto_normal_foldB split hψ_meas hθn_meas hSum_meas

/-- **Asymptotic normality of the one-shot DML estimator of the average treatment effect.** Under [the
back-door identification assumptions](hyp:hA), with [strict overlap for the true propensity
score](hyp:h_overlap) and [the same overlap bounds holding almost everywhere under the covariate
law for every realization of the propensity learner](hyp:h_e_overlap), [finite second moments of
the observed and potential outcomes](hyp:h_y2,h_yd2), and a one-shot sample split whose
evaluation-fold share [converges to a positive limit c](hyp:hc_pos,h_split_rate): suppose the
outcome-regression and propensity learners μ̂_n, ê_n are [jointly measurable in the realization
and the covariate](hyp:h_mu_meas,h_e_meas), [square-integrable under the covariate law at every
realization](hyp:h_mu_memLp,h_e_memLp), [measurable with respect to the product of the σ-algebra
generated by the training-fold observations and the covariate
σ-algebra](hyp:h_mu_uncurry_foldA,h_e_uncurry_foldA), and [have L² errors under the covariate law
that are each o_p(1)](hyp:h_mu_rate,h_e_rate), with [the product of the outcome-regression and
propensity L² errors being o_p(n^(−1/2)) for each arm](hyp:h_product_rate). These nuisance
conditions are imposed at every realization of the learners, not only on a high-probability event.
Given in addition [measurability of the augmented inverse-probability-weighted influence
function](hyp:hψ_meas), [almost-everywhere measurability of the rescaled estimator at every sample
size](hyp:hθn_meas), and [almost-everywhere measurability of the normalized influence-function sum
at every sample size](hyp:hSum_meas), then [√|B(n)|·(θ̂_n − θ₀), where B(n) is the evaluation
fold, converges in distribution to the centered normal law whose variance is the second moment of
the augmented inverse-probability-weighted influence function under the observed-data law](goal).

Together with `|B(n)|/n → c > 0`, Slutsky scaling gives the
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
    {c : ℝ} (hc_pos : 0 < c)
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
    Modes.TendstoInLaw (fun _ : ℕ => P.μ) (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB) atTop
            (gaussianMeasure 0 (∫ x, (S.ψ_AIPW x) ^ 2 ∂S.P_Z)) := by
  exact dml_ATE_tendstoNormal_on_highProbEvent S hA h_overlap h_y2 h_yd2 sample split
    hc_pos h_split_rate μ_hat e_hat (fun _ => Set.univ) (fun _ => 0)
    tendsto_const_nhds (by simp) h_mu_meas h_e_meas
    (fun n ω _ a => h_mu_memLp n ω a) (fun n ω _ => h_e_memLp n ω)
    (fun n ω _ => h_e_overlap n ω)
    h_mu_uncurry_foldA h_e_uncurry_foldA
    h_mu_rate h_e_rate h_product_rate hψ_meas hθn_meas hSum_meas

end ATE
end Estimation
end Causalean
