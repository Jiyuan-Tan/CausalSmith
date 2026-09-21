/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.CausalApplication.RegressionBridge
public import Causalean.Estimation.ATE.Score.AIPWMoment

/-! # Conditional-mean candidates for causal nuisance workflows

Using the conditional-expectation bridge (`RegressionBridge`), this file gives generic
aliases showing that a candidate satisfying `IsResidualOrthogonal` agrees almost everywhere
with the conditional expectation of an arbitrary real response. These aliases acquire an
outcome-regression or propensity interpretation only after the supplied law is separately
shown to be an arm-specific outcome law or a covariate--treatment-indicator law. No concrete
learner is shown here to satisfy `IsResidualOrthogonal`. `mlNuisanceVec` packages candidates
into the `Estimation.ATE.NuisanceVec` expected by the AIPW moment.
-/

@[expose] public section

namespace Causalean.ML.CausalApplication

open MeasureTheory

variable {γ : Type*} [MeasurableSpace γ]

/-- **Generic conditional-mean identification.** [A measurable candidate](hyp:m,hm)
[equals almost everywhere the response conditional mean given covariates](goal) under
[a finite covariate--real-response law](hyp:Pd) on [the measurable covariate space](hyp:γ),
provided [the response is integrable](hyp:hY),
[the candidate evaluated at the covariates is integrable](hyp:hmint), and
[every admissible covariate function is orthogonal to the residual](hyp:hproj).

This statement does not show that `Pd` is an arm-specific outcome law. -/
theorem response_condExp_ae_eq_of_isResidualOrthogonal
    (Pd : Measure (γ × ℝ)) [IsFiniteMeasure Pd] {m : γ → ℝ} (hm : Measurable m)
    (hY : Integrable (fun z => z.2) Pd) (hmint : Integrable (fun z => m z.1) Pd)
    (hproj : Causalean.ML.IsResidualOrthogonal Pd m) :
    (fun z => m z.1) =ᵐ[Pd] (Pd[fun z => z.2 | covarSigma (X := γ)]) :=
  condExp_of_isResidualOrthogonal Pd hm hY hmint hproj

/-- **Generic auxiliary-response identification.** [A measurable candidate](hyp:e,he)
[equals almost everywhere the auxiliary response conditional mean given covariates](goal)
under [a finite covariate--real-response law](hyp:Pe) on
[the measurable covariate space](hyp:γ), provided [the response is integrable](hyp:hD),
[the candidate evaluated at the covariates is integrable](hyp:heint), and
[every admissible covariate function is orthogonal to the residual](hyp:hproj).

This becomes a propensity statement only when `Pe` is separately shown to be the law of a
covariate and a treatment indicator. -/
theorem auxiliaryResponse_condExp_ae_eq_of_isResidualOrthogonal
    (Pe : Measure (γ × ℝ)) [IsFiniteMeasure Pe] {e : γ → ℝ} (he : Measurable e)
    (hD : Integrable (fun z => z.2) Pe) (heint : Integrable (fun z => e z.1) Pe)
    (hproj : Causalean.ML.IsResidualOrthogonal Pe e) :
    (fun z => e z.1) =ᵐ[Pe] (Pe[fun z => z.2 | covarSigma (X := γ)]) :=
  condExp_of_isResidualOrthogonal Pe he hD heint hproj

/-- [The machine-learning nuisance vector](goal) packages supplied estimates for AIPW: it stores
[the treatment-indexed outcome regressions](hyp:μ_fn) [as its outcome component](step:1),
[the propensity function](hyp:e_fn) [as its propensity component](step:2),
[the outcome measurability certificates](hyp:hμ) [in their evidence field](step:3), and
[the propensity measurability certificate](hyp:he) [in its evidence field](step:4), all on
[the measurable covariate space](hyp:γ).

This packages the nuisance functions consumed by the augmented inverse-probability-weighted
estimator. -/
noncomputable def mlNuisanceVec
    (μ_fn : Bool → γ → ℝ) (e_fn : γ → ℝ)
    (hμ : ∀ b, Measurable (μ_fn b)) (he : Measurable e_fn) :
    Causalean.Estimation.ATE.NuisanceVec γ where
  μ_fn := μ_fn
  e_fn := e_fn
  μ_meas := hμ
  e_meas := he

end Causalean.ML.CausalApplication
