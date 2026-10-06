/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Partially linear model under the backdoor PO framework (continuous treatment)

This file sets up the partially linear regression (PLR) model as a causal model
inside the potential-outcome framework, with a **real-valued (continuous)
treatment** `D ∈ ℝ`.  It parallels `POBackdoorSystem` (binary treatment) in
`PO/ID/Exact/ATE.lean`, swapping the treatment's value space `Bool → ℝ`.

* `POPartialLinearSystem` — the bare PO substrate: a real treatment node `D`, a
  real outcome node `Y`, a covariate variable `X`, plus the value-space equivs
  and the distinctness of the three nodes.  Derived: `YofD d` (the potential
  outcome `Y(d)`), the factual `D/Y/X`, and the σ-algebras `σ(X)`, `σ(X,D)`.
* `POPartialLinearModel` — adds the *homogeneous linear dose-response* structural
  restriction `Y(d) = b(X) + θ·d + U`, the standard backdoor assumption stated in
  conditional-mean form `E[U | σ(X,D)] = 0`, and consistency `Y = Y(D)`.
* `factualY_eq` — the observed-data form `Y = b(X) + θ·D + U`.
* `causal_homogeneity` — the causal reading `Y(d) − Y(d') = θ·(d − d')`.
-/

module
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ConditionalExpectation

/-! # Partially Linear Model Setup

This file provides the potential-outcome substrate for the partially linear
model with a real-valued treatment. `POPartialLinearSystem` records the
treatment, outcome, and covariate nodes; packages them as `dVar`, `yVar`, and
`xVar`; defines potential outcomes `YofD`, factual maps, and the sigma-algebras
`sigmaX` and `sigmaXD`; and proves the measurability and inclusion lemmas used
by the identification proof.

`POPartialLinearModel` adds the homogeneous structural restriction
`Y(d) = b(X) + theta * d + U`, a conditional-mean backdoor assumption, and
consistency. Its two exported consequences are `factualY_eq`, the observed-data
regression form, and `causal_homogeneity`, the constant per-unit causal effect
identity. -/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- **Continuous-treatment backdoor subsystem.** Inside a potential-outcome system, this bundles
[a real-valued treatment node `D`](hyp:D,hDreal), [a real-valued outcome node `Y`](hyp:Y,hYreal),
and [a covariate variable `X` taking values in an arbitrary measurable space](hyp:Xvar), subject
to [the treatment, outcome, and covariate being pairwise distinct](hyp:hDY,hDX,hYX). This mirrors
the binary backdoor subsystem but the treatment now ranges over the real line, as required by the
partially linear model `Y = g(X) + θ·D + noise`. -/
structure POPartialLinearSystem (P : POSystem) (γ : Type*) [MeasurableSpace γ] where
  /-- The treatment node. -/
  D : P.V
  /-- The outcome node. -/
  Y : P.V
  /-- The covariate variable, valued in the covariate space. -/
  Xvar : POVar P γ
  /-- The treatment node's value space is the real line. -/
  hDreal : P.X D ≃ᵐ ℝ
  /-- The outcome node's value space is the real line. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- Treatment and outcome are distinct nodes. -/
  hDY : D ≠ Y
  /-- Treatment and covariate are distinct nodes. -/
  hDX : D ≠ Xvar.v
  /-- Outcome and covariate are distinct nodes. -/
  hYX : Y ≠ Xvar.v

namespace POPartialLinearSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POPartialLinearSystem P γ)

/-- The [continuous treatment variable](goal) in [a partially linear potential-outcome
system](hyp:S) [represents dose on the real line](step:1), within [the ambient
potential-outcome population](hyp:P) and [covariate space](hyp:γ). -/
def dVar : POVar P ℝ := ⟨S.D, S.hDreal⟩
/-- The [real-valued outcome variable](goal) in [a partially linear potential-outcome
system](hyp:S) [is the response modeled as baseline plus a linear dose effect and
error](step:1), within [the ambient population](hyp:P) and [covariate space](hyp:γ). -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩
/-- The [adjustment covariate variable](goal) in [a partially linear
potential-outcome system](hyp:S) [retains its original measurable value space](step:1)
inside [the ambient population](hyp:P) and [covariate space](hyp:γ). -/
def xVar : POVar P γ := S.Xvar

/-- The [dose-response potential outcome](goal) in [a partially linear
system](hyp:S) [records each unit's response if treatment were set to the selected
dose](step:1); [the real-valued dose](hyp:d) varies continuously in [the ambient
population](hyp:P) with [covariates](hyp:γ). -/
noncomputable def YofD (d : ℝ) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d
/-- The [observed treatment dose](goal) in [a partially linear system](hyp:S)
[records each unit's realized continuous treatment](step:1) in [the ambient
population](hyp:P) with [covariates](hyp:γ). -/
noncomputable def factualD : P.Ω → ℝ := S.dVar.factual
/-- The [observed outcome](goal) in [a partially linear system](hyp:S) [records each
unit's realized response](step:1) in [the ambient population](hyp:P) with
[covariates](hyp:γ). -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual
/-- The [observed covariate](goal) in [a partially linear system](hyp:S) [records each
unit's realized adjustment value](step:1) in [the ambient population](hyp:P) and
[covariate space](hyp:γ). -/
noncomputable def factualX : P.Ω → γ := S.xVar.factual

/-- In [a partially linear system](hyp:S), [the potential outcome at a fixed
dose](hyp:d) is [measurable, so dose-specific means and conditional means are
well-defined](goal). -/
@[fun_prop]
lemma measurable_YofD (d : ℝ) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d
/-- [The realized dose in a partially linear system](hyp:S) is [measurable, so it can
enter the observed treatment–covariate information set](goal). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- [The observed response in a partially linear system](hyp:S) is [measurable, so its
conditional regression is well-defined](goal). -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual
/-- [The observed covariate in a partially linear system](hyp:S) is [measurable, so it
can generate the adjustment information set](goal). -/
@[fun_prop]
lemma measurable_factualX : Measurable S.factualX := S.xVar.measurable_factual

/-- The [covariate information set](goal) in [a partially linear system](hyp:S) [is
generated by the observed adjustment covariate](step:1) in [the ambient
population](hyp:P) with [covariate space](hyp:γ). -/
noncomputable def sigmaX : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.factualX inferInstance

/-- [The covariate information set in a partially linear system](hyp:S) is [contained in
the full observable σ-algebra](goal), so covariate-measurable quantities are also valid
random variables on the population. -/
lemma sigmaX_le : S.sigmaX ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.measurable_factualX.comap_le

/-- [The observed covariate in a partially linear system](hyp:S) is [measurable using
only the information it generates](goal), which licenses conditioning on covariates. -/
@[fun_prop]
lemma measurable_factualX_sigmaX : Measurable[S.sigmaX] S.factualX :=
  comap_measurable S.factualX

/-- The [observed covariate–dose state](goal) in [a partially linear system](hyp:S)
[pairs each unit's covariate with its realized treatment dose](step:1) in [the ambient
population](hyp:P) and [covariate space](hyp:γ). -/
noncomputable def factualXD : P.Ω → γ × ℝ :=
  fun ω => (S.factualX ω, S.factualD ω)

/-- [The observed covariate–dose state in a partially linear system](hyp:S) is
[measurable, so it can index the backdoor conditional mean](goal). -/
@[fun_prop]
lemma measurable_factualXD : Measurable S.factualXD :=
  S.measurable_factualX.prodMk S.measurable_factualD

/-- The [joint covariate–treatment information set](goal) in [a partially linear
system](hyp:S) [is generated by observed covariates and the realized dose](step:1), in
[the ambient population](hyp:P) with [covariate space](hyp:γ); this is the information
set on which the structural error must have mean zero. -/
noncomputable def sigmaXD : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.factualXD inferInstance

/-- [The covariate–treatment information set in a partially linear system](hyp:S) is
[contained in the full observable σ-algebra](goal), so conditioning on both variables is
well-defined. -/
lemma sigmaXD_le : S.sigmaXD ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.measurable_factualXD.comap_le

/-- [The observed covariate–dose state in a partially linear system](hyp:S) is
[measurable using only its jointly generated information](goal). -/
@[fun_prop]
lemma measurable_factualXD_sigmaXD : Measurable[S.sigmaXD] S.factualXD :=
  comap_measurable S.factualXD

/-- [The observed covariate in a partially linear system](hyp:S) is [available in the
joint covariate–treatment information set](goal). -/
@[fun_prop]
lemma measurable_factualX_sigmaXD : Measurable[S.sigmaXD] S.factualX :=
  measurable_fst.comp (comap_measurable S.factualXD)

/-- [The realized dose in a partially linear system](hyp:S) is [available in the joint
covariate–treatment information set](goal). -/
@[fun_prop]
lemma measurable_factualD_sigmaXD : Measurable[S.sigmaXD] S.factualD :=
  measurable_snd.comp (comap_measurable S.factualXD)

/-- [The covariate information set in a partially linear system](hyp:S) is [coarser
than the joint covariate–treatment information set](goal), enabling the conditional-
expectation tower used for partialling out. -/
lemma sigmaX_le_sigmaXD : S.sigmaX ≤ S.sigmaXD := by
  have h : S.factualX = Prod.fst ∘ S.factualXD := rfl
  unfold sigmaX sigmaXD
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le

end POPartialLinearSystem

/-- **Partially linear model under the backdoor PO framework.** On top of the PO substrate, this
bundles [a measurable covariate function `b` giving the nonparametric baseline](hyp:b,b_meas), [a
homogeneous per-unit treatment effect `θ`](hyp:θ), [a measurable structural error term
`U`](hyp:U,U_meas), the structural restriction that [every unit's dose-response is the straight
line `Y(d) = b(X) + θ·d + U` with the same slope for everyone](hyp:structural), [the standard
backdoor (unconfoundedness) assumption that the structural error has zero mean conditional on the
observed covariate and treatment](hyp:backdoor), and [consistency: the observed outcome is the
potential outcome at the realized treatment](hyp:consistency). -/
structure POPartialLinearModel (P : POSystem) (γ : Type*) [MeasurableSpace γ]
    extends POPartialLinearSystem P γ where
  /-- Consistency (SUTVA): the observed outcome equals the potential outcome of
  the realized treatment. -/
  consistency : P.Consistency
  /-- The covariate part `b(x)` of the structural dose-response (the nonparametric
  baseline `g(X)`). -/
  b : γ → ℝ
  /-- The covariate part is measurable. -/
  b_meas : Measurable b
  /-- The homogeneous (constant across units) per-unit treatment effect — the
  causal parameter the model is about. -/
  θ : ℝ
  /-- The structural error term. -/
  U : P.Ω → ℝ
  /-- The structural error is measurable. -/
  U_meas : Measurable U
  /-- Homogeneous linear dose-response: for almost every unit, the potential
  outcome is the straight line `b(X) + θ·d + U` in the dose `d`, simultaneously
  for all doses. -/
  structural : ∀ᵐ ω ∂P.μ, ∀ d : ℝ,
      toPOPartialLinearSystem.YofD d ω
        = b (toPOPartialLinearSystem.factualX ω) + θ * d + U ω
  /-- Backdoor unconfoundedness in conditional-mean form: the structural error
  has zero mean given the observed covariate and treatment.  This is the
  operative content of the standard backdoor assumption `U ⊥ D | σ(X)` together
  with `E[U | σ(X)] = 0`. -/
  backdoor :
    P.μ[U | toPOPartialLinearSystem.sigmaXD] =ᵐ[P.μ] 0

namespace POPartialLinearModel

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (M : POPartialLinearModel P γ)

/-- The observed-data form of the structural model: almost surely
`Y = b(X) + θ·D + U`.  Obtained from the homogeneous dose-response evaluated at
the realized treatment, using consistency `Y = Y(D)`. -/
lemma factualY_eq :
    M.factualY =ᵐ[P.μ]
      fun ω => M.b (M.factualX ω) + M.θ * M.factualD ω + M.U ω := by
  filter_upwards [M.structural] with ω hω
  have hcons :
      M.yVar.factual ω = M.yVar.cfUnder M.dVar (M.dVar.factual ω) ω :=
    POVar.factual_eq_cfUnder_self_selected M.consistency M.yVar M.dVar
      (Ne.symm M.hDY) ω
  have hstr := hω (M.factualD ω)
  simpa [POPartialLinearSystem.factualY, POPartialLinearSystem.YofD,
    POPartialLinearSystem.factualD, POPartialLinearSystem.factualX] using
    hcons.trans hstr

/-- **Causal reading of `θ`.** [Almost surely, for every pair of dose levels, the
difference of the corresponding potential outcomes equals the slope `θ` times the
difference of the doses](goal), so `θ` is the constant per-unit causal effect of
the treatment. -/
lemma causal_homogeneity :
    ∀ᵐ ω ∂P.μ, ∀ d d' : ℝ,
      M.YofD d ω - M.YofD d' ω = M.θ * (d - d') := by
  filter_upwards [M.structural] with ω hω
  intro d d'
  rw [hω d, hω d']
  ring

end POPartialLinearModel

end PO
end Causalean
