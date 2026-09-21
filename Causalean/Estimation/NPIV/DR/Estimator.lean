/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TRAE-DR evaluation-fold estimator formula

This file defines the evaluation-fold average

    θ̂ⁿ_TRAE-DR := (1/|B(n)|) Σ_{i ∈ B(n)} φ_{ĥ_n, q̂_n}(W_i),

for arbitrary random nuisance functions `(ĥ_n, q̂_n)`. The definition does
not impose fold-A training or independence conditions. Here
`φ_{h, q}(w) := m_e(w; h) + m(w; q) - q(z) h(x)` is the
pointwise pseudo-outcome from `InverseProblemSystem.phiVal`
(`Causalean/Estimation/NPIV/Setup.lean`).

This file defines only the estimator.  Asymptotic linearity is in
`AsymptoticLinear.lean`; abstract limit results and a conditional Wald
coverage transfer are in
`AsymptoticNormal.lean`.
-/

module
public import Causalean.Estimation.NPIV.Setup
public import Causalean.Stat.Sample
public import Causalean.Stat.SampleSplit

/-!
Defines estimator-level helpers and local instances for the doubly robust NPIV
development. The module exposes sample, measure, and inverse-problem-system
fields in the form used by the DR rate and limit theorems.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open MeasureTheory Causalean.Stat

/-! ## Local instance helpers

Expose the `InverseProblemSystem` measurable-space fields as scoped
instances so the rest of the `DR` namespace can use plain (non-`@`)
syntax for `Measure S.𝒲`, `Integrable`, `IIDSample`, `OneShotSplit`,
`IsAsymLinear`, and `IsProbabilityMeasure`. -/

/-- For a measurable sample space with a measure and an inverse-problem system, the measurable structure on the observation space is the measurable structure specified by that system. -/
scoped instance instMeasurableSpace_𝒲
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒲 := S.inst𝒲

/-- For a measurable sample space with a measure and an inverse-problem system, the measurable structure on the covariate space is the measurable structure specified by that system. -/
scoped instance instMeasurableSpace_𝒳
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒳 := S.inst𝒳

/-- For a measurable sample space with a measure and an inverse-problem system, the measurable structure on the instrument space is the measurable structure specified by that system. -/
scoped instance instMeasurableSpace_𝒵
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒵 := S.inst𝒵

/-- [The one-shot TRAE doubly robust estimator](goal) averages the plug-in pseudo-outcome
over the evaluation fold of [a split sample](hyp:sample,split), using [an inverse-problem
system on a measured sample space](hyp:Ω,μ,S), [its observation law](hyp:P_W), [the primal
and dual nuisance sequences](hyp:h_hat,q_hat), and [the selected sample size and
realization](hyp:n,ω).

One-shot **TRAE doubly robust estimator**:

    θ̂ⁿ_TRAE-DR := (1/|B(n)|) Σ_{i ∈ B(n)} φ_{ĥ_n, q̂_n}(W_i),

where `W_i = sample.Z i ω` and `φ_{h, q}` is `InverseProblemSystem.phiVal`.
The nuisances `ĥ_n n ω : 𝒳 → ℝ` and `q̂_n n ω : 𝒵 → ℝ` are arbitrary random
functions of `(n, ω)`. Fold-A-only training, when required by an application,
must be supplied separately. -/
noncomputable def trae_dr_estimator
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (n : ℕ) (ω : Ω) : ℝ :=
  ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω)

/-- **Estimator unfolding.** For [primal nuisance estimators `ĥ_n`, indexed by sample size and
by outcome](hyp:h_hat), paired with dual nuisance estimators `q̂_n`, an inverse-problem system,
an i.i.d. sample, and a one-shot cross-fitting split, [the one-shot TRAE doubly robust
estimator evaluated at sample size `n` and outcome `ω` equals the average, over the evaluation
fold `B(n)`, of the pointwise doubly-robust pseudo-outcome `φ_{ĥ_n,q̂_n}` computed at each
fold member's observation](goal). -/
lemma trae_dr_estimator_eq_avg_phi
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (n : ℕ) (ω : Ω) :
    trae_dr_estimator S sample split h_hat q_hat n ω
      = ((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n,
            S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω) := rfl

end DR
end NPIV
end Estimation
end Causalean
