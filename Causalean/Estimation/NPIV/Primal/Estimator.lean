/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TRAE primal estimator (sup-min over candidate / critic classes)

Defines the primal Tikhonov regularized adversarial estimator interface from
`def:est-trae-primal` in
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`:

    ĥ_n ∈ argmin_{h ∈ H} sup_{f ∈ F}
            P_{A(n)} [2{m(W; f) - h(X) f(Z)} - f(Z)² + λ_n h(X)²].

Rather than formalizing `argmin-sup` as a computable choice, this file exposes

* `TRAEClasses S` — bundling the candidate / critic classes `H ⊆ Hbar`
  and `F ⊆ Qbar`;
* `innerIntegrand`, `innerObjective`, `supObjective` — the empirical
  objectives at a candidate `h`;
* `IsTRAEPrimalEstimator` — the post-hoc property the rate proof
  consumes (the empirical regularized objective at `ĥ_n` is no worse
  than at the comparison point `h*_λ`), bundled with a measurability
  condition.

This mirrors the way `Estimation/NPIV/DR/Estimator.lean` treats `ĥ_n` as an
arbitrary measurable nuisance: the rate theorem consumes the optimality
hypothesis rather than constructing the estimator.
-/

module
public import Causalean.Estimation.NPIV.Operator
public import Causalean.Stat.Sample
public import Causalean.Stat.SampleSplit

/-!
# TRAE Primal Estimator Interface

This file defines the public estimator-level interface for the primal NPIV rate
proof.  It exposes scoped measurable-space instances for the spaces stored in an
inverse-problem system, the `TRAEClasses` bundle of candidate and critic classes,
the empirical objective pieces `innerIntegrand`, `innerObjective`, and
`supObjective`, and the predicate `IsTRAEPrimalEstimator` recording membership,
empirical sup-min optimality, and joint measurability of the estimator.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat

/-! ## Local instance helpers

Mirror the helpers in `DR/Estimator.lean`: expose the
`InverseProblemSystem` measurable-space fields as scoped instances so
the rest of the `Primal` namespace can use plain (non-`@`) syntax for
`Measure S.𝒲`, `IIDSample`, `OneShotSplit`, etc. -/

/-- For an inverse-problem system, the observation space is equipped with the measurable space specified by that system.

The observation space carries the measurable space stored in the inverse
problem system. -/
scoped instance instMeasurableSpace_𝒲
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒲 := S.inst𝒲

/-- For an inverse-problem system, the covariate space is equipped with the measurable space specified by that system.

The covariate space carries the measurable space stored in the inverse
problem system. -/
scoped instance instMeasurableSpace_𝒳
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒳 := S.inst𝒳

/-- For an inverse-problem system, the instrument space is equipped with the measurable space specified by that system.

The instrument space carries the measurable space stored in the inverse
problem system. -/
scoped instance instMeasurableSpace_𝒵
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒵 := S.inst𝒵

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Candidate / critic classes -/

/-- This structure packages [a nonempty statistical candidate class for the primal
nuisance](hyp:H,H_nonempty) that [sits inside the ambient candidate set](hyp:H_subset),
together with [a nonempty statistical critic class](hyp:F,F_nonempty) that [sits inside the
ambient critic set](hyp:F_subset), for the primal Tikhonov-regularized adversarial
optimization (`def:est-trae-population-criterion`, line 139). -/
structure TRAEClasses (S : OperatorSystem Ω μ) where
  /-- Statistical candidate class for the primal nuisance. -/
  H : Set (S.𝒳 → ℝ)
  /-- Statistical critic class. -/
  F : Set (S.𝒵 → ℝ)
  /-- `H` is contained in the candidate set `Hbar`. -/
  H_subset : H ⊆ S.Hbar
  /-- `F` is contained in the candidate set `Qbar`. -/
  F_subset : F ⊆ S.Qbar
  /-- The candidate class is non-empty. -/
  H_nonempty : H.Nonempty
  /-- The critic class is non-empty. -/
  F_nonempty : F.Nonempty

/-! ## Empirical objectives -/

/-- [The empirical integrand](goal) for [an NPIV operator system](hyp:S), [regularization
level](hyp:lambda), [candidate](hyp:h), and [critic](hyp:f) at [an observation](hyp:w) is
`2(m(w;f) - h(x)f(z)) - f(z)² + λh(x)²`, with the system's covariate and instrument.

The fold-`A` empirical pointwise integrand at `(h, f)` and observation
`w : 𝒲`:

    2 (m(w; f) − h(x) f(z)) − f(z)² + λ h(x)²,    where (x, z) := (xOf w, zOf w).

This is the bracket inside `def:est-trae-primal` (line 156). -/
noncomputable def innerIntegrand
    (S : OperatorSystem Ω μ) (lambda : ℝ)
    (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ) (w : S.𝒲) : ℝ :=
  2 * (S.m w f - h (S.xOf w) * f (S.zOf w))
    - f (S.zOf w) ^ 2 + lambda * h (S.xOf w) ^ 2

/-- [The fold-A inner objective](goal) averages the empirical integrand for [an NPIV
operator system](hyp:S), [sample and split](hyp:sample,split), [regularization level,
candidate, and critic](hyp:lambda,h,f) over the nuisance fold selected by [the sample-size
index and realization](hyp:n,ω).

The fold-`A` empirical inner objective at a candidate `h` and critic
`f`: the average of `innerIntegrand` over the nuisance fold `A(n)`. -/
noncomputable def innerObjective
    (S : OperatorSystem Ω μ)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ((split.foldA n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldA n,
      innerIntegrand S lambda h f (sample.Z i ω)

/-- [The TRAE primal sup-min objective](goal) takes the supremum of the fold-A inner
objective over [the critic class](hyp:TC), for [an NPIV operator system](hyp:S), [sample and
split](hyp:sample,split), [regularization level and candidate](hyp:lambda,h), and [the chosen
sample-size index and realization](hyp:n,ω).

The TRAE primal sup-min objective:
    `sup_{f ∈ TC.F} P_{A(n)} [innerIntegrand λ h f W]`. -/
noncomputable def supObjective
    (S : OperatorSystem Ω μ) (TC : TRAEClasses S)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ f ∈ TC.F, innerObjective S sample split lambda h f n ω

/-! ## TRAE primal estimator predicate

We expose the *post-hoc property* the rate theorem actually consumes: at
the empirical optimum `ĥ_n`, the sup-objective is no worse than at any
realized comparison point `h*_λ ∈ H`.  Plus a measurability-in-`ω`
condition for downstream probability arguments. -/

/-- An estimator, indexed by sample size and randomness, **is a TRAE primal estimator**
relative to a nuisance fold when, at every sample size and realization, it [belongs to the
statistical candidate class](hyp:mem_H), [attains an empirical sup-min objective on that fold no
worse than at any other candidate in the class](hyp:opt), and [is jointly measurable in the
randomness and the covariate argument](hyp:measurable).

Concretely:

* (`mem_H`) for every `(n, ω)`, the candidate `h_hat n ω` lies in
  `TC.H ⊆ Hbar`;
* (`opt`) for every `(n, ω)` and every `h' ∈ TC.H`, the empirical
  sup-objective at `h_hat n ω` is no worse than at `h'`;
* (`measurable`) for every `n`, the random function `ω ↦ h_hat n ω` is
  jointly measurable in `(ω, x)` (encoded as measurability of
  `(ω, x) ↦ h_hat n ω x`).  The exact joint-measurability shape may be
  refined when the rate proof needs it. -/
structure IsTRAEPrimalEstimator
    (S : OperatorSystem Ω μ) (TC : TRAEClasses S)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (lambda : ℝ)
    (h_hat : ℕ → Ω → S.𝒳 → ℝ) : Prop where
  /-- Membership of the empirical optimizer in the statistical class `H`. -/
  mem_H : ∀ n ω, h_hat n ω ∈ TC.H
  /-- Empirical sup-min optimality on fold `A(n)`. -/
  opt :
    ∀ n ω, ∀ h' ∈ TC.H,
      supObjective S TC sample split lambda (h_hat n ω) n ω
        ≤ supObjective S TC sample split lambda h' n ω
  /-- Joint measurability of `(ω, x) ↦ h_hat n ω x`. -/
  measurable :
    ∀ n, Measurable (fun p : Ω × S.𝒳 => h_hat n p.1 p.2)

/-- For [an NPIV operator system](hyp:S), [candidate and critic classes](hyp:TC),
[an independent sample](hyp:sample), [a one-shot split](hyp:split), [a regularization
sequence](hyp:lambda), and [an estimator sequence](hyp:h_hat), the estimator is a
sample-size-dependent TRAE estimator when its [candidate belongs to the statistical
class](hyp:mem_H), [minimizes the empirical objective formed with `lambda n` at each
index](hyp:opt), and [is jointly measurable](hyp:measurable).

This is the standard interface for a vanishing Tikhonov sequence. -/
structure IsTRAEPrimalEstimatorSequence
    (S : OperatorSystem Ω μ) (TC : TRAEClasses S)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (lambda : ℕ → ℝ)
    (h_hat : ℕ → Ω → S.𝒳 → ℝ) : Prop where
  /-- Membership of the empirical optimizer in the statistical class `H`. -/
  mem_H : ∀ n ω, h_hat n ω ∈ TC.H
  /-- Empirical sup-min optimality at index `n`, using `lambda n`. -/
  opt :
    ∀ n ω, ∀ h' ∈ TC.H,
      supObjective S TC sample split (lambda n) (h_hat n ω) n ω
        ≤ supObjective S TC sample split (lambda n) h' n ω
  /-- Joint measurability of `(omega, x) ↦ h_hat n omega x`. -/
  measurable :
    ∀ n, Measurable (fun p : Ω × S.𝒳 => h_hat n p.1 p.2)

end Primal
end NPIV
end Estimation
end Causalean
