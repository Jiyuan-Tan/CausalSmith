/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# NPIV / TRAE setup: linear inverse-problem functional system

This file provides the substrate for the non-iterated Tikhonov regularized
adversarial estimator (TRAE) of Bennett, Kallus, Mao, Newey, Syrgkanis, and
Uehara (2023). The target is a scalar linear functional of a primal solution
to a linear inverse problem; the main algebraic object is a doubly
robust score built from the primal solution and from the solution of a dual
inverse problem.

Mirrors the following definitions from
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`:

* `def:est-trae-system` — the linear inverse-problem functional system.
* `def:est-trae-dual-solution` — the dual solution `q₀`.
* `def:est-trae-dr-functional` — the doubly-robust functional `Θ` and its
  pointwise score `φ_{h,q}`.

The candidate sets `Hbar, Qbar` are kept as plain sets of ℝ-valued functions
closed under subtraction. No topological closedness or minimum-norm property
is recorded here. Later operator-system files add an ambient `Lp` formulation;
this setup layer records only the moment-equation contract and the linearity
needed for the mixed-bias proof.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory

/-! ## Linear inverse-problem functional system -/

/-- A **linear inverse-problem functional system** packages [an observation space together with
measurable treatment-side and instrument-side covariate projections of the observed
data](hyp:𝒲,𝒳,𝒵,W,meas_W,xOf,zOf,meas_xOf,meas_zOf), [measurable candidate sets for the
primal and dual nuisances, each closed under
subtraction](hyp:Hbar,Qbar,meas_of_Hbar,meas_of_Qbar,Hbar_sub,Qbar_sub), [observation-level moment
maps that are linear in their nuisance argument, jointly measurable and integrable against every
candidate](hyp:m,m_e,m_sub,m_e_sub,measurable_m,measurable_m_e,integrable_m,integrable_m_e), whose
[cross product `q(Z)h(X)` is integrable as well](hyp:integrable_qh), and [a primal nuisance in the
candidate set satisfying the inverse-problem moment equation against every dual
candidate](hyp:h₀,h₀_mem,primal_moment) (`def:est-trae-system`).

The structure carries:

* an observation space `𝒲` and covariate components `𝒳`, `𝒵` together with
  the random variables `W, X, Z` on `Ω`;
* candidate sets `Hbar ⊆ (𝒳 → ℝ)` and `Qbar ⊆ (𝒵 → ℝ)` for the primal and dual
  nuisances; closure under subtraction is the only algebraic property recorded
  at this setup layer;
* observation-level moment maps `m(W; q)` and `m_e(W; h)`, linear in their
  nuisance argument;
* a designated primal nuisance `h₀ ∈ Hbar` satisfying the combined inverse-problem
  moment `E[m(W; q)] = E[h₀(X) q(Z)]` for every `q ∈ Qbar`.

The structure does not assert that `h₀` is the minimum-norm solution among
all functions satisfying the moment equation.

Measurability and integrability obligations are recorded as fields so the
mixed-bias identity in `MixedBias.lean` can use linearity-of-integral on
`Hbar - Hbar` and `Qbar - Qbar`. -/
structure InverseProblemSystem
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Observation type. -/
  𝒲 : Type*
  /-- "Action" / treatment-side covariate type used by `Hbar`-side functions. -/
  𝒳 : Type*
  /-- Instrument-side covariate type used by `Qbar`-side functions. -/
  𝒵 : Type*
  inst𝒲 : MeasurableSpace 𝒲
  inst𝒳 : MeasurableSpace 𝒳
  inst𝒵 : MeasurableSpace 𝒵
  /-- Observed data point. -/
  W : Ω → 𝒲
  meas_W : @Measurable Ω 𝒲 _ inst𝒲 W
  /-- Treatment-side projection from `𝒲` to `𝒳`. -/
  xOf : 𝒲 → 𝒳
  /-- Instrument-side projection from `𝒲` to `𝒵`. -/
  zOf : 𝒲 → 𝒵
  meas_xOf : @Measurable 𝒲 𝒳 inst𝒲 inst𝒳 xOf
  meas_zOf : @Measurable 𝒲 𝒵 inst𝒲 inst𝒵 zOf
  /-- Candidate set for the primal nuisance (`Hbar ⊆ L²(P_X)` in the
  TeX; here it is a plain set of measurable ℝ-valued functions, without a
  topological-closedness field). -/
  Hbar : Set (𝒳 → ℝ)
  /-- Candidate set for the dual nuisance (`Qbar ⊆ L²(P_Z)` in the
  TeX; here it is a plain set of measurable ℝ-valued functions, without a
  topological-closedness field). -/
  Qbar : Set (𝒵 → ℝ)
  meas_of_Hbar : ∀ h ∈ Hbar, Measurable h
  meas_of_Qbar : ∀ q ∈ Qbar, Measurable q
  /-- Closure under subtraction (the only algebraic property the mixed-bias
  proof needs; standing in for the closed-linear-subspace assumption). -/
  Hbar_sub : ∀ h₁ ∈ Hbar, ∀ h₂ ∈ Hbar, (fun x => h₁ x - h₂ x) ∈ Hbar
  Qbar_sub : ∀ q₁ ∈ Qbar, ∀ q₂ ∈ Qbar, (fun z => q₁ z - q₂ z) ∈ Qbar
  /-- Observation-level moment map `m(W; q)`, linear in the dual nuisance
  argument `q`. -/
  m   : 𝒲 → (𝒵 → ℝ) → ℝ
  /-- Observation-level moment map `m_e(W; h)`, linear in the primal
  nuisance argument `h`. -/
  m_e : 𝒲 → (𝒳 → ℝ) → ℝ
  /-- Linearity of `m` over subtraction in the dual argument. -/
  m_sub :
    ∀ (w : 𝒲) (q₁ q₂ : 𝒵 → ℝ),
      m w (fun z => q₁ z - q₂ z) = m w q₁ - m w q₂
  /-- Linearity of `m_e` over subtraction in the primal argument. -/
  m_e_sub :
    ∀ (w : 𝒲) (h₁ h₂ : 𝒳 → ℝ),
      m_e w (fun x => h₁ x - h₂ x) = m_e w h₁ - m_e w h₂
  /-- Joint measurability of `ω ↦ m(W ω; q)` for `q ∈ Qbar`. -/
  measurable_m   : ∀ q ∈ Qbar, Measurable (fun ω => m (W ω) q)
  /-- Joint measurability of `ω ↦ m_e(W ω; h)` for `h ∈ Hbar`. -/
  measurable_m_e : ∀ h ∈ Hbar, Measurable (fun ω => m_e (W ω) h)
  /-- Integrability of `ω ↦ m(W ω; q)` for `q ∈ Qbar`. -/
  integrable_m   : ∀ q ∈ Qbar, Integrable (fun ω => m (W ω) q) μ
  /-- Integrability of `ω ↦ m_e(W ω; h)` for `h ∈ Hbar`. -/
  integrable_m_e : ∀ h ∈ Hbar, Integrable (fun ω => m_e (W ω) h) μ
  /-- Integrability of the cross product `q(Z) · h(X)` for `h ∈ Hbar, q ∈ Qbar`,
  where `X = xOf ∘ W` and `Z = zOf ∘ W`. -/
  integrable_qh :
    ∀ h ∈ Hbar, ∀ q ∈ Qbar,
      Integrable (fun ω => q (zOf (W ω)) * h (xOf (W ω))) μ
  /-- Primal nuisance candidate `h₀ ∈ Hbar` satisfying the moment equation. -/
  h₀ : 𝒳 → ℝ
  h₀_mem : h₀ ∈ Hbar
  /-- Primal moment identity (Definition 4.5, item 5):
        `E[m(W; q)] = E[h₀(X) q(Z)]` for every `q ∈ Qbar`. -/
  primal_moment :
    ∀ q ∈ Qbar,
      ∫ ω, m (W ω) q ∂μ = ∫ ω, h₀ (xOf (W ω)) * q (zOf (W ω)) ∂μ

namespace InverseProblemSystem

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- [The treatment-side covariate random variable](goal) of [an inverse-problem
system](hyp:S) on [a measured sample space](hyp:Ω,μ) sends [each outcome](hyp:ω) to the
covariate projection of its generated observation. -/
def X (S : InverseProblemSystem Ω μ) (ω : Ω) : S.𝒳 := S.xOf (S.W ω)

/-- [The instrument-side covariate random variable](goal) of [an inverse-problem
system](hyp:S) on [a measured sample space](hyp:Ω,μ) sends [each outcome](hyp:ω) to the
instrument projection of its generated observation. -/
def Z (S : InverseProblemSystem Ω μ) (ω : Ω) : S.𝒵 := S.zOf (S.W ω)

/-- [The scalar target](goal) of [an inverse-problem system](hyp:S) on [a measured sample
space](hyp:Ω,μ) is the expected treatment-side moment evaluated at the true primal nuisance. -/
noncomputable def θ₀ (S : InverseProblemSystem Ω μ) : ℝ :=
  ∫ ω, S.m_e (S.W ω) S.h₀ ∂μ

/-- [The pointwise doubly robust pseudo-outcome](goal) for [an inverse-problem
system](hyp:S) on [a measured sample space](hyp:Ω,μ) combines [a primal nuisance](hyp:h)
and [a dual nuisance](hyp:q) at [an observation](hyp:w) as the treatment-side moment plus
the outcome-side moment minus their covariate–instrument product.

The pointwise pseudo-outcome at a sample value `w : 𝒲`:
    `φ_{h,q}(w) := m_e(w; h) + m(w; q) − q(zOf w) h(xOf w)`.

This evaluates the doubly-robust score at any observation in the value
space, so it is reusable for empirical (sample-fold) averages. -/
noncomputable def phiVal (S : InverseProblemSystem Ω μ)
    (h : S.𝒳 → ℝ) (q : S.𝒵 → ℝ) (w : S.𝒲) : ℝ :=
  S.m_e w h + S.m w q - q (S.zOf w) * h (S.xOf w)

/-- [The pseudo-outcome along the random observation](goal) evaluates the pointwise score of
[an inverse-problem system](hyp:S) on [a measured sample space](hyp:Ω,μ), using [a primal
nuisance](hyp:h) and [a dual nuisance](hyp:q), at the observation generated by [the given
outcome](hyp:ω).

The pseudo-outcome along the random observation `W`:
    `φ_{h,q}(ω) := φ_{h,q}(W ω)`. -/
noncomputable def phi (S : InverseProblemSystem Ω μ)
    (h : S.𝒳 → ℝ) (q : S.𝒵 → ℝ) (ω : Ω) : ℝ :=
  S.phiVal h q (S.W ω)

/-- `DualSolution S q₀` says `q₀ ∈ Qbar` and `q₀` solves the dual moment
identity
    `E[m_e(W; h)] = E[q₀(Z) h(X)]`
for every `h ∈ Hbar` (`def:est-trae-dual-solution`). -/
structure DualSolution (S : InverseProblemSystem Ω μ) (q₀ : S.𝒵 → ℝ) : Prop where
  /-- Membership of `q₀` in the dual candidate set. -/
  mem : q₀ ∈ S.Qbar
  /-- The dual moment identity. -/
  identity :
    ∀ h ∈ S.Hbar,
      ∫ ω, S.m_e (S.W ω) h ∂μ
        = ∫ ω, q₀ (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ

/-- [The doubly robust functional](goal) for [an inverse-problem system](hyp:S) on [a measured
sample space](hyp:Ω,μ) is the expected pseudo-outcome formed from [a primal nuisance](hyp:h)
and [a dual nuisance](hyp:q).

The doubly-robust functional from `def:est-trae-dr-functional`:
    `Θ(h, q) := E[m_e(W; h) + m(W; q) − q(Z) h(X)] = E[φ_{h,q}(W)]`. -/
noncomputable def Θ (S : InverseProblemSystem Ω μ)
    (h : S.𝒳 → ℝ) (q : S.𝒵 → ℝ) : ℝ :=
  ∫ ω, S.phi h q ω ∂μ

end InverseProblemSystem

end NPIV
end Estimation
end Causalean
