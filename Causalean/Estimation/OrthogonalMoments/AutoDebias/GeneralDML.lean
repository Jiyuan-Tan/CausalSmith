/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DML bridge for general automatic debiasing

Packages a regression nuisance and a mean-pairing nuisance into the joint
nuisance type expected by the abstract orthogonal-moment and DML layers.
-/

module
public import Causalean.Estimation.OrthogonalMoments.AutoDebias.General

/-! # General automatic-debiasing moment for DML

The construction in this file turns `RegNuisanceMomentSys` and an
`AutoDebiasMeanRepresentation` into a `LinearMoment` whenever the original score is
affine in the scalar target.  Its observation-level moment
is exactly `autoDebiasedScore`; its nuisance truth is `(g₀, α₀)`; and its two
error gauges are the L² errors of the regression target and representer. -/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory
open Causalean.Estimation.OrthogonalMoments

/-- For [a regression-nuisance moment system](hyp:S), the [joint nuisance type
used by the general automatic-debiasing DML bridge](goal) pairs a regression
nuisance with a candidate representer on the covariate space. -/
abbrev generalAutoNuisance (S : RegNuisanceMomentSys) : Type _ :=
  S.H × (S.X → ℝ)

/-- For [a regression-nuisance moment system](hyp:S), its [joint automatic-debiasing
nuisance type has the componentwise additive commutative group structure](goal). -/
noncomputable instance generalAutoNuisance.instAddCommGroup
    (S : RegNuisanceMomentSys) : AddCommGroup (generalAutoNuisance S) := by
  unfold generalAutoNuisance
  infer_instance

/-- For [a regression-nuisance moment system](hyp:S), its [joint automatic-debiasing
nuisance type has the componentwise real vector-space structure](goal). -/
noncomputable instance generalAutoNuisance.instModule
    (S : RegNuisanceMomentSys) : Module ℝ (generalAutoNuisance S) := by
  unfold generalAutoNuisance
  exact Prod.instModule

/-- Given [an auxiliary sampling measure](hyp:μ), [a regression-nuisance moment
system](hyp:S), [its automatic-debiasing representer](hyp:rep), [a nonnegative
neighborhood radius](hyp:ε,hε), [measurability of every debiased score](hyp:hscore),
[an affine decomposition of the original score](hyp:m_a,m_b,h_m_a_meas,h_m_decomp),
and [a nonzero population mean of the truth coefficient](hyp:hJ₀), the [associated
linear moment](goal) uses the joint nuisance `(g, α)`, the automatically debiased
observation-level score, and L² regression-target and representer error gauges.

Its Jacobian is defined as `∫ m_a(g₀,z) dP_Z`; it is not a caller-supplied scalar. -/
noncomputable def autoDebiasedGeneralMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : RegNuisanceMomentSys) (rep : AutoDebiasMeanRepresentation S)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hscore : ∀ η : generalAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => autoDebiasedScore S η.1 η.2 θ z))
    (m_a m_b : S.H → S.Z → ℝ)
    (h_m_a_meas : ∀ g, Measurable (m_a g))
    (h_m_decomp : ∀ g z θ, S.m g z θ = m_a g z * θ + m_b g z)
    (hJ₀ : (∫ z, m_a S.g₀ z ∂S.P_Z) ≠ 0) :
    LinearMoment Ω μ S.Z S.P_Z (generalAutoNuisance S) where
  m := fun η z θ => autoDebiasedScore S η.1 η.2 θ z
  η₀ := (S.g₀, rep.α₀)
  θ₀ := S.θ₀
  H_ε := {η |
    (eLpNorm (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x) 2 S.P_X).toReal ≤ ε ∧
    (eLpNorm (fun x => η.2 x - rep.α₀ x) 2 S.P_X).toReal ≤ ε}
  ρ₁ := fun η η' =>
    ⟨(eLpNorm (fun x => S.γ_target η.1 x - S.γ_target η'.1 x) 2 S.P_X).toReal,
      ENNReal.toReal_nonneg⟩
  ρ₂ := fun η η' =>
    ⟨(eLpNorm (fun x => η.2 x - η'.2 x) 2 S.P_X).toReal,
      ENNReal.toReal_nonneg⟩
  m_meas := hscore
  η₀_mem := by simp [hε]
  linScale := ∫ z, m_a S.g₀ z ∂S.P_Z
  linScale_ne_zero := hJ₀
  m_a := fun η => m_a η.1
  m_b := fun η z => m_b η.1 z + η.2 (S.proj_X z) *
    (S.Y_obs z - S.γ_target η.1 (S.proj_X z))
  m_a_meas := fun η => h_m_a_meas η.1
  m_b_meas := fun η => by
    have h0 := hscore η 0
    have heq : (fun z => autoDebiasedScore S η.1 η.2 0 z) =
        fun z => m_b η.1 z + η.2 (S.proj_X z) *
          (S.Y_obs z - S.γ_target η.1 (S.proj_X z)) := by
      funext z
      rw [autoDebiasedScore, h_m_decomp]
      ring
    rw [← heq]
    exact h0
  m_decomp := by
    intro η z θ
    rw [autoDebiasedScore, h_m_decomp]
    ring
  linScale_eq := rfl

/-- Under [the inputs defining the general automatic-debiasing
moment](hyp:μ,S,rep,ε,hε,hscore,m_a,m_b,h_m_a_meas,h_m_decomp,hJ₀), if [the truth baseline moment](hyp:h_m_int)
and [representer-weighted truth residual](hyp:h_resid_int) are integrable, then
[the bridged general moment has population mean zero at its nuisance and
parameter truth](goal). -/
theorem autoDebiasedGeneralMoment_meanZero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : RegNuisanceMomentSys) (rep : AutoDebiasMeanRepresentation S)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hscore : ∀ η : generalAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => autoDebiasedScore S η.1 η.2 θ z))
    (m_a m_b : S.H → S.Z → ℝ)
    (h_m_a_meas : ∀ g, Measurable (m_a g))
    (h_m_decomp : ∀ g z θ, S.m g z θ = m_a g z * θ + m_b g z)
    (hJ₀ : (∫ z, m_a S.g₀ z ∂S.P_Z) ≠ 0)
    (h_m_int : Integrable (fun z => S.m S.g₀ z S.θ₀) S.P_Z)
    (h_resid_int : Integrable
      (fun z => rep.α₀ (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z) :
    MeanZero (autoDebiasedGeneralMoment μ S rep ε hε hscore
      m_a m_b h_m_a_meas h_m_decomp hJ₀).toGeneralMoment := by
  exact autoDebiasedMoment_meanZero_at_truth S rep h_resid_int h_m_int

end Causalean.Estimation.OrthogonalMoments.AutoDebias
