/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ConverseObserved

/-! # Compatible full-data realization of an observed MSM candidate

This file packages the reciprocal-tilt Bernoulli construction as an
`MSMDataCompatible` model.  The base observational unit is retained as the latent
variable, so latent unconfoundedness is immediate; the marked law supplies the
complete propensity and reproduces the observable record law.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

universe u

variable {P : POSystem.{u, u, u}} {γ : Type u} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Given [a measurable observed candidate representative](hyp:h,hh) that [agrees on the
treated arm](hyp:heq) with [an observed calibrated MSM candidate](hyp:hmem), has [uniform
two-sided overlap under the treated law](hyp:huniform), and yields an [integrable potential
outcome under the marked law](hyp:hint), there [exists a compatible full-data model whose
target equals the candidate mean](goal). -/
theorem exists_compatible_realization [StandardBorelSpace P.Ω]
    (Λ : ℝ) (etilde h : P.Ω → ℝ)
    (hh : Measurable h)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hmem : etilde ∈ S.MSMSetCalibObs Λ)
    (huniform : ∃ ε : ℝ, 0 < ε ∧
      ∀ᵐ ω ∂P.μ.restrict S.treatedSet, ε ≤ h ω ∧ h ω ≤ 1 - ε)
    (hint : Integrable (fun p : P.Ω × Bool => S.factualY p.1)
      (Causalean.Mathlib.Probability.bernoulliMarkedLaw
        (P.μ.restrict S.treatedSet) h)) :
    ∃ M : MSMDataCompatible.{u, u} S Λ, M.target = S.candMean true etilde := by
  let ν₁ := P.μ.restrict S.treatedSet
  let Q := Causalean.Mathlib.Probability.bernoulliMarkedLaw ν₁ h
  have hposE : ∀ᵐ ω ∂P.μ, 0 < etilde ω := hmem.1.1.1.mono fun _ hω => hω.1
  have hltE : ∀ᵐ ω ∂P.μ, etilde ω < 1 := hmem.1.1.1.mono fun _ hω => hω.2
  have hhpos : ∀ᵐ ω ∂ν₁, 0 < h ω := by
    filter_upwards [ae_restrict_of_ae hposE, heq] with ω hω heqω
    simpa [← heqω] using hω
  have hhle : ∀ᵐ ω ∂ν₁, h ω ≤ 1 := by
    filter_upwards [ae_restrict_of_ae hltE, heq] with ω hω heqω
    exact (heqω.symm ▸ hω).le
  have hmass : Causalean.Mathlib.Probability.reciprocalTilt ν₁ h Set.univ = 1 :=
    S.reciprocalTilt_treated_univ_eq_one etilde h heq hposE hmem.1.2
  have hprob : IsProbabilityMeasure Q :=
    Causalean.Mathlib.Probability.bernoulliMarkedLaw_isProbabilityMeasure
      ν₁ h hh hhpos hhle hmass
  let _ : IsProbabilityMeasure Q := hprob
  let X : P.Ω × Bool → γ := fun p => S.factualX p.1
  let U : P.Ω × Bool → P.Ω := Prod.fst
  let Z : P.Ω × Bool → Bool := Prod.snd
  let Y1 : P.Ω × Bool → ℝ := fun p => S.factualY p.1
  have hmXU :
      MeasurableSpace.comap X inferInstance ⊔
        MeasurableSpace.comap U inferInstance =
          MeasurableSpace.comap Prod.fst inferInstance := by
    apply le_antisymm
    · apply sup_le
      · exact MeasurableSpace.comap_le_comap_of_eq_comp
          S.factualX S.measurable_factualX rfl
      · exact le_rfl
    · exact le_sup_right
  have hcond :
      Q[(fun p => if p.2 then (1 : ℝ) else 0) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[Q]
          (fun p => h p.1) :=
    Causalean.Mathlib.Probability.bernoulliMarkedLaw_condExp_mark
      ν₁ h hh hhpos hhle hmass
  let eFull : P.Ω × Bool → ℝ :=
    Q[(fun p => if p.2 then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance ⊔
        MeasurableSpace.comap U inferInstance]
  have heFull : eFull =ᵐ[Q] (fun p => h p.1) := by
    change Q[(fun p => if p.2 then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance ⊔
        MeasurableSpace.comap U inferInstance] =ᵐ[Q] (fun p => h p.1)
    rw [hmXU]
    exact hcond
  have hbase : Q.map Prod.fst =
      Causalean.Mathlib.Probability.reciprocalTilt ν₁ h :=
    Causalean.Mathlib.Probability.bernoulliMarkedLaw_map_fst
      ν₁ h hh hhpos hhle
  have hac : Causalean.Mathlib.Probability.reciprocalTilt ν₁ h ≪ ν₁ :=
    withDensity_absolutelyContinuous ν₁ (fun a => ENNReal.ofReal (1 / h a))
  obtain ⟨ε, hε, huniform⟩ := huniform
  have huniformQ : ∀ᵐ p ∂Q, ε ≤ h p.1 ∧ h p.1 ≤ 1 - ε := by
    have ht := hac.ae_le huniform
    rw [← hbase] at ht
    exact (ae_map_iff measurable_fst.aemeasurable
      ((measurableSet_le measurable_const hh).inter
        (measurableSet_le hh measurable_const))).mp ht
  have hoverFull : ∀ᵐ p ∂Q, ε ≤ eFull p ∧ eFull p ≤ 1 - ε := by
    filter_upwards [heFull, huniformQ] with p hep hp
    simpa [hep] using hp
  have hoddsE := hmem.1.1.2
  have hoddsH : ∀ᵐ ω ∂ν₁,
      1 / Λ ≤ OR (h ω) (S.propensityFactor (S.factualX ω)) ∧
        OR (h ω) (S.propensityFactor (S.factualX ω)) ≤ Λ := by
    filter_upwards [ae_restrict_of_ae hoddsE, heq] with ω hω heqω
    have hfactor := congrFun S.propScore_eq_propensityFactor_comp ω
    simpa [← heqω, Function.comp_apply, hfactor] using hω
  have hoddsQ : ∀ᵐ p ∂Q,
      1 / Λ ≤ OR (eFull p) (S.propensityFactor (X p)) ∧
        OR (eFull p) (S.propensityFactor (X p)) ≤ Λ := by
    have ht := hac.ae_le hoddsH
    rw [← hbase] at ht
    have htQ := (ae_map_iff measurable_fst.aemeasurable
      (by
        have hor : Measurable (fun ω =>
            OR (h ω) (S.propensityFactor (S.factualX ω))) := by
          unfold OR
          fun_prop
        exact (measurableSet_le measurable_const hor).inter
          (measurableSet_le hor measurable_const))).mp ht
    filter_upwards [heFull, htQ] with p hep hp
    simpa [eFull, X, hep] using hp
  have hlatent : CondIndepFun
      (MeasurableSpace.comap X inferInstance ⊔
        MeasurableSpace.comap U inferInstance)
      (sup_le (S.measurable_factualX.comp measurable_fst).comap_le measurable_fst.comap_le)
      Z Y1 Q := by
    apply condIndepFun_of_measurable_right (measurable_snd)
    have hY : Measurable[
        MeasurableSpace.comap X inferInstance ⊔
          MeasurableSpace.comap U inferInstance] Y1 := by
      rw [hmXU]
      apply Measurable.of_comap_le
      exact MeasurableSpace.comap_le_comap_of_eq_comp
        S.factualY S.measurable_factualY rfl
    exact hY
  let M : MSMDataCompatible S Λ := {
    Ω := P.Ω × Bool
    UType := P.Ω
    Q := Q
    X := X
    U := U
    Z := Z
    Y1 := Y1
    completePropensity := eFull
    measurable_X := S.measurable_factualX.comp measurable_fst
    measurable_U := measurable_fst
    measurable_Z := measurable_snd
    measurable_Y1 := S.measurable_factualY.comp measurable_fst
    propensity_eq := by rfl
    latentUnconfounded := hlatent
    completeOverlap := ⟨ε, hε, hoverFull⟩
    completeOdds := hoddsQ
    observedLaw := S.bernoulliMarkedLaw_observedRecord_eq
      etilde h hh heq hposE hltE hmem.1.2
    integrable_Y1 := hint }
  refine ⟨M, ?_⟩
  exact S.bernoulliMarkedLaw_target_eq_candMean etilde h hh heq hposE hltE

end POBackdoorSystem

end PO
end Causalean
