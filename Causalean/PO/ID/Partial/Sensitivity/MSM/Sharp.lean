/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.CompatibleRealization

/-! # Sharpness of the calibrated marginal sensitivity bounds

This file combines the arbitrary-model converse with reciprocal-tilt
realizations of supplied upper and lower cutoff candidates. Under the explicit
feasibility, overlap, integrability, and boundedness hypotheses below, the
calibrated variational endpoints are the supremum and infimum of the compatible
full-data treated-potential-outcome means.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

universe u

variable {P : POSystem.{u, u, u}} {γ : Type u} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Given [an observed backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[compatible treated means](goal) are the means of `Y(1)` across all compatible full-data
models in the ambient universe. -/
def compatibleTargets (Λ : ℝ) : Set ℝ :=
  {θ | ∃ M : MSMDataCompatible.{u, u} S Λ, M.target = θ}

/-- **Conditional sharpness from supplied cutoff realizations.** Fix
[a sensitivity level at least one](hyp:hΛ), [strict observed overlap](hyp:hoverlap),
[upper and lower covariate cutoffs](hyp:cUpper,cLower), [upper-cutoff measurability and
integrability](hyp:hcUpper_meas,hcUpper_int), [upper-cutoff feasibility and envelope
conditions](hyp:hupper_mem,hupper_env,hupper_weight_env,hupper_c_env), [lower-cutoff
measurability and integrability](hyp:hcLower_meas,hcLower_int), [lower-cutoff feasibility
and envelope conditions](hyp:hlower_mem,hlower_env,hlower_weight_env,hlower_c_env). If the two
realized cutoff propensities additionally have [uniform overlap on the treated
law](hyp:hupper_uniform,hlower_uniform) and produce [integrable
potential outcomes under their marked laws](hyp:hupper_Y1_int,hlower_Y1_int), and the
calibrated candidate means are [bounded below and above](hyp:hbddBelow,hbddAbove), then
[the calibrated upper and lower endpoints are respectively the supremum and infimum of
the compatible full-data treated means](goal).

This is a conditional realization theorem, not Dorn--Guo Theorem 1 under the paper's population
conditions: it assumes feasible extremal cutoffs and their realization regularity. In the source,
Appendix C.3 proves Proposition 2 and Theorem 1; Appendix C.2 proves Corollary 4. -/
theorem msmCalib_sharp [StandardBorelSpace P.Ω]
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (cUpper cLower : P.Ω → ℝ)
    (hcUpper_meas : Measurable[S.sigmaX] cUpper)
    (hcUpper_int : Integrable cUpper P.μ)
    (hupper_mem : S.cutoffProp Λ cUpper ∈ S.MSMSetCalib true Λ)
    (hupper_env : Integrable
      (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hupper_weight_env : Integrable
      (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hupper_c_env : Integrable
      (fun ω => |cUpper ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hcLower_meas : Measurable[S.sigmaX] cLower)
    (hcLower_int : Integrable cLower P.μ)
    (hlower_mem : S.lowerCutoffProp Λ cLower ∈ S.MSMSetCalib true Λ)
    (hlower_env : Integrable
      (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hlower_weight_env : Integrable
      (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hlower_c_env : Integrable
      (fun ω => |cLower ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hupper_uniform : ∃ ε : ℝ, 0 < ε ∧
      ∀ᵐ ω ∂P.μ.restrict S.treatedSet,
        ε ≤ S.cutoffProp Λ cUpper ω ∧ S.cutoffProp Λ cUpper ω ≤ 1 - ε)
    (hlower_uniform : ∃ ε : ℝ, 0 < ε ∧
      ∀ᵐ ω ∂P.μ.restrict S.treatedSet,
        ε ≤ S.lowerCutoffProp Λ cLower ω ∧
          S.lowerCutoffProp Λ cLower ω ≤ 1 - ε)
    (hupper_Y1_int : Integrable (fun p : P.Ω × Bool => S.factualY p.1)
      (Causalean.Mathlib.Probability.bernoulliMarkedLaw
        (P.μ.restrict S.treatedSet) (S.cutoffProp Λ cUpper)))
    (hlower_Y1_int : Integrable (fun p : P.Ω × Bool => S.factualY p.1)
      (Causalean.Mathlib.Probability.bernoulliMarkedLaw
        (P.μ.restrict S.treatedSet) (S.lowerCutoffProp Λ cLower)))
    (hbddBelow : BddBelow (S.candMean true '' S.MSMSetCalib true Λ))
    (hbddAbove : BddAbove (S.candMean true '' S.MSMSetCalib true Λ)) :
    S.msmUpperCalib true Λ = sSup (S.compatibleTargets Λ) ∧
      S.msmLowerCalib true Λ = sInf (S.compatibleTargets Λ) := by
  have hupper_obs : S.cutoffProp Λ cUpper ∈ S.MSMSetCalibObs Λ :=
    S.cutoffProp_mem_MSMSetCalibObs Λ cUpper hcUpper_meas hupper_mem
  have hlower_obs : S.lowerCutoffProp Λ cLower ∈ S.MSMSetCalibObs Λ :=
    S.lowerCutoffProp_mem_MSMSetCalibObs Λ cLower hcLower_meas hlower_mem
  have hwMin_meas : Measurable (S.wMin Λ) := S.measurable_wMin Λ
  have hwMax_meas : Measurable (S.wMax Λ) := S.measurable_wMax Λ
  have hupper_meas : Measurable (S.cutoffProp Λ cUpper) := by
    unfold POBackdoorSystem.cutoffProp
    exact measurable_const.div (Measurable.ite
      (measurableSet_lt (hcUpper_meas.mono S.sigmaX_le le_rfl) S.measurable_factualY)
      hwMax_meas hwMin_meas)
  have hlower_meas : Measurable (S.lowerCutoffProp Λ cLower) := by
    unfold POBackdoorSystem.lowerCutoffProp
    exact measurable_const.div (Measurable.ite
      (measurableSet_lt (hcLower_meas.mono S.sigmaX_le le_rfl) S.measurable_factualY)
      hwMin_meas hwMax_meas)
  obtain ⟨MUpper, hMUpper⟩ := S.exists_compatible_realization Λ
    (S.cutoffProp Λ cUpper) (S.cutoffProp Λ cUpper) hupper_meas
    Filter.EventuallyEq.rfl hupper_obs hupper_uniform hupper_Y1_int
  obtain ⟨MLower, hMLower⟩ := S.exists_compatible_realization Λ
    (S.lowerCutoffProp Λ cLower) (S.lowerCutoffProp Λ cLower) hlower_meas
    Filter.EventuallyEq.rfl hlower_obs hlower_uniform hlower_Y1_int
  have hupperCut : S.candMean true (S.cutoffProp Λ cUpper) =
      S.msmUpperCalib true Λ :=
    (S.msmUpperCalib_eq_cutoff Λ hΛ hoverlap cUpper hcUpper_meas
      hcUpper_int hupper_mem hupper_env hupper_weight_env hupper_c_env).symm
  have hlowerCut : S.candMean true (S.lowerCutoffProp Λ cLower) =
      S.msmLowerCalib true Λ :=
    (S.msmLowerCalib_eq_cutoff Λ hΛ hoverlap cLower hcLower_meas
      hcLower_int hlower_mem hlower_env hlower_weight_env hlower_c_env).symm
  have hupperTarget : MUpper.target = S.msmUpperCalib true Λ := hMUpper.trans hupperCut
  have hlowerTarget : MLower.target = S.msmLowerCalib true Λ := hMLower.trans hlowerCut
  have hUpperMem : MUpper.target ∈ S.compatibleTargets Λ := ⟨MUpper, rfl⟩
  have hLowerMem : MLower.target ∈ S.compatibleTargets Λ := ⟨MLower, rfl⟩
  have hne : (S.compatibleTargets Λ).Nonempty := ⟨MUpper.target, hUpperMem⟩
  have hall : ∀ θ ∈ S.compatibleTargets Λ,
      S.msmLowerCalib true Λ ≤ θ ∧ θ ≤ S.msmUpperCalib true Λ := by
    rintro θ ⟨M, rfl⟩
    exact M.target_mem_Icc_msmCalib hΛ hoverlap hbddBelow hbddAbove
  have hTargetsAbove : BddAbove (S.compatibleTargets Λ) :=
    ⟨S.msmUpperCalib true Λ, fun θ hθ => (hall θ hθ).2⟩
  have hTargetsBelow : BddBelow (S.compatibleTargets Λ) :=
    ⟨S.msmLowerCalib true Λ, fun θ hθ => (hall θ hθ).1⟩
  constructor
  · apply le_antisymm
    · rw [← hupperTarget]
      exact le_csSup hTargetsAbove hUpperMem
    · exact csSup_le hne fun θ hθ => (hall θ hθ).2
  · apply le_antisymm
    · exact le_csInf hne fun θ hθ => (hall θ hθ).1
    · rw [← hlowerTarget]
      exact csInf_le hTargetsBelow hLowerMem

end POBackdoorSystem

end PO
end Causalean
