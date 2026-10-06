/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlLowerBound
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlQuantileBalance
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ObservedCandidates

/-! # Observed candidates for the control marginal sensitivity model

This file is the control-arm reflection of `MSM.ObservedCandidates`. It restricts calibrated
control candidates to functions with an observed covariate--outcome measurable
version on the control arm and proves that the explicit control cutoff
optimizers keep both calibrated endpoints unchanged.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Given [a binary-treatment backdoor system](hyp:S) and
[a candidate control propensity](hyp:etilde),
the candidate is [observed-data measurable on the control arm](goal) when it has a version that is
[measurable with respect to the factual covariate--outcome σ-algebra](step:1) and [agrees with the
candidate almost surely among control units](step:2). -/
def ObservedOnControl (etilde : P.Ω → ℝ) : Prop :=
  ∃ eObs : P.Ω → ℝ,
    Measurable[S.sigmaXYObs] eObs ∧
      etilde =ᵐ[P.μ.restrict S.controlSet] eObs

/-- Given [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[observed calibrated control candidate set](goal) consists of candidates that belong to the
calibrated control marginal-sensitivity set and are observed-data measurable on the
control arm. -/
def MSMSetCalibObs0 (Λ : ℝ) : Set (P.Ω → ℝ) :=
  { etilde | etilde ∈ S.MSMSetCalib0 Λ ∧ S.ObservedOnControl etilde }

/-- Given [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[observed-candidate calibrated control upper endpoint](goal) is the supremum of the control
candidate mean over observed calibrated control candidates. -/
noncomputable def msmUpperCalibObs0 (Λ : ℝ) : ℝ :=
  sSup (S.candMean0 '' S.MSMSetCalibObs0 Λ)

/-- Given [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[observed-candidate calibrated control lower endpoint](goal) is the infimum of the control
candidate mean over observed calibrated control candidates. -/
noncomputable def msmLowerCalibObs0 (Λ : ℝ) : ℝ :=
  sInf (S.candMean0 '' S.MSMSetCalibObs0 Λ)

/-- For [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), [every
observed calibrated control candidate is a calibrated control candidate](goal). -/
theorem MSMSetCalibObs0_subset (Λ : ℝ) : S.MSMSetCalibObs0 Λ ⊆ S.MSMSetCalib0 Λ :=
  fun _ h => h.1

private lemma sigmaX_le_sigmaXYObs0 : S.sigmaX ≤ S.sigmaXYObs := by
  rw [POBackdoorSystem.sigmaX, POBackdoorSystem.sigmaXYObs]
  exact le_sup_left

@[fun_prop]
private lemma measurable_factualY_sigmaXYObs0 : Measurable[S.sigmaXYObs] S.factualY := by
  exact (comap_measurable S.factualY).mono le_sup_right le_rfl

@[fun_prop]
private lemma measurable_propScore_sigmaXYObs0 (d : Bool) :
    Measurable[S.sigmaXYObs] (S.propScore d) := by
  exact stronglyMeasurable_condExp.measurable.mono S.sigmaX_le_sigmaXYObs0 le_rfl

@[fun_prop]
private lemma measurable_wMin0_sigmaXYObs (Λ : ℝ) :
    Measurable[S.sigmaXYObs] (S.wMin0 Λ) := by
  unfold POBackdoorSystem.wMin0
  fun_prop

@[fun_prop]
private lemma measurable_wMax0_sigmaXYObs (Λ : ℝ) :
    Measurable[S.sigmaXYObs] (S.wMax0 Λ) := by
  unfold POBackdoorSystem.wMax0
  fun_prop

@[fun_prop]
private lemma measurable_cutoffProp0_sigmaXYObs (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable[S.sigmaXYObs] (S.cutoffProp0 Λ c) := by
  unfold POBackdoorSystem.cutoffProp0
  have hc' : Measurable[S.sigmaXYObs] c := hc.mono S.sigmaX_le_sigmaXYObs0 le_rfl
  exact measurable_const.div (Measurable.ite
    (measurableSet_lt hc' S.measurable_factualY_sigmaXYObs0)
    (S.measurable_wMax0_sigmaXYObs Λ) (S.measurable_wMin0_sigmaXYObs Λ))

@[fun_prop]
private lemma measurable_lowerCutoffProp0_sigmaXYObs (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable[S.sigmaXYObs] (S.lowerCutoffProp0 Λ c) := by
  unfold POBackdoorSystem.lowerCutoffProp0
  have hc' : Measurable[S.sigmaXYObs] c := hc.mono S.sigmaX_le_sigmaXYObs0 le_rfl
  exact measurable_const.div (Measurable.ite
    (measurableSet_lt hc' S.measurable_factualY_sigmaXYObs0)
    (S.measurable_wMin0_sigmaXYObs Λ) (S.measurable_wMax0_sigmaXYObs Λ))

/-- For [a binary-treatment backdoor system](hyp:S), [a sensitivity level](hyp:Λ), and [a
covariate-measurable cutoff](hyp:c,hc), if [the upper control-cutoff candidate is calibrated and
box-feasible](hyp:hmem), then [that candidate belongs to the observed calibrated control
class](goal). -/
theorem cutoffProp0_mem_MSMSetCalibObs0 (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) (hmem : S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ) :
    S.cutoffProp0 Λ c ∈ S.MSMSetCalibObs0 Λ := by
  refine ⟨hmem, S.cutoffProp0 Λ c, S.measurable_cutoffProp0_sigmaXYObs Λ c hc, ?_⟩
  exact Filter.EventuallyEq.rfl

/-- For [a binary-treatment backdoor system](hyp:S), [a sensitivity level](hyp:Λ), and [a
covariate-measurable cutoff](hyp:c,hc), if [the lower control-cutoff candidate is calibrated and
box-feasible](hyp:hmem), then [that candidate belongs to the observed calibrated control
class](goal). -/
theorem lowerCutoffProp0_mem_MSMSetCalibObs0 (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) (hmem : S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ) :
    S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalibObs0 Λ := by
  refine ⟨hmem, S.lowerCutoffProp0 Λ c,
    S.measurable_lowerCutoffProp0_sigmaXYObs Λ c hc, ?_⟩
  exact Filter.EventuallyEq.rfl

/-- **Observed-candidate control upper endpoint.** Fix
[a sensitivity level at least one](hyp:hΛ), [strict control overlap](hyp:hoverlap), and
[a covariate-measurable integrable cutoff](hyp:c,hc_meas,hc_int)
whose upper control-cutoff candidate is [calibrated and box-feasible](hyp:hcut_mem). Under [the
three integrable envelopes used by the control exchange argument](hyp:henv,hweight_env,hc_env),
[the supremum over observed-data calibrated control candidates equals the calibrated control upper
endpoint](goal). -/
theorem msmUpperCalibObs0_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ)
    (henv : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    S.msmUpperCalibObs0 Λ = S.msmUpperCalib0 Λ := by
  let eCut := S.cutoffProp0 Λ c
  have hcut_obs : eCut ∈ S.MSMSetCalibObs0 Λ :=
    S.cutoffProp0_mem_MSMSetCalibObs0 Λ c hc_meas hcut_mem
  have hne : (S.candMean0 '' S.MSMSetCalibObs0 Λ).Nonempty :=
    ⟨S.candMean0 eCut, Set.mem_image_of_mem _ hcut_obs⟩
  have hle_all : ∀ x ∈ S.candMean0 '' S.MSMSetCalibObs0 Λ, x ≤ S.candMean0 eCut := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal0 Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env hc_env
      hmem.1
  have hbdd : BddAbove (S.candMean0 '' S.MSMSetCalibObs0 Λ) :=
    ⟨S.candMean0 eCut, hle_all⟩
  have hobs : S.msmUpperCalibObs0 Λ = S.candMean0 eCut := by
    unfold POBackdoorSystem.msmUpperCalibObs0
    exact le_antisymm (csSup_le hne hle_all)
      (le_csSup hbdd (Set.mem_image_of_mem _ hcut_obs))
  calc
    S.msmUpperCalibObs0 Λ = S.candMean0 eCut := hobs
    _ = S.msmUpperCalib0 Λ :=
      (S.msmUpperCalib0_eq_cutoff Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv
        hweight_env hc_env).symm

/-- **Observed-candidate control lower endpoint.** Fix
[a sensitivity level at least one](hyp:hΛ), [strict control overlap](hyp:hoverlap), and
[a covariate-measurable integrable cutoff](hyp:c,hc_meas,hc_int)
whose lower control-cutoff candidate is [calibrated and box-feasible](hyp:hcut_mem). Under [the
three integrable envelopes used by the lower control exchange argument](hyp:henv,hweight_env,hc_env),
[the infimum over observed-data calibrated control candidates equals the calibrated control lower
endpoint](goal). -/
theorem msmLowerCalibObs0_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ)
    (henv : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    S.msmLowerCalibObs0 Λ = S.msmLowerCalib0 Λ := by
  let eCut := S.lowerCutoffProp0 Λ c
  have hcut_obs : eCut ∈ S.MSMSetCalibObs0 Λ :=
    S.lowerCutoffProp0_mem_MSMSetCalibObs0 Λ c hc_meas hcut_mem
  have hne : (S.candMean0 '' S.MSMSetCalibObs0 Λ).Nonempty :=
    ⟨S.candMean0 eCut, Set.mem_image_of_mem _ hcut_obs⟩
  have hle_all : ∀ x ∈ S.candMean0 '' S.MSMSetCalibObs0 Λ, S.candMean0 eCut ≤ x := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal0_lower Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env
      hc_env hmem.1
  have hbdd : BddBelow (S.candMean0 '' S.MSMSetCalibObs0 Λ) :=
    ⟨S.candMean0 eCut, hle_all⟩
  have hobs : S.msmLowerCalibObs0 Λ = S.candMean0 eCut := by
    unfold POBackdoorSystem.msmLowerCalibObs0
    exact le_antisymm (csInf_le hbdd (Set.mem_image_of_mem _ hcut_obs))
      (le_csInf hne hle_all)
  calc
    S.msmLowerCalibObs0 Λ = S.candMean0 eCut := hobs
    _ = S.msmLowerCalib0 Λ :=
      (S.msmLowerCalib0_eq_cutoff Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv
        hweight_env hc_env).symm

end POBackdoorSystem

end PO
end Causalean
