/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.LowerBound
public import Causalean.PO.ID.Partial.Sensitivity.MSM.QuantileBalance

/-! # Observed candidates for the treated marginal sensitivity model

Dorn--Guo's calibrated variational problem optimizes over candidates that are
functions of the observed covariate and outcome on the treated arm. This file
formalizes that candidate class and proves that restricting the existing
calibrated variational problem to it does not change either endpoint: the
explicit upper and lower quantile-cutoff optimizers are observed-data measurable.

The construction of a compatible full-data law realizing every observed
candidate is a separate measure-construction problem and is not asserted here.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Given [a binary-treatment backdoor system](hyp:S), the [observed covariate--outcome
σ-algebra](goal) is the least σ-algebra on the population making both the factual covariate and
factual outcome measurable. -/
noncomputable def sigmaXYObs : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.factualX inferInstance
    ⊔ MeasurableSpace.comap S.factualY inferInstance

/-- Given [a binary-treatment backdoor system](hyp:S) and [a candidate propensity](hyp:etilde),
the candidate is [observed-data measurable on the treated arm](goal) when it has a version that
is [measurable with respect to the factual covariate--outcome σ-algebra](step:1) and [agrees with
the candidate almost surely among treated units](step:2). -/
def ObservedOnTreated (etilde : P.Ω → ℝ) : Prop :=
  ∃ eObs : P.Ω → ℝ,
    Measurable[S.sigmaXYObs] eObs ∧
      etilde =ᵐ[P.μ.restrict S.treatedSet] eObs

/-- Given [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[observed calibrated treated candidate set](goal) consists of candidates that belong to the
calibrated marginal-sensitivity set and are observed-data measurable on the treated
arm. -/
def MSMSetCalibObs (Λ : ℝ) : Set (P.Ω → ℝ) :=
  { etilde | etilde ∈ S.MSMSetCalib true Λ ∧ S.ObservedOnTreated etilde }

/-- Given [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[observed-candidate calibrated upper endpoint](goal) is the supremum of the treated candidate
mean over observed calibrated candidates. -/
noncomputable def msmUpperCalibObs (Λ : ℝ) : ℝ :=
  sSup (S.candMean true '' S.MSMSetCalibObs Λ)

/-- Given [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), the
[observed-candidate calibrated lower endpoint](goal) is the infimum of the treated candidate
mean over observed calibrated candidates. -/
noncomputable def msmLowerCalibObs (Λ : ℝ) : ℝ :=
  sInf (S.candMean true '' S.MSMSetCalibObs Λ)

/-- For [a binary-treatment backdoor system](hyp:S) and [a sensitivity level](hyp:Λ), [every
observed calibrated treated candidate is a calibrated treated candidate](goal). -/
theorem MSMSetCalibObs_subset (Λ : ℝ) : S.MSMSetCalibObs Λ ⊆ S.MSMSetCalib true Λ :=
  fun _ h => h.1

private lemma sigmaX_le_sigmaXYObs : S.sigmaX ≤ S.sigmaXYObs := by
  rw [POBackdoorSystem.sigmaX, POBackdoorSystem.sigmaXYObs]
  exact le_sup_left

@[fun_prop]
private lemma measurable_factualY_sigmaXYObs : Measurable[S.sigmaXYObs] S.factualY := by
  exact (comap_measurable S.factualY).mono le_sup_right le_rfl

@[fun_prop]
private lemma measurable_propScore_sigmaXYObs (d : Bool) :
    Measurable[S.sigmaXYObs] (S.propScore d) := by
  exact stronglyMeasurable_condExp.measurable.mono S.sigmaX_le_sigmaXYObs le_rfl

@[fun_prop]
private lemma measurable_wMin_sigmaXYObs (Λ : ℝ) :
    Measurable[S.sigmaXYObs] (S.wMin Λ) := by
  unfold POBackdoorSystem.wMin
  fun_prop

@[fun_prop]
private lemma measurable_wMax_sigmaXYObs (Λ : ℝ) :
    Measurable[S.sigmaXYObs] (S.wMax Λ) := by
  unfold POBackdoorSystem.wMax
  fun_prop

@[fun_prop]
private lemma measurable_cutoffProp_sigmaXYObs (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable[S.sigmaXYObs] (S.cutoffProp Λ c) := by
  unfold POBackdoorSystem.cutoffProp
  have hc' : Measurable[S.sigmaXYObs] c := hc.mono S.sigmaX_le_sigmaXYObs le_rfl
  exact measurable_const.div (Measurable.ite
    (measurableSet_lt hc' S.measurable_factualY_sigmaXYObs)
    (S.measurable_wMax_sigmaXYObs Λ) (S.measurable_wMin_sigmaXYObs Λ))

@[fun_prop]
private lemma measurable_lowerCutoffProp_sigmaXYObs (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable[S.sigmaXYObs] (S.lowerCutoffProp Λ c) := by
  unfold POBackdoorSystem.lowerCutoffProp
  have hc' : Measurable[S.sigmaXYObs] c := hc.mono S.sigmaX_le_sigmaXYObs le_rfl
  exact measurable_const.div (Measurable.ite
    (measurableSet_lt hc' S.measurable_factualY_sigmaXYObs)
    (S.measurable_wMin_sigmaXYObs Λ) (S.measurable_wMax_sigmaXYObs Λ))

/-- For [a binary-treatment backdoor system](hyp:S), [a sensitivity level](hyp:Λ), and [a
covariate-measurable cutoff](hyp:c,hc), if [the upper-cutoff candidate is calibrated and
box-feasible](hyp:hmem), then [that candidate belongs to the observed calibrated treated
class](goal). -/
theorem cutoffProp_mem_MSMSetCalibObs (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) (hmem : S.cutoffProp Λ c ∈ S.MSMSetCalib true Λ) :
    S.cutoffProp Λ c ∈ S.MSMSetCalibObs Λ := by
  refine ⟨hmem, S.cutoffProp Λ c, S.measurable_cutoffProp_sigmaXYObs Λ c hc, ?_⟩
  exact Filter.EventuallyEq.rfl

/-- For [a binary-treatment backdoor system](hyp:S), [a sensitivity level](hyp:Λ), and [a
covariate-measurable cutoff](hyp:c,hc), if [the lower-cutoff candidate is calibrated and
box-feasible](hyp:hmem), then [that candidate belongs to the observed calibrated treated
class](goal). -/
theorem lowerCutoffProp_mem_MSMSetCalibObs (Λ : ℝ) (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) (hmem : S.lowerCutoffProp Λ c ∈ S.MSMSetCalib true Λ) :
    S.lowerCutoffProp Λ c ∈ S.MSMSetCalibObs Λ := by
  refine ⟨hmem, S.lowerCutoffProp Λ c,
    S.measurable_lowerCutoffProp_sigmaXYObs Λ c hc, ?_⟩
  exact Filter.EventuallyEq.rfl

/-- **Observed-candidate upper endpoint.** Fix [a sensitivity level at least one](hyp:hΛ),
[strict overlap](hyp:hoverlap), and [a covariate-measurable integrable cutoff](hyp:c,hc_meas,hc_int)
whose upper-cutoff candidate is [calibrated and box-feasible](hyp:hcut_mem). Under [the three
integrable envelopes used by the cutoff exchange argument](hyp:henv,hweight_env,hc_env), [the supremum over
observed-data calibrated candidates equals the calibrated MSM upper endpoint](goal). -/
theorem msmUpperCalibObs_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.cutoffProp Λ c ∈ S.MSMSetCalib true Λ)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ) :
    S.msmUpperCalibObs Λ = S.msmUpperCalib true Λ := by
  let eCut := S.cutoffProp Λ c
  have hcut_obs : eCut ∈ S.MSMSetCalibObs Λ :=
    S.cutoffProp_mem_MSMSetCalibObs Λ c hc_meas hcut_mem
  have hne : (S.candMean true '' S.MSMSetCalibObs Λ).Nonempty :=
    ⟨S.candMean true eCut, Set.mem_image_of_mem _ hcut_obs⟩
  have hle_all : ∀ x ∈ S.candMean true '' S.MSMSetCalibObs Λ, x ≤ S.candMean true eCut := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env hc_env
      hmem.1
  have hbdd : BddAbove (S.candMean true '' S.MSMSetCalibObs Λ) :=
    ⟨S.candMean true eCut, hle_all⟩
  have hobs : S.msmUpperCalibObs Λ = S.candMean true eCut := by
    unfold POBackdoorSystem.msmUpperCalibObs
    exact le_antisymm (csSup_le hne hle_all)
      (le_csSup hbdd (Set.mem_image_of_mem _ hcut_obs))
  calc
    S.msmUpperCalibObs Λ = S.candMean true eCut := hobs
    _ = S.msmUpperCalib true Λ :=
      (S.msmUpperCalib_eq_cutoff Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv
        hweight_env hc_env).symm

/-- **Observed-candidate lower endpoint.** Fix [a sensitivity level at least one](hyp:hΛ),
[strict overlap](hyp:hoverlap), and [a covariate-measurable integrable cutoff](hyp:c,hc_meas,hc_int)
whose lower-cutoff candidate is [calibrated and box-feasible](hyp:hcut_mem). Under [the three
integrable envelopes used by the lower-cutoff exchange argument](hyp:henv,hweight_env,hc_env), [the infimum over
observed-data calibrated candidates equals the calibrated MSM lower endpoint](goal). -/
theorem msmLowerCalibObs_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.lowerCutoffProp Λ c ∈ S.MSMSetCalib true Λ)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ) :
    S.msmLowerCalibObs Λ = S.msmLowerCalib true Λ := by
  let eCut := S.lowerCutoffProp Λ c
  have hcut_obs : eCut ∈ S.MSMSetCalibObs Λ :=
    S.lowerCutoffProp_mem_MSMSetCalibObs Λ c hc_meas hcut_mem
  have hne : (S.candMean true '' S.MSMSetCalibObs Λ).Nonempty :=
    ⟨S.candMean true eCut, Set.mem_image_of_mem _ hcut_obs⟩
  have hle_all : ∀ x ∈ S.candMean true '' S.MSMSetCalibObs Λ, S.candMean true eCut ≤ x := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal_lower Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env
      hc_env hmem.1
  have hbdd : BddBelow (S.candMean true '' S.MSMSetCalibObs Λ) :=
    ⟨S.candMean true eCut, hle_all⟩
  have hobs : S.msmLowerCalibObs Λ = S.candMean true eCut := by
    unfold POBackdoorSystem.msmLowerCalibObs
    exact le_antisymm (csInf_le hbdd (Set.mem_image_of_mem _ hcut_obs))
      (le_csInf hne hle_all)
  calc
    S.msmLowerCalibObs Λ = S.candMean true eCut := hobs
    _ = S.msmLowerCalib true Λ :=
      (S.msmLowerCalib_eq_cutoff Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv
        hweight_env hc_env).symm

end POBackdoorSystem

end PO
end Causalean
