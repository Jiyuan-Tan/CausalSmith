/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.Converse

/-! # Observed-law transport for the MSM converse

This file transports the conditional propensity, calibration identity, and
inverse-probability-weighted target identity from a compatible full-data model
to its common observed-record law.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable {S : POBackdoorSystem P γ} {Λ : ℝ}

namespace MSMDataCompatible

variable (M : MSMDataCompatible S Λ)

/-- For [a compatible model](hyp:M), the [observed candidate induced by its conditional
propensity](goal) uses the `(X,Y)` factor on treated records and the observed propensity on
control records. -/
noncomputable def observedCandidate : P.Ω → ℝ := fun ω =>
  if S.factualD ω then M.xyPropensityFactor (S.factualX ω, S.factualY ω)
  else S.propScore true ω

/-- For [a compatible model](hyp:M), the [record-level version of its induced observed
candidate](goal) is a measurable statistic of `(X,Z,Z·Y)`. -/
noncomputable def recordCandidate : ((γ × Bool) × ℝ) → ℝ := fun r =>
  if r.1.2 then M.xyPropensityFactor (r.1.1, r.2)
  else S.propensityFactor r.1.1

/-- The [record-level induced candidate](hyp:M) is [measurable](goal). -/
@[fun_prop]
theorem measurable_recordCandidate : Measurable M.recordCandidate := by
  unfold recordCandidate
  exact Measurable.ite
    ((measurable_snd.comp measurable_fst) (measurableSet_singleton true))
    (M.measurable_xyPropensityFactor.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (S.measurable_propensityFactor.comp (measurable_fst.comp measurable_fst))

/-- The [induced candidate evaluated on a factual observable record](hyp:M) [is the
record-level candidate](goal). -/
theorem recordCandidate_factualObservedRecord (ω : P.Ω) :
    M.recordCandidate (S.factualObservedRecord ω) = M.observedCandidate ω := by
  by_cases hd : S.factualD ω
  · have hi : S.dVar.indicator true ω = 1 := by
      have hmem : ω ∈ S.treatedSet := by
        simpa [POBackdoorSystem.treatedSet] using hd
      rw [S.treated_indicator_eq]
      simp [hmem]
    simp [recordCandidate, observedCandidate, factualObservedRecord, hd, hi]
  · have hfactor := congrFun S.propScore_eq_propensityFactor_comp ω
    simp [recordCandidate, observedCandidate, factualObservedRecord, hd,
      Function.comp_apply] at hfactor ⊢
    exact hfactor.symm

/-- The [induced candidate evaluated on a compatible model's observable record](hyp:M)
[equals its `(X,Y(1))` conditional propensity on treated units and the observed propensity
on controls](goal). -/
theorem recordCandidate_observedRecord (ω : M.Ω) :
    M.recordCandidate (M.observedRecord ω) =
      if M.Z ω then M.xyPropensity ω else S.propensityFactor (M.X ω) := by
  by_cases hz : M.Z ω
  · have hfactor := congrFun M.xyPropensity_eq_factor_comp ω
    simpa [recordCandidate, MSMDataCompatible.observedRecord, hz,
      Function.comp_apply] using hfactor.symm
  · simp [recordCandidate, MSMDataCompatible.observedRecord, hz]

/-- The [induced observed candidate](hyp:M) has an [observed `(X,Y)`-measurable version on
the treated arm](goal). -/
theorem observedCandidate_observedOnTreated :
    S.ObservedOnTreated M.observedCandidate := by
  let eObs : P.Ω → ℝ := fun ω =>
    M.xyPropensityFactor (S.factualX ω, S.factualY ω)
  have heObs : Measurable[S.sigmaXYObs] eObs := by
    apply M.measurable_xyPropensityFactor.comp
    exact ((comap_measurable S.factualX).mono le_sup_left le_rfl).prodMk
      ((comap_measurable S.factualY).mono le_sup_right le_rfl)
  refine ⟨eObs, heObs, ?_⟩
  filter_upwards [ae_restrict_mem S.measurableSet_treatedSet] with ω hω
  have hd : S.factualD ω = true := by
    simpa [POBackdoorSystem.treatedSet] using hω
  simp [observedCandidate, eObs, hd]

/-- Under [a sensitivity level at least one](hyp:hΛ) and [observed strict overlap](hyp:hoverlap),
the [candidate induced by any compatible model lies in the observed MSM odds box](goal). -/
theorem observedCandidate_mem_MSMSet (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    M.observedCandidate ∈ S.MSMSet true Λ := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hq := M.ae_propensityFactor_mem_Ioo hoverlap
  have hg := M.ae_xyPropensity_mem_Ioo hoverlap
  have hodds := M.xyPropensity_odds hΛ hoverlap
  have hmodelInterior : ∀ᵐ ω ∂M.Q,
      0 < M.recordCandidate (M.observedRecord ω) ∧
        M.recordCandidate (M.observedRecord ω) < 1 := by
    filter_upwards [hq, hg] with ω hqω hgω
    rw [M.recordCandidate_observedRecord]
    split <;> assumption
  have hmodelOdds : ∀ᵐ ω ∂M.Q,
      1 / Λ ≤ OR (M.recordCandidate (M.observedRecord ω))
          (S.propensityFactor (M.observedRecord ω).1.1) ∧
        OR (M.recordCandidate (M.observedRecord ω))
          (S.propensityFactor (M.observedRecord ω).1.1) ≤ Λ := by
    filter_upwards [hq, hodds] with ω hqω hoddsω
    rw [M.recordCandidate_observedRecord]
    by_cases hz : M.Z ω
    · simpa [MSMDataCompatible.observedRecord, hz] using hoddsω
    · have hor : OR (S.propensityFactor (M.X ω))
          (S.propensityFactor (M.X ω)) = 1 := by
        unfold OR
        have hp : S.propensityFactor (M.X ω) ≠ 0 := ne_of_gt hqω.1
        have hpc : 1 - S.propensityFactor (M.X ω) ≠ 0 := by linarith [hqω.2]
        field_simp
      have hlower : 1 / Λ ≤ (1 : ℝ) := by
        rw [div_le_one hΛpos]
        exact hΛ
      simpa [MSMDataCompatible.observedRecord, hz, hor] using And.intro hlower hΛ
  let interior : ((γ × Bool) × ℝ) → Prop := fun r =>
    0 < M.recordCandidate r ∧ M.recordCandidate r < 1
  have hinteriorMeas : MeasurableSet {r | interior r} :=
    (measurableSet_lt measurable_const M.measurable_recordCandidate).inter
      (measurableSet_lt M.measurable_recordCandidate measurable_const)
  let oddsBox : ((γ × Bool) × ℝ) → Prop := fun r =>
    1 / Λ ≤ OR (M.recordCandidate r) (S.propensityFactor r.1.1) ∧
      OR (M.recordCandidate r) (S.propensityFactor r.1.1) ≤ Λ
  have hoddsMeas : MeasurableSet {r | oddsBox r} := by
    have hOR : Measurable (fun r =>
        OR (M.recordCandidate r) (S.propensityFactor r.1.1)) := by
      unfold OR
      fun_prop
    exact (measurableSet_le measurable_const hOR).inter
      (measurableSet_le hOR measurable_const)
  have hfactual : Measurable S.factualObservedRecord := by
    unfold factualObservedRecord
    exact (S.measurable_factualX.prodMk S.measurable_factualD).prodMk
      ((S.dVar.measurable_indicator true (measurableSet_singleton true)).mul
        S.measurable_factualY)
  have hinteriorObs :=
    (Mathlib.MeasureTheory.ae_comp_iff_of_map_eq M.measurable_observedRecord
      hfactual interior hinteriorMeas M.observedLaw).mp hmodelInterior
  have hoddsObs :=
    (Mathlib.MeasureTheory.ae_comp_iff_of_map_eq M.measurable_observedRecord
      hfactual oddsBox hoddsMeas M.observedLaw).mp hmodelOdds
  constructor
  · filter_upwards [hinteriorObs] with ω hω
    simpa [interior, M.recordCandidate_factualObservedRecord] using hω
  · filter_upwards [hoddsObs] with ω hω
    have hfactor := congrFun S.propScore_eq_propensityFactor_comp ω
    change 1 / Λ ≤ OR (M.recordCandidate (S.factualObservedRecord ω))
        (S.propensityFactor (S.factualX ω)) ∧
      OR (M.recordCandidate (S.factualObservedRecord ω))
        (S.propensityFactor (S.factualX ω)) ≤ Λ at hω
    rw [M.recordCandidate_factualObservedRecord] at hω
    simpa [Function.comp_apply, hfactor] using hω

/-- For [a compatible model](hyp:M), the [record-level inverse treatment weight](goal) is
zero on controls and the reciprocal induced candidate on treated records. -/
noncomputable def recordInverseWeight : ((γ × Bool) × ℝ) → ℝ := fun r =>
  if r.1.2 then 1 / M.recordCandidate r else 0

/-- The [record-level inverse treatment weight](hyp:M) is [measurable](goal). -/
@[fun_prop]
theorem measurable_recordInverseWeight : Measurable M.recordInverseWeight := by
  unfold recordInverseWeight
  exact Measurable.ite
    ((measurable_snd.comp measurable_fst) (measurableSet_singleton true))
    (measurable_const.div M.measurable_recordCandidate) measurable_const

/-- The [record inverse weight](hyp:M) composed with the model record [equals the model's
inverse treatment weight](goal). -/
theorem recordInverseWeight_observedRecord :
    M.recordInverseWeight ∘ M.observedRecord = M.inverseWeight := by
  funext ω
  by_cases hz : M.Z ω
  · have hc := M.recordCandidate_observedRecord ω
    simp [recordInverseWeight, MSMDataCompatible.observedRecord, inverseWeight,
      treatmentIndicator, hz] at hc ⊢
    rw [hc]
  · simp [recordInverseWeight, MSMDataCompatible.observedRecord, inverseWeight,
      treatmentIndicator, hz]

/-- The [record inverse weight](hyp:M) composed with the factual record [equals treatment
divided by the induced observed candidate](goal). -/
theorem recordInverseWeight_factualObservedRecord :
    M.recordInverseWeight ∘ S.factualObservedRecord =
      fun ω => S.dVar.indicator true ω / M.observedCandidate ω := by
  funext ω
  change (if S.factualD ω then
      1 / M.recordCandidate (S.factualObservedRecord ω) else 0) =
    S.dVar.indicator true ω / M.observedCandidate ω
  rw [M.recordCandidate_factualObservedRecord]
  by_cases hd : S.factualD ω
  · have hmem : ω ∈ S.treatedSet := by
      simpa [POBackdoorSystem.treatedSet] using hd
    have hi : S.dVar.indicator true ω = 1 := by
      rw [S.treated_indicator_eq]
      simp [hmem]
    simp [hd, hi]
  · have hnmem : ω ∉ S.treatedSet := by
      simpa [POBackdoorSystem.treatedSet] using hd
    have hi : S.dVar.indicator true ω = 0 := by
      rw [S.treated_indicator_eq]
      simp [hnmem]
    simp [hd, hi]

/-- **Transported calibration.** The [candidate induced by a compatible model](hyp:M)
[has conditional inverse-weight mean one given the observed covariate](goal). -/
theorem observedCandidate_calibrated :
    S.Calibrated true M.observedCandidate := by
  let design : ((γ × Bool) × ℝ) → γ := fun r => r.1.1
  have hdesign : Measurable design := measurable_fst.comp measurable_fst
  have hint : Integrable (M.recordInverseWeight ∘ M.observedRecord) M.Q := by
    rw [M.recordInverseWeight_observedRecord]
    exact M.integrable_inverseWeight
  have hcond :
      M.Q[M.recordInverseWeight ∘ M.observedRecord |
        MeasurableSpace.comap (design ∘ M.observedRecord) inferInstance] =ᵐ[M.Q]
          (fun _ => 1) := by
    rw [M.recordInverseWeight_observedRecord]
    simpa [design, MSMDataCompatible.observedRecord, Function.comp_def] using
      M.condExp_inverseWeight_sigmaX_eq_one
  have htransport :=
    Mathlib.MeasureTheory.condExp_comp_eq_one_of_map_eq
      M.measurable_observedRecord
      (by
        unfold factualObservedRecord
        exact (S.measurable_factualX.prodMk S.measurable_factualD).prodMk
          ((S.dVar.measurable_indicator true (measurableSet_singleton true)).mul
            S.measurable_factualY))
      design hdesign M.recordInverseWeight M.measurable_recordInverseWeight
      M.observedLaw hint hcond
  rw [M.recordInverseWeight_factualObservedRecord] at htransport
  unfold Calibrated sigmaX
  simpa [design, factualObservedRecord, Function.comp_def] using htransport

/-- For [a compatible model](hyp:M), the [record-level weighted treated outcome](goal) is
the record's treated outcome multiplied by its inverse treatment weight. -/
noncomputable def recordWeightedOutcome : ((γ × Bool) × ℝ) → ℝ := fun r =>
  M.recordInverseWeight r * r.2

/-- The [record-level weighted treated outcome](hyp:M) is [measurable](goal). -/
@[fun_prop]
theorem measurable_recordWeightedOutcome : Measurable M.recordWeightedOutcome := by
  unfold recordWeightedOutcome
  exact M.measurable_recordInverseWeight.mul measurable_snd

/-- The [record-level weighted outcome](hyp:M) composed with the compatible model record
[equals the full-data weighted potential outcome](goal). -/
theorem recordWeightedOutcome_observedRecord :
    M.recordWeightedOutcome ∘ M.observedRecord = M.weightedY1 := by
  funext ω
  change M.recordInverseWeight (M.observedRecord ω) *
      (if M.Z ω then M.Y1 ω else 0) = M.inverseWeight ω * M.Y1 ω
  have hw : M.recordInverseWeight (M.observedRecord ω) = M.inverseWeight ω := by
    simpa only [Function.comp_apply] using
      congrFun M.recordInverseWeight_observedRecord ω
  rw [hw]
  by_cases hz : M.Z ω
  · simp [hz]
  · simp [hz, inverseWeight, treatmentIndicator]

/-- The [record-level weighted outcome](hyp:M) composed with the factual record [is the
candidate-mean integrand](goal). -/
theorem recordWeightedOutcome_factualObservedRecord :
    M.recordWeightedOutcome ∘ S.factualObservedRecord =
      fun ω => S.dVar.indicator true ω * S.factualY ω / M.observedCandidate ω := by
  funext ω
  simp only [Function.comp_apply]
  unfold recordWeightedOutcome
  have hw : M.recordInverseWeight (S.factualObservedRecord ω) =
      S.dVar.indicator true ω / M.observedCandidate ω := by
    simpa only [Function.comp_apply] using
      congrFun M.recordInverseWeight_factualObservedRecord ω
  rw [hw]
  simp only [factualObservedRecord]
  by_cases hd : S.factualD ω
  · have hmem : ω ∈ S.treatedSet := by
      simpa [POBackdoorSystem.treatedSet] using hd
    have hi : S.dVar.indicator true ω = 1 := by
      rw [S.treated_indicator_eq]
      simp [hmem]
    simp [hi, div_eq_mul_inv, mul_comm]
  · have hnmem : ω ∉ S.treatedSet := by
      simpa [POBackdoorSystem.treatedSet] using hd
    have hi : S.dVar.indicator true ω = 0 := by
      rw [S.treated_indicator_eq]
      simp [hnmem]
    simp [hi]

/-- **Transported IPW identity.** The [candidate mean induced by a compatible model](hyp:M)
[equals that model's full-data treated-potential-outcome mean](goal). -/
theorem candMean_observedCandidate_eq_target :
    S.candMean true M.observedCandidate = M.target := by
  have htransport := Mathlib.MeasureTheory.integral_comp_eq_of_map_eq
    M.measurable_observedRecord
    (by
      unfold factualObservedRecord
      exact (S.measurable_factualX.prodMk S.measurable_factualD).prodMk
        ((S.dVar.measurable_indicator true (measurableSet_singleton true)).mul
          S.measurable_factualY))
    M.recordWeightedOutcome M.measurable_recordWeightedOutcome M.observedLaw
  change ∫ ω, (M.recordWeightedOutcome ∘ M.observedRecord) ω ∂M.Q =
    ∫ ω, (M.recordWeightedOutcome ∘ S.factualObservedRecord) ω ∂P.μ at htransport
  rw [M.recordWeightedOutcome_observedRecord,
    M.recordWeightedOutcome_factualObservedRecord] at htransport
  unfold candMean
  exact htransport.symm.trans M.integral_weightedY1_eq_target

/-- **MSM converse candidate.** Under [a sensitivity level at least one](hyp:hΛ) and
[observed strict overlap](hyp:hoverlap), every [compatible model](hyp:M) induces an
[observed, calibrated MSM candidate](goal). -/
theorem observedCandidate_mem_MSMSetCalibObs (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    M.observedCandidate ∈ S.MSMSetCalibObs Λ :=
  ⟨⟨M.observedCandidate_mem_MSMSet hΛ hoverlap,
      M.observedCandidate_calibrated⟩,
    M.observedCandidate_observedOnTreated⟩

/-- **MSM converse.** Under [a sensitivity level at least one](hyp:hΛ), [observed strict
overlap](hyp:hoverlap), and [boundedness of the calibrated candidate means](hyp:hbdd,hbdd'),
the [treated-potential-outcome mean of every compatible model](hyp:M) [lies in the calibrated
MSM interval](goal). -/
theorem target_mem_Icc_msmCalib (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hbdd : BddBelow (S.candMean true '' S.MSMSetCalib true Λ))
    (hbdd' : BddAbove (S.candMean true '' S.MSMSetCalib true Λ)) :
    M.target ∈ Set.Icc (S.msmLowerCalib true Λ) (S.msmUpperCalib true Λ) := by
  have hmem : M.observedCandidate ∈ S.MSMSetCalib true Λ :=
    (M.observedCandidate_mem_MSMSetCalibObs hΛ hoverlap).1
  have himage : S.candMean true M.observedCandidate ∈
      S.candMean true '' S.MSMSetCalib true Λ := Set.mem_image_of_mem _ hmem
  rw [Set.mem_Icc, ← M.candMean_observedCandidate_eq_target]
  exact ⟨csInf_le hbdd himage, le_csSup hbdd' himage⟩


end MSMDataCompatible

end POBackdoorSystem
end PO
end Causalean
