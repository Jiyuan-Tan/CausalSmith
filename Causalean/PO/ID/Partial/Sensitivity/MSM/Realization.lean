/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Kernel.BernoulliMark
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlCutoffConstruct
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ObservedCandidates

/-! # Calibration identities for MSM full-data realization

This file proves the calibration-to-measure identities needed by the
Dorn--Guo reciprocal-tilt construction. Using calibration's integrability of the inverse treated
weight, an observed representative of a calibrated
candidate produces a reciprocal tilt whose covariate marginal is exactly the
observed covariate law and whose total mass is one. The resulting Bernoulli-mark
law reproduces the factual observed record and has target mean `candMean`.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- If [an observed representative](hyp:h) [agrees on treated units with a
candidate](hyp:heq) whose inverse treated weight [is integrable](hyp:hint), then
[the representative's reciprocal is integrable under the treated sublaw](goal). -/
@[fun_prop]
theorem observed_reciprocal_integrable (etilde h : P.Ω → ℝ)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hint : Integrable (fun ω => S.dVar.indicator true ω / etilde ω) P.μ) :
    Integrable (fun ω => 1 / h ω) (P.μ.restrict S.treatedSet) := by
  refine hint.restrict.congr ?_
  filter_upwards [heq, ae_restrict_mem S.measurableSet_treatedSet] with ω hω hT
  have hA : S.dVar.indicator true ω = 1 := by
    rw [S.treated_indicator_eq]
    simp [hT]
  simp [hA, hω]

/-- Suppose [an observed representative](hyp:h) [agrees on treated
units with a calibrated candidate](hyp:heq,hcal), and [the candidate is positive almost
surely](hyp:hpos). Then [the covariate marginal of the representative's reciprocal tilt of
the treated sublaw equals the observed covariate law](goal). -/
theorem reciprocalTilt_map_factualX_eq_of_calibrated (etilde h : P.Ω → ℝ)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < etilde ω)
    (hcal : S.Calibrated true etilde) :
    (Causalean.Mathlib.Probability.reciprocalTilt
      (P.μ.restrict S.treatedSet) h).map S.factualX = P.μ.map S.factualX := by
  have hint0 : Integrable (fun ω => S.dVar.indicator true ω / etilde ω) P.μ :=
    S.calibrated_weight_integrable true etilde hcal
  have hint : Integrable (fun ω => 1 / h ω) (P.μ.restrict S.treatedSet) :=
    S.observed_reciprocal_integrable etilde h heq hint0
  have hhpos : ∀ᵐ ω ∂P.μ.restrict S.treatedSet, 0 < h ω := by
    filter_upwards [ae_restrict_of_ae hpos, heq] with ω hω hω'
    simpa [← hω'] using hω
  ext B hB
  rw [Measure.map_apply S.measurable_factualX hB,
    Measure.map_apply S.measurable_factualX hB]
  rw [Causalean.Mathlib.Probability.reciprocalTilt]
  rw [withDensity_apply _ (hB.preimage S.measurable_factualX)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn]
  swap
  · filter_upwards [ae_restrict_of_ae hhpos] with ω hω
    exact one_div_nonneg.mpr hω.le
  have hsX : MeasurableSet[S.sigmaX] (S.factualX ⁻¹' B) := by
    rw [POBackdoorSystem.sigmaX]
    exact hB.preimage (comap_measurable S.factualX)
  have hXamb : MeasurableSet (S.factualX ⁻¹' B) :=
    hB.preimage S.measurable_factualX
  have hreal :
      ∫ ω in S.factualX ⁻¹' B, 1 / h ω ∂P.μ.restrict S.treatedSet =
        P.μ.real (S.factualX ⁻¹' B) := by
    calc
      ∫ ω in S.factualX ⁻¹' B, 1 / h ω ∂P.μ.restrict S.treatedSet =
          ∫ ω in S.factualX ⁻¹' B,
            S.dVar.indicator true ω / etilde ω ∂P.μ := by
        rw [Measure.restrict_comm (μ := P.μ) (s := S.factualX ⁻¹' B)
          (t := S.treatedSet) hXamb]
        rw [← integral_indicator S.measurableSet_treatedSet]
        apply integral_congr_ae
        have heq_imp : ∀ᵐ ω ∂P.μ, ω ∈ S.treatedSet → etilde ω = h ω :=
          ae_imp_of_ae_restrict heq
        filter_upwards [ae_restrict_of_ae heq_imp] with ω hω
        by_cases hT : ω ∈ S.treatedSet
        · have hA : S.dVar.indicator true ω = 1 := by
            rw [S.treated_indicator_eq]
            simp [hT]
          simp [Set.indicator_of_mem hT, hA, (hω hT).symm]
        · have hA : S.dVar.indicator true ω = 0 := by
            rw [S.treated_indicator_eq]
            simp [hT]
          simp [Set.indicator_of_notMem hT, hA]
      _ = ∫ ω in S.factualX ⁻¹' B,
            P.μ[fun ω => S.dVar.indicator true ω / etilde ω | S.sigmaX] ω ∂P.μ := by
        symm
        exact setIntegral_condExp S.sigmaX_le hint0 hsX
      _ = ∫ _ω in S.factualX ⁻¹' B, (1 : ℝ) ∂P.μ :=
        setIntegral_congr_ae hXamb (by
          filter_upwards [hcal] with x hx _
          exact hx)
      _ = P.μ.real (S.factualX ⁻¹' B) := by simp
  rw [hreal]
  exact MeasureTheory.ofReal_measureReal (measure_ne_top P.μ _)

/-- Under [the same observed-representative, agreement, positivity, and calibration
conditions](hyp:heq,hpos,hcal), [the reciprocal tilt of the treated sublaw has total mass
one](goal). -/
theorem reciprocalTilt_treated_univ_eq_one (etilde h : P.Ω → ℝ)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < etilde ω)
    (hcal : S.Calibrated true etilde) :
    Causalean.Mathlib.Probability.reciprocalTilt
      (P.μ.restrict S.treatedSet) h univ = 1 := by
  have hmarg := S.reciprocalTilt_map_factualX_eq_of_calibrated
    etilde h heq hpos hcal
  have hu := congrArg (fun μ : Measure γ => μ univ) hmarg
  rw [Measure.map_apply S.measurable_factualX MeasurableSet.univ,
    Measure.map_apply S.measurable_factualX MeasurableSet.univ] at hu
  simpa using hu

/-- For [a base measure](hyp:ν₁), [a unit-interval weight](hyp:h,hpos,hle),
[the reciprocal tilt decomposes into the base measure plus its failure-odds tilt](goal). -/
theorem reciprocalTilt_eq_add_failureTilt
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) (h : α → ℝ)
    (hpos : ∀ᵐ a ∂ν₁, 0 < h a)
    (hle : ∀ᵐ a ∂ν₁, h a ≤ 1) :
    Causalean.Mathlib.Probability.reciprocalTilt ν₁ h =
      ν₁ + ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a)) := by
  unfold Causalean.Mathlib.Probability.reciprocalTilt
  calc
    ν₁.withDensity (fun a => ENNReal.ofReal (1 / h a)) =
        ν₁.withDensity (fun a => 1 + ENNReal.ofReal ((1 - h a) / h a)) := by
      apply withDensity_congr_ae
      filter_upwards [hpos, hle] with a ha ha'
      have hratio : 0 ≤ (1 - h a) / h a :=
        div_nonneg (sub_nonneg.mpr ha') ha.le
      have hreal : 1 / h a = 1 + (1 - h a) / h a := by
        field_simp
        ring
      calc
        ENNReal.ofReal (1 / h a) =
            ENNReal.ofReal (1 + (1 - h a) / h a) := congrArg ENNReal.ofReal hreal
        _ = ENNReal.ofReal 1 + ENNReal.ofReal ((1 - h a) / h a) :=
          ENNReal.ofReal_add zero_le_one hratio
        _ = 1 + ENNReal.ofReal ((1 - h a) / h a) := by simp
    _ = ν₁.withDensity 1 +
        ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a)) := by
      change ν₁.withDensity
          ((fun _a : α => (1 : ENNReal)) +
            (fun a => ENNReal.ofReal ((1 - h a) / h a))) =
        ν₁.withDensity (fun _a : α => (1 : ENNReal)) +
          ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a))
      exact withDensity_add_left measurable_const _
    _ = ν₁ + ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a)) := by
      exact congrArg
        (fun m => m + ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a)))
        withDensity_one

/-- Suppose [an observed representative](hyp:h) [agrees on treated units with a
calibrated candidate](hyp:heq,hcal) that [lies strictly between zero and one](hyp:hpos,hlt).
Then [the covariate marginal of the failure-odds tilt is the observed control-arm covariate
sublaw](goal). -/
theorem failureTilt_map_factualX_eq_control (etilde h : P.Ω → ℝ)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < etilde ω)
    (hlt : ∀ᵐ ω ∂P.μ, etilde ω < 1)
    (hcal : S.Calibrated true etilde) :
    ((P.μ.restrict S.treatedSet).withDensity
      (fun ω => ENNReal.ofReal ((1 - h ω) / h ω))).map S.factualX =
        (P.μ.restrict S.controlSet).map S.factualX := by
  let ν₁ := P.μ.restrict S.treatedSet
  let ν₀ := ν₁.withDensity (fun ω => ENNReal.ofReal ((1 - h ω) / h ω))
  let ν := Causalean.Mathlib.Probability.reciprocalTilt ν₁ h
  have hhpos : ∀ᵐ ω ∂ν₁, 0 < h ω := by
    filter_upwards [ae_restrict_of_ae hpos, heq] with ω hω hω'
    simpa [← hω'] using hω
  have hhle : ∀ᵐ ω ∂ν₁, h ω ≤ 1 := by
    filter_upwards [ae_restrict_of_ae hlt, heq] with ω hω hω'
    exact (hω'.symm ▸ hω).le
  have htilt : ν = ν₁ + ν₀ := by
    exact reciprocalTilt_eq_add_failureTilt ν₁ h hhpos hhle
  have hmarg : ν.map S.factualX = P.μ.map S.factualX := by
    exact S.reciprocalTilt_map_factualX_eq_of_calibrated etilde h heq hpos hcal
  have hcompl : S.treatedSetᶜ = S.controlSet := by
    ext ω
    simp only [POBackdoorSystem.treatedSet, POBackdoorSystem.controlSet,
      Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
    cases S.factualD ω <;> simp
  ext B hB
  rw [Measure.map_apply S.measurable_factualX hB,
    Measure.map_apply S.measurable_factualX hB]
  change ν₀ (S.factualX ⁻¹' B) =
    (P.μ.restrict S.controlSet) (S.factualX ⁻¹' B)
  have htiltB := congrArg (fun m : Measure P.Ω => m (S.factualX ⁻¹' B)) htilt
  rw [Measure.add_apply ν₁ ν₀ (S.factualX ⁻¹' B)] at htiltB
  have hmargB := congrArg (fun m : Measure γ => m B) hmarg
  rw [Measure.map_apply S.measurable_factualX hB,
    Measure.map_apply S.measurable_factualX hB] at hmargB
  have hpart := Measure.restrict_add_restrict_compl
    (μ := P.μ) S.measurableSet_treatedSet
  rw [hcompl] at hpart
  have hpartB := congrArg (fun m : Measure P.Ω => m (S.factualX ⁻¹' B)) hpart
  rw [Measure.add_apply (P.μ.restrict S.treatedSet) (P.μ.restrict S.controlSet)
    (S.factualX ⁻¹' B)] at hpartB
  apply (ENNReal.add_right_inj (measure_ne_top ν₁ (S.factualX ⁻¹' B))).mp
  calc
    ν₁ (S.factualX ⁻¹' B) + ν₀ (S.factualX ⁻¹' B) =
        ν (S.factualX ⁻¹' B) := htiltB.symm
    _ = P.μ (S.factualX ⁻¹' B) := hmargB
    _ = (P.μ.restrict S.treatedSet) (S.factualX ⁻¹' B) +
        (P.μ.restrict S.controlSet) (S.factualX ⁻¹' B) := hpartB.symm
    _ = ν₁ (S.factualX ⁻¹' B) +
        (P.μ.restrict S.controlSet) (S.factualX ⁻¹' B) := by rfl

/-- For [a backdoor system](hyp:S), the [observable record](goal) of a
[marked full-data point](hyp:p) contains its covariate, Boolean treatment mark, and treated
observed outcome `Z·Y(1)`. -/
noncomputable def markedObservedRecord (p : P.Ω × Bool) : (γ × Bool) × ℝ :=
  ((S.factualX p.1, p.2), if p.2 then S.factualY p.1 else 0)

/-- For [a backdoor system](hyp:S), the [factual observable record](goal) of an
[observational unit](hyp:ω) contains its covariate, factual treatment, and treated observed
outcome. -/
noncomputable def factualObservedRecord (ω : P.Ω) : (γ × Bool) × ℝ :=
  ((S.factualX ω, S.factualD ω),
    S.dVar.indicator true ω * S.factualY ω)

/-- Suppose [a measurable observed representative](hyp:h,hh) [agrees on treated units with a
calibrated candidate](hyp:heq,hcal) that [lies strictly between zero and one](hyp:hpos,hlt).
Then [the reciprocal-tilt Bernoulli construction has exactly the factual observed law of
`(X,Z,Z·Y)`](goal). -/
theorem bernoulliMarkedLaw_observedRecord_eq (etilde h : P.Ω → ℝ)
    (hh : Measurable h)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < etilde ω)
    (hlt : ∀ᵐ ω ∂P.μ, etilde ω < 1)
    (hcal : S.Calibrated true etilde) :
    (Causalean.Mathlib.Probability.bernoulliMarkedLaw
      (P.μ.restrict S.treatedSet) h).map S.markedObservedRecord =
        P.μ.map S.factualObservedRecord := by
  let ν₁ := P.μ.restrict S.treatedSet
  let Q := Causalean.Mathlib.Probability.bernoulliMarkedLaw ν₁ h
  let T : Set (P.Ω × Bool) := univ ×ˢ {true}
  let F : Set (P.Ω × Bool) := univ ×ˢ {false}
  have hT : MeasurableSet T := MeasurableSet.univ.prod (measurableSet_singleton true)
  have hF : MeasurableSet F := MeasurableSet.univ.prod (measurableSet_singleton false)
  have hTF : Tᶜ = F := by
    ext ⟨ω, z⟩
    cases z <;> simp [T, F]
  have hg : Measurable S.markedObservedRecord := by
    unfold markedObservedRecord
    exact ((S.measurable_factualX.comp measurable_fst).prodMk measurable_snd).prodMk
      (Measurable.ite (measurable_snd (measurableSet_singleton true))
        (S.measurable_factualY.comp measurable_fst) measurable_const)
  have hf : Measurable S.factualObservedRecord := by
    unfold factualObservedRecord
    exact (S.measurable_factualX.prodMk S.measurable_factualD).prodMk
      ((S.dVar.measurable_indicator true (measurableSet_singleton true)).mul
        S.measurable_factualY)
  have hhpos : ∀ᵐ ω ∂ν₁, 0 < h ω := by
    filter_upwards [ae_restrict_of_ae hpos, heq] with ω hω hω'
    simpa [← hω'] using hω
  have hhle : ∀ᵐ ω ∂ν₁, h ω ≤ 1 := by
    filter_upwards [ae_restrict_of_ae hlt, heq] with ω hω hω'
    exact (hω'.symm ▸ hω).le
  have hQpart : Q.restrict T + Q.restrict F = Q := by
    rw [← hTF]
    exact Measure.restrict_add_restrict_compl (μ := Q) hT
  have hcompl : S.treatedSetᶜ = S.controlSet := by
    ext ω
    simp only [POBackdoorSystem.treatedSet, POBackdoorSystem.controlSet,
      Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
    cases S.factualD ω <;> simp
  have hPpart : P.μ.restrict S.treatedSet + P.μ.restrict S.controlSet = P.μ := by
    rw [← hcompl]
    exact Measure.restrict_add_restrict_compl (μ := P.μ) S.measurableSet_treatedSet
  have htreated : (Q.restrict T).map S.markedObservedRecord =
      (P.μ.restrict S.treatedSet).map S.factualObservedRecord := by
    calc
      (Q.restrict T).map S.markedObservedRecord =
          ν₁.map (fun ω => S.markedObservedRecord (ω, true)) := by
        exact Causalean.Mathlib.Probability.bernoulliMarkedLaw_map_restrict_true
          ν₁ h hh hhpos S.markedObservedRecord hg
      _ = ν₁.map S.factualObservedRecord := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem S.measurableSet_treatedSet] with ω hω
        have hD : S.factualD ω = true := hω
        have hA : S.dVar.indicator true ω = 1 := by
          rw [S.treated_indicator_eq]
          simp [hω]
        simp [markedObservedRecord, factualObservedRecord, hD, hA]
  have hcontrol : (Q.restrict F).map S.markedObservedRecord =
      (P.μ.restrict S.controlSet).map S.factualObservedRecord := by
    let ν₀ := ν₁.withDensity (fun ω => ENNReal.ofReal ((1 - h ω) / h ω))
    let k : P.Ω → (γ × Bool) × ℝ :=
      fun ω => ((S.factualX ω, false), 0)
    let j : γ → (γ × Bool) × ℝ := fun x => ((x, false), 0)
    have hk : Measurable k := by dsimp [k]; fun_prop
    have hj : Measurable j := by dsimp [j]; fun_prop
    have hrestrict : (Q.restrict F).map S.markedObservedRecord =
        (Q.restrict F).map (k ∘ Prod.fst) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hF] with p hp
      rcases p with ⟨ω, z⟩
      have hz : z = false := hp.2
      simp [markedObservedRecord, k, hz]
    have hfalsefst : (Q.restrict F).map Prod.fst = ν₀ := by
      exact Causalean.Mathlib.Probability.bernoulliMarkedLaw_restrict_false_map_fst
        ν₁ h hh hhpos hhle
    have hcov : ν₀.map S.factualX =
        (P.μ.restrict S.controlSet).map S.factualX := by
      exact S.failureTilt_map_factualX_eq_control etilde h heq hpos hlt hcal
    calc
      (Q.restrict F).map S.markedObservedRecord =
          (Q.restrict F).map (k ∘ Prod.fst) := hrestrict
      _ = ((Q.restrict F).map Prod.fst).map k := by
        rw [Measure.map_map hk measurable_fst]
      _ = ν₀.map k := by rw [hfalsefst]
      _ = ν₀.map (j ∘ S.factualX) := by rfl
      _ = (ν₀.map S.factualX).map j := by
        rw [Measure.map_map hj S.measurable_factualX]
      _ = ((P.μ.restrict S.controlSet).map S.factualX).map j := by rw [hcov]
      _ = (P.μ.restrict S.controlSet).map (j ∘ S.factualX) := by
        rw [Measure.map_map hj S.measurable_factualX]
      _ = (P.μ.restrict S.controlSet).map S.factualObservedRecord := by
        apply Measure.map_congr
        have hcontrol_meas : MeasurableSet S.controlSet := by
          rw [← hcompl]
          exact S.measurableSet_treatedSet.compl
        filter_upwards [ae_restrict_mem hcontrol_meas] with ω hω
        have hD : S.factualD ω = false := hω
        have hA : S.dVar.indicator true ω = 0 := by
          rw [S.treated_indicator_eq]
          have hnT : ω ∉ S.treatedSet := by
            have hmem : ω ∈ S.treatedSetᶜ := by rwa [hcompl]
            exact hmem
          simp [hnT]
        simp [j, factualObservedRecord, hD, hA]
  calc
    Q.map S.markedObservedRecord =
        (Q.restrict T + Q.restrict F).map S.markedObservedRecord := by rw [hQpart]
    _ = (Q.restrict T).map S.markedObservedRecord +
        (Q.restrict F).map S.markedObservedRecord := Measure.map_add _ _ hg
    _ = (P.μ.restrict S.treatedSet).map S.factualObservedRecord +
        (P.μ.restrict S.controlSet).map S.factualObservedRecord := by
      rw [htreated, hcontrol]
    _ = (P.μ.restrict S.treatedSet +
        P.μ.restrict S.controlSet).map S.factualObservedRecord :=
      (Measure.map_add _ _ hf).symm
    _ = P.μ.map S.factualObservedRecord := by rw [hPpart]

/-- Suppose [a measurable observed representative](hyp:h,hh) [agrees on treated units with a
candidate](hyp:heq) that [lies strictly between zero and one](hyp:hpos,hlt). Then [the mean of
the treated potential outcome in the reciprocal-tilt Bernoulli construction equals the
candidate inverse-probability-weighted mean](goal). -/
theorem bernoulliMarkedLaw_target_eq_candMean (etilde h : P.Ω → ℝ)
    (hh : Measurable h)
    (heq : etilde =ᵐ[P.μ.restrict S.treatedSet] h)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < etilde ω)
    (hlt : ∀ᵐ ω ∂P.μ, etilde ω < 1) :
    ∫ p, S.factualY p.1 ∂Causalean.Mathlib.Probability.bernoulliMarkedLaw
        (P.μ.restrict S.treatedSet) h = S.candMean true etilde := by
  let ν₁ := P.μ.restrict S.treatedSet
  have hhpos : ∀ᵐ ω ∂ν₁, 0 < h ω := by
    filter_upwards [ae_restrict_of_ae hpos, heq] with ω hω hω'
    simpa [← hω'] using hω
  have hhle : ∀ᵐ ω ∂ν₁, h ω ≤ 1 := by
    filter_upwards [ae_restrict_of_ae hlt, heq] with ω hω hω'
    exact (hω'.symm ▸ hω).le
  rw [← integral_map measurable_fst.aemeasurable
    S.measurable_factualY.aestronglyMeasurable]
  rw [Causalean.Mathlib.Probability.bernoulliMarkedLaw_map_fst ν₁ h hh hhpos hhle]
  rw [Causalean.Mathlib.Probability.reciprocalTilt]
  have hdens : Measurable (fun ω => ENNReal.ofReal (1 / h ω)) :=
    (measurable_const.div hh).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hdens (by simp) S.factualY]
  unfold candMean
  rw [← integral_indicator S.measurableSet_treatedSet]
  apply integral_congr_ae
  have hhpos_imp : ∀ᵐ ω ∂P.μ, ω ∈ S.treatedSet → 0 < h ω :=
    ae_imp_of_ae_restrict hhpos
  have heq_imp : ∀ᵐ ω ∂P.μ, ω ∈ S.treatedSet → etilde ω = h ω :=
    ae_imp_of_ae_restrict heq
  filter_upwards [hhpos_imp, heq_imp] with ω hω hω'
  by_cases hT : ω ∈ S.treatedSet
  · have hA : S.dVar.indicator true ω = 1 := by
      rw [S.treated_indicator_eq]
      simp [hT]
    rw [Set.indicator_of_mem hT, ENNReal.toReal_ofReal
      (one_div_nonneg.mpr (hω hT).le), hA, hω' hT]
    simp only [one_mul, div_eq_mul_inv]
    ring
  · have hA : S.dVar.indicator true ω = 0 := by
      rw [S.treated_indicator_eq]
      simp [hT]
    simp [Set.indicator_of_notMem hT, hA]

end POBackdoorSystem

end PO
end Causalean
