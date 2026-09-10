/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.EstimatorMeasurable
import Causalean.Mathlib.MeasureTheory.CondExpPreimage
import Causalean.Mathlib.MeasureTheory.PartitionIntegral

/-! # A measurable global version of the clamp regression -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set

noncomputable section

/-- [clamp design is measurable](goal) for [the specified `J` input](hyp:J). -/
lemma clampDesign_measurable {J : ℕ} :
    Measurable (fun o : ClampObs J => (o.X, o.A)) := by
  let h : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_fst.comp h).prodMk
    (measurable_fst.comp (measurable_snd.comp h))

/-- [clamp outcome is measurable](goal) for [the specified `J` input](hyp:J). -/
lemma clampOutcome_measurable {J : ℕ} : Measurable (fun o : ClampObs J => o.Y) := by
  exact measurable_snd.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

/-- Extend the model's regression from its declared dose interval by zero. -/
def clampRegressionExtension (P : ClampLaw J) (d : Fin J × ℝ) : ℝ :=
  if d.2 ∈ Set.Icc (0 : ℝ) 1 then P.mu d.1 d.2 else 0

private lemma measurable_mu_extension {J : ℕ} (P : ClampLaw J)
    {beta L : ℝ} (hholder : HolderRegression P beta L) (x : Fin J) :
    Measurable fun a : ℝ => if a ∈ Set.Icc (0 : ℝ) 1 then P.mu x a else 0 := by
  let f : ℝ → ℝ := fun a => P.mu x a
  let g : ℝ → ℝ := fun _ => 0
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) := (hholder x).1
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)ᶜ := continuous_const.continuousOn
  convert hf.measurable_piecewise hg measurableSet_Icc using 1
  funext a
  by_cases ha : a ∈ Set.Icc (0 : ℝ) 1 <;> simp [f, g, Set.piecewise, ha]

/-- [clamp regression extension is measurable](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `L` input](hyp:L), [the specified `hholder` input](hyp:hholder). -/
lemma clampRegressionExtension_measurable {J : ℕ} (P : ClampLaw J)
    {beta L : ℝ} (hholder : HolderRegression P beta L) :
    Measurable (clampRegressionExtension P) := by
  apply measurable_from_prod_countable_right
  intro x
  exact measurable_mu_extension P hholder x

/-- [clamp regression extension satisfies the stated identity](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `x` input](hyp:x), [the specified `a` input](hyp:a), [the specified `ha` input](hyp:ha). -/
lemma clampRegressionExtension_eq {J : ℕ} (P : ClampLaw J)
    (x : Fin J) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    clampRegressionExtension P (x, a) = P.mu x a := by
  simp [clampRegressionExtension, ha]

/-- [clamp regression extension lies in the stated closed interval](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `L` input](hyp:L), [the specified `hholder` input](hyp:hholder), [the specified `d` input](hyp:d). -/
lemma clampRegressionExtension_mem_Icc {J : ℕ} (P : ClampLaw J)
    {beta L : ℝ} (hholder : HolderRegression P beta L) (d : Fin J × ℝ) :
    clampRegressionExtension P d ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ha : d.2 ∈ Set.Icc (0 : ℝ) 1
  · simpa [clampRegressionExtension, ha] using (hholder d.1).2.1 d.2 ha
  · simp [clampRegressionExtension, ha]

/-- [clamp outcome is integrable](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel). -/
lemma clampOutcome_integrable {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    Integrable (fun o : ClampObs J => o.Y) P.dataMeasure := by
  let _ := hmodel.probability
  refine Integrable.of_bound clampOutcome_measurable.aestronglyMeasurable 1 ?_
  filter_upwards [hmodel.outcomeSupport] with o ho
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [ho.1], ho.2⟩

/-- [the stated clamp regression extension almost everywhere identity mu property holds](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel). -/
lemma clampRegressionExtension_ae_eq_mu {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    (fun o : ClampObs J => clampRegressionExtension P (o.X, o.A)) =ᵐ[P.dataMeasure]
      fun o => P.mu o.X o.A := by
  filter_upwards [hmodel.treatmentSupport] with o ho
  exact clampRegressionExtension_eq P o.X ho

private lemma conditionalTreatmentMeasure_finite {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (x : Fin J) :
    IsFiniteMeasure (conditionalTreatmentMeasure P x) := by
  have hpiInt : Integrable (P.pi x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
    · exact (aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
        (hmodel.condDensity.1 x)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc,
        hmodel.condDensity.2.1 x, hmodel.thinning x] with a ha hnon hthin
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      calc
        P.pi x a ≤ cplus * a ^ kappa := hthin.2
        _ ≤ cplus := by
          simpa using mul_le_mul_of_nonneg_left
            (Real.rpow_le_one ha.1 ha.2 hkappa) hcplus
  refine ⟨?_⟩
  simp only [conditionalTreatmentMeasure]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  exact lt_of_le_of_lt (lintegral_mono fun a => Real.ofReal_le_enorm _)
    hpiInt.hasFiniteIntegral

private lemma conditionalRegression_integrable {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (x : Fin J)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Integrable (B.indicator (P.mu x)) (conditionalTreatmentMeasure P x) := by
  let _ := conditionalTreatmentMeasure_finite P hmodel hkappa hcplus x
  have hm : Measurable (B.indicator (fun a =>
      if a ∈ Set.Icc (0 : ℝ) 1 then P.mu x a else 0)) :=
    (measurable_mu_extension P hmodel.holder x).indicator hB
  have hsupp : ∀ᵐ a ∂conditionalTreatmentMeasure P x,
      a ∈ Set.Icc (0 : ℝ) 1 := by
    unfold conditionalTreatmentMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Icc)
  have hint : Integrable (B.indicator (fun a =>
      if a ∈ Set.Icc (0 : ℝ) 1 then P.mu x a else 0))
      (conditionalTreatmentMeasure P x) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [hsupp] with a ha
    rw [Real.norm_eq_abs]
    by_cases hBa : a ∈ B
    · simp only [Set.indicator_of_mem hBa, if_pos ha]
      exact abs_le.2 ⟨by linarith [(hmodel.holder x).2.1 a ha |>.1],
        (hmodel.holder x).2.1 a ha |>.2⟩
    · simp [Set.indicator_of_notMem hBa]
  refine hint.congr (hsupp.mono fun a ha => ?_)
  change 0 ≤ a ∧ a ≤ 1 at ha
  by_cases hBa : a ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hBa, ha]

/-- The conditional-expectation regression tie implies the cellwise
set-integral identity used by the causal bridge. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hB` condition](hyp:hB), [the `hBIcc` condition](hyp:hBIcc). [This is the stated conclusion](goal).
-/
lemma holderRegression_setIntegral {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) (B : Set ℝ) (hB : MeasurableSet B)
    (hBIcc : B ⊆ Set.Icc (0 : ℝ) 1) :
    (∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B}, o.Y ∂P.dataMeasure) =
      P.px x * ∫ a in B, P.mu x a * P.pi x a := by
  let _ := hmodel.probability
  let design : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
  let E : Set (ClampObs J) := {o | o.X = x ∧ o.A ∈ B}
  have hdesign : Measurable design := clampDesign_measurable
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun
      (measurable_fst.comp (Measurable.of_comap_le le_rfl)) measurable_const).inter
      (hB.preimage
        (measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))))
  have hEcond : MeasurableSet[MeasurableSpace.comap design inferInstance] E := by
    have hrect : MeasurableSet (({x} : Set (Fin J)) ×ˢ B) :=
      (measurableSet_singleton x).prod hB
    have hpre : E = design ⁻¹' (({x} : Set (Fin J)) ×ˢ B) := by
      ext o
      simp [E, design]
    rw [hpre]
    exact hrect.preimage (Measurable.of_comap_le le_rfl)
  have hY := clampOutcome_integrable P hmodel
  have hcond := (hmodel.holder x).2.2.1
  have hf := conditionalRegression_integrable P hmodel
    hkappa hcplus x B hB
  have htreat := stratumTreatment_integral_eq P hmodel.toBridge
    hkappa hcplus hpmin x (B.indicator (P.mu x)) hf
  rw [conditionalTreatment_integral_eq_density P hmodel.toBridge x] at htreat
  calc
    (∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B}, o.Y ∂P.dataMeasure) =
        ∫ o in E, o.Y ∂P.dataMeasure := by rfl
    _ = ∫ o in E,
        P.dataMeasure[(fun o : ClampObs J => o.Y) |
          MeasurableSpace.comap design inferInstance] o ∂P.dataMeasure :=
      (setIntegral_condExp hdesign.comap_le hY hEcond).symm
    _ = ∫ o in E, P.mu o.X o.A ∂P.dataMeasure := by
      exact setIntegral_congr_ae hE (hcond.mono fun o ho _ => ho)
    _ = ∫ o, Set.indicator {o : ClampObs J | o.X = x}
        (fun o => B.indicator (P.mu x) o.A) o ∂P.dataMeasure := by
      rw [← integral_indicator hE]
      apply integral_congr_ae
      filter_upwards with o
      by_cases hx : o.X = x <;> by_cases ha : o.A ∈ B <;>
        simp [E, Set.indicator, hx, ha]
    _ = P.px x * ∫ a in Set.Icc (0 : ℝ) 1,
        P.pi x a * B.indicator (P.mu x) a := htreat
    _ = P.px x * ∫ a in B, P.mu x a * P.pi x a := by
      congr 1
      rw [← integral_indicator measurableSet_Icc, ← integral_indicator hB]
      apply integral_congr_ae
      filter_upwards with a
      by_cases ha : a ∈ B
      · have haI := hBIcc ha
        simp [Set.indicator_of_mem ha, haI, mul_comm]
      · by_cases haI : a ∈ Set.Icc (0 : ℝ) 1 <;>
          simp [Set.indicator_of_notMem ha, haI]

/-- Any integrable conditional-regression version satisfies the same cellwise
set-integral identity; this is the smoothness-free form used by the
continuity-only causal bridge. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hver` condition](hyp:hver), [the `hB` condition](hyp:hB), [the `hBIcc` condition](hyp:hBIcc), [the `hmuInt` condition](hyp:hmuInt). [This is the stated conclusion](goal).
-/
-- @node: regressionVersion_setIntegral
lemma regressionVersion_setIntegral {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin : ℝ}
    (hmodel : BridgeClampModel P kappa cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (mu : Fin J → ℝ → ℝ)
    (hver : P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => mu o.X o.A)
    (x : Fin J) (B : Set ℝ) (hB : MeasurableSet B)
    (hBIcc : B ⊆ Set.Icc (0 : ℝ) 1)
    (hmuInt : Integrable (B.indicator (mu x)) (conditionalTreatmentMeasure P x)) :
    (∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B}, o.Y ∂P.dataMeasure) =
      P.px x * ∫ a in B, mu x a * P.pi x a := by
  let _ := hmodel.probability
  let design : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
  let E : Set (ClampObs J) := {o | o.X = x ∧ o.A ∈ B}
  have hdesign : Measurable design := clampDesign_measurable
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun
      (measurable_fst.comp (Measurable.of_comap_le le_rfl)) measurable_const).inter
      (hB.preimage (measurable_fst.comp (measurable_snd.comp
        (Measurable.of_comap_le le_rfl))))
  have hEcond : MeasurableSet[MeasurableSpace.comap design inferInstance] E := by
    rw [show E = design ⁻¹' (({x} : Set (Fin J)) ×ˢ B) by ext o; simp [E, design]]
    exact ((measurableSet_singleton x).prod hB).preimage (Measurable.of_comap_le le_rfl)
  have hY : Integrable (fun o : ClampObs J => o.Y) P.dataMeasure := by
    refine Integrable.of_bound clampOutcome_measurable.aestronglyMeasurable 1 ?_
    filter_upwards [hmodel.outcomeSupport] with o ho
    simpa [Real.norm_eq_abs] using (abs_le.2 ⟨by linarith [ho.1], ho.2⟩)
  have htreat := stratumTreatment_integral_eq P hmodel hkappa hcplus hpmin
    x (B.indicator (mu x)) hmuInt
  rw [conditionalTreatment_integral_eq_density P hmodel x] at htreat
  calc
    (∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B}, o.Y ∂P.dataMeasure) =
        ∫ o in E, o.Y ∂P.dataMeasure := by rfl
    _ = ∫ o in E, P.dataMeasure[(fun o : ClampObs J => o.Y) |
          MeasurableSpace.comap design inferInstance] o ∂P.dataMeasure :=
      (setIntegral_condExp hdesign.comap_le hY hEcond).symm
    _ = ∫ o in E, mu o.X o.A ∂P.dataMeasure :=
      setIntegral_congr_ae hE (hver.mono fun o ho _ => ho)
    _ = ∫ o, Set.indicator {o : ClampObs J | o.X = x}
        (fun o => B.indicator (mu x) o.A) o ∂P.dataMeasure := by
      rw [← integral_indicator hE]
      apply integral_congr_ae
      filter_upwards with o
      by_cases hx : o.X = x <;> by_cases ha : o.A ∈ B <;>
        simp [E, Set.indicator, hx, ha]
    _ = P.px x * ∫ a in Set.Icc (0 : ℝ) 1,
        P.pi x a * B.indicator (mu x) a := htreat
    _ = P.px x * ∫ a in B, mu x a * P.pi x a := by
      congr 1
      rw [← integral_indicator measurableSet_Icc, ← integral_indicator hB]
      apply integral_congr_ae
      filter_upwards with a
      by_cases ha : a ∈ B
      · have haI := hBIcc ha
        simp [Set.indicator_of_mem ha, haI, mul_comm]
      · by_cases haI : a ∈ Set.Icc (0 : ℝ) 1 <;>
          simp [Set.indicator_of_notMem ha, haI]

/-- [the stated clamp regression cond exp property holds](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel), [the specified `x₀` input](hyp:x₀). -/
theorem clampRegression_condExp {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (x₀ : Fin J) :
    P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance] =ᵐ[P.dataMeasure]
      clampRegressionExtension P ∘ fun o => (o.X, o.A) := by
  have hraw := (hmodel.holder x₀).2.2.1
  exact hraw.trans <| (clampRegressionExtension_ae_eq_mu P hmodel).symm

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
