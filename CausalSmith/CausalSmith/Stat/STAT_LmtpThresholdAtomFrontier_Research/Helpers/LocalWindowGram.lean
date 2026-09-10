/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Pushforward
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ShiftedPowerCoercivity

/-!
# Local-window population-law bridge

This module identifies the fixed-stratum treatment marginal with its declared
density law and transports integrals through that measure identity.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped ENNReal

noncomputable section

-- @node: measurable_clampObs_X
private lemma measurable_clampObs_X {J : ℕ} :
    Measurable (fun o : ClampObs J => o.X) := by
  exact measurable_fst.comp (Measurable.of_comap_le le_rfl)

-- @node: measurable_clampObs_A
private lemma measurable_clampObs_A {J : ℕ} :
    Measurable (fun o : ClampObs J => o.A) := by
  exact measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

/-- Unit local-window weight in a fixed stratum. -/
def localWindowWeight {J : ℕ} (x : Fin J) (delta h : ℝ) (o : ClampObs J) : ℝ :=
  if o.X = x ∧ scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1 then 1 else 0

/-- Monomial feature clipped outside the local window, so its global envelope
is one while its weighted Gram agrees with the total local Gram. -/
def localWindowFeature {J ell : ℕ} (delta h : ℝ) (j : Fin (ell + 1))
    (o : ClampObs J) : ℝ :=
  if scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1 then
    monomialVec ell (scaledDose delta h o) j else 0

/-- [the stated measurable local window weight property holds](goal) for [the specified `J` input](hyp:J), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma measurable_localWindowWeight {J : ℕ} (x : Fin J) (delta h : ℝ) :
    Measurable (localWindowWeight x delta h) := by
  have hu : Measurable (fun o : ClampObs J => scaledDose delta h o) :=
    (measurable_clampObs_A.sub measurable_const).div_const _
  apply Measurable.ite
  · exact (measurable_clampObs_X (J := J) (measurableSet_singleton x)).inter
      (hu measurableSet_Icc)
  · exact measurable_const
  · exact measurable_const

/-- [the stated measurable local window feature property holds](goal) for [the specified `J` input](hyp:J), [the specified `ell` input](hyp:ell), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `j` input](hyp:j). -/
lemma measurable_localWindowFeature {J ell : ℕ} (delta h : ℝ)
    (j : Fin (ell + 1)) : Measurable (localWindowFeature (J := J) delta h j) := by
  have hu : Measurable (fun o : ClampObs J => scaledDose delta h o) :=
    (measurable_clampObs_A.sub measurable_const).div_const _
  apply Measurable.ite
  · exact hu measurableSet_Icc
  · exact hu.pow_const _
  · exact measurable_const

/-- For [a stratum](hyp:x), [threshold](hyp:delta), and [bandwidth](hyp:h), [the local-window weight lies between zero and one for every observation](goal). -/
lemma localWindowWeight_mem_unit {J : ℕ} (x : Fin J) (delta h : ℝ) :
    ∀ o : ClampObs J, localWindowWeight x delta h o ∈ Set.Icc (0 : ℝ) 1 := by
  intro o
  by_cases ho : o.X = x ∧ 0 ≤ scaledDose delta h o ∧ scaledDose delta h o ≤ 1
  · simp [localWindowWeight, Set.mem_Icc, ho]
  · simp [localWindowWeight, Set.mem_Icc, ho]

/-- For [a polynomial degree](hyp:ell), [threshold](hyp:delta), [bandwidth](hyp:h), and [basis coordinate](hyp:j), [the local-window feature has absolute value at most one for every observation](goal). -/
lemma abs_localWindowFeature_le_one {J ell : ℕ} (delta h : ℝ)
    (j : Fin (ell + 1)) :
    ∀ o : ClampObs J, |localWindowFeature (J := J) delta h j o| ≤ 1 := by
  intro o
  by_cases hu : scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1
  · simp only [localWindowFeature, if_pos hu, monomialVec]
    rw [abs_of_nonneg (pow_nonneg hu.1 _)]
    exact pow_le_one₀ hu.1 hu.2
  · simp [localWindowFeature, hu]

/-- The treatment marginal inside a fixed stratum is its stratum mass times
the declared conditional treatment measure. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin). [This is the stated conclusion](goal).
-/
-- @node: stratumTreatmentMeasure_eq
lemma stratumTreatmentMeasure_eq {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin : ℝ}
    (hmodel : BridgeClampModel P kappa cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) :
    (P.dataMeasure.restrict {o : ClampObs J | o.X = x}).map (fun o => o.A) =
      ENNReal.ofReal (P.px x) • conditionalTreatmentMeasure P x := by
  letI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  have hpx : 0 ≤ P.px x := le_trans hpmin.le (hmodel.stratumMass x).2
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
  let μ := (P.dataMeasure.restrict {o : ClampObs J | o.X = x}).map (fun o => o.A)
  let ν := ENNReal.ofReal (P.px x) • conditionalTreatmentMeasure P x
  have hcondFinite : IsFiniteMeasure (conditionalTreatmentMeasure P x) := by
    refine ⟨?_⟩
    simp only [conditionalTreatmentMeasure]
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    exact lt_of_le_of_lt (lintegral_mono fun a => Real.ofReal_le_enorm _)
      hpiInt.hasFiniteIntegral
  letI : IsFiniteMeasure (conditionalTreatmentMeasure P x) := hcondFinite
  have hνFinite : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    dsimp [ν]
    change ENNReal.ofReal (P.px x) *
      (conditionalTreatmentMeasure P x) Set.univ < ⊤
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  letI : IsFiniteMeasure ν := hνFinite
  have hμae : ∀ᵐ a ∂μ, a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_map_iff measurable_clampObs_A.aemeasurable]
    · exact ae_restrict_of_ae hmodel.treatmentSupport
    · exact measurableSet_Icc
  have hνae : ∀ᵐ a ∂ν, a ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [ν, conditionalTreatmentMeasure]
    exact Measure.smul_absolutelyContinuous.ae_le
      ((withDensity_absolutelyContinuous _ _).ae_le
        (ae_restrict_mem measurableSet_Icc))
  change μ = ν
  rw [← Measure.restrict_eq_self_of_ae_mem hμae,
    ← Measure.restrict_eq_self_of_ae_mem hνae]
  apply (Measure.restrict_congr_meas measurableSet_Icc).2
  intro t ht htm
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ t) (measure_ne_top ν t)).mp
  change μ.real t = ν.real t
  have hsource : μ.real t =
      P.dataMeasure.real {o : ClampObs J | o.X = x ∧ o.A ∈ t} := by
    simp only [μ, measureReal_def]
    rw [Measure.map_apply measurable_clampObs_A htm,
      Measure.restrict_apply (measurable_clampObs_A htm)]
    congr 2
    ext o
    simp [and_comm]
  have htarget : (conditionalTreatmentMeasure P x).real t =
      ∫ a in t, P.pi x a := by
    have hpiT : Integrable (P.pi x) (volume.restrict t) :=
      hpiInt.mono_measure (Measure.restrict_mono_set volume ht)
    simp only [conditionalTreatmentMeasure, measureReal_def]
    rw [withDensity_apply _ htm]
    rw [Measure.restrict_restrict htm,
      inter_eq_self_of_subset_left ht]
    rw [← ofReal_integral_eq_lintegral_ofReal hpiT]
    · rw [ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae ((hmodel.condDensity.2.1 x).filter_mono
        (ae_mono (Measure.restrict_mono_set volume ht)))
    · exact (hmodel.condDensity.2.1 x).filter_mono
        (ae_mono (Measure.restrict_mono_set volume ht))
  rw [hsource]
  have hlaw := (hmodel.condDensity.2.2 x).2 t htm ht
  rw [hlaw, show ν.real t = P.px x * (conditionalTreatmentMeasure P x).real t by
    simp [ν, measureReal_def, hpx]]
  rw [htarget]

/-- Integration form of `stratumTreatmentMeasure_eq`. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hf` condition](hyp:hf). [This is the stated conclusion](goal).
-/
-- @node: stratumTreatment_integral_eq
lemma stratumTreatment_integral_eq {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin : ℝ}
    (hmodel : BridgeClampModel P kappa cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) (f : ℝ → ℝ)
    (hf : Integrable f (conditionalTreatmentMeasure P x)) :
    (∫ o, Set.indicator {o : ClampObs J | o.X = x} (fun o => f o.A) o
        ∂P.dataMeasure) =
      P.px x * ∫ a, f a ∂conditionalTreatmentMeasure P x := by
  have hX : MeasurableSet {o : ClampObs J | o.X = x} :=
    measurable_clampObs_X (measurableSet_singleton x)
  have hpx : 0 ≤ P.px x := le_trans hpmin.le (hmodel.stratumMass x).2
  rw [integral_indicator hX]
  rw [← integral_map measurable_clampObs_A.aemeasurable]
  · rw [stratumTreatmentMeasure_eq P hmodel hkappa hcplus hpmin x,
      integral_smul_measure, ENNReal.toReal_ofReal hpx]
    rfl
  · rw [stratumTreatmentMeasure_eq P hmodel hkappa hcplus hpmin x]
    exact (hf.smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable

/-- Integration against the declared conditional treatment measure is
integration against its real density on `[0,1]`. The result uses [the `hmodel` condition](hyp:hmodel). [This is the stated conclusion](goal).
-/
-- @node: conditionalTreatment_integral_eq_density
lemma conditionalTreatment_integral_eq_density {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin : ℝ}
    (hmodel : BridgeClampModel P kappa cminus cplus pmin)
    (x : Fin J) (f : ℝ → ℝ) :
    (∫ a, f a ∂conditionalTreatmentMeasure P x) =
      ∫ a in Set.Icc (0 : ℝ) 1, P.pi x a * f a := by
  have hpiMeas : AEMeasurable (fun a : ℝ => ENNReal.ofReal (P.pi x a))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
      (hmodel.condDensity.1 x)).ennreal_ofReal
  rw [conditionalTreatmentMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hpiMeas]
  · apply integral_congr_ae
    filter_upwards [hmodel.condDensity.2.1 x] with a ha
    simp [ENNReal.toReal_ofReal ha, smul_eq_mul, mul_comm]
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

/-- Positive bandwidth identifies the scaled unit window with the original
treatment interval. The result uses [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
-- @node: scaledDose_mem_Icc_iff
lemma scaledDose_mem_Icc_iff {J : ℕ} {delta h : ℝ} (hh : 0 < h)
    (o : ClampObs J) :
    scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1 ↔
      o.A ∈ Set.Icc delta (delta + h) := by
  simp only [scaledDose, Set.mem_Icc]
  constructor
  · intro hu
    constructor
    · exact sub_nonneg.mp (((div_nonneg_iff).mp hu.1 |>.resolve_right
        (fun hneg => (not_lt_of_ge hneg.2 hh))).1)
    · have := (div_le_iff₀ hh).mp hu.2
      linarith
  · intro ha
    constructor
    · exact div_nonneg (sub_nonneg.mpr ha.1) hh.le
    · exact (div_le_iff₀ hh).mpr (by linarith)

/-- The population local-window mass is the stratum mass times the declared
density integral over that window. The result uses [the `hmodel` condition](hyp:hmodel), [the `hh` condition](hyp:hh), [the `hwindow` condition](hyp:hwindow). [This is the stated conclusion](goal).
-/
-- @node: localWindowWeight_integral_eq
lemma localWindowWeight_integral_eq {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (x : Fin J) (hh : 0 < h)
    (hwindow : Set.Icc delta (delta + h) ⊆ Set.Icc (0 : ℝ) 1) :
    (∫ o, localWindowWeight x delta h o ∂P.dataMeasure) =
      P.px x * ∫ a in Set.Icc delta (delta + h), P.pi x a := by
  let E : Set (ClampObs J) := {o | o.X = x ∧ o.A ∈ Set.Icc delta (delta + h)}
  have hE : MeasurableSet E :=
    (measurable_clampObs_X (measurableSet_singleton x)).inter
      (measurable_clampObs_A measurableSet_Icc)
  have hfun : localWindowWeight x delta h = Set.indicator E (fun _ => (1 : ℝ)) := by
    funext o
    by_cases ho : o.X = x ∧ o.A ∈ Set.Icc delta (delta + h)
    · rw [Set.indicator_of_mem (show o ∈ E from ho)]
      simp [localWindowWeight, ho.1, (scaledDose_mem_Icc_iff hh o).2 ho.2]
    · rw [Set.indicator_of_notMem (show o ∉ E from ho)]
      have hscaled : ¬(o.X = x ∧ scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1) :=
        fun hz => ho ⟨hz.1, (scaledDose_mem_Icc_iff hh o).1 hz.2⟩
      change (if o.X = x ∧ scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1
        then 1 else 0) = 0
      exact if_neg hscaled
  rw [hfun, integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
  exact (hmodel.condDensity.2.2 x).2 (Set.Icc delta (delta + h))
    measurableSet_Icc hwindow

/-- A positive interval captures a fixed positive fraction of the power mass
at its upper endpoint. The result uses [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
-- @node: integral_rpow_window_lower
lemma integral_rpow_window_lower {delta h kappa : ℝ}
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hkappa : 0 ≤ kappa) :
    h / 2 * ((delta + h) / 2) ^ kappa ≤
      ∫ a in delta..delta + h, a ^ kappa := by
  let m := delta + h / 2
  have hdm : delta ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ delta + h := by dsimp [m]; linarith
  have hm0 : 0 ≤ m := by dsimp [m]; linarith
  have hb2 : (delta + h) / 2 ≤ m := by dsimp [m]; linarith
  have hconst :
      (∫ _a in m..delta + h, ((delta + h) / 2) ^ kappa) ≤
        ∫ a in m..delta + h, a ^ kappa := by
    apply intervalIntegral.integral_mono_on hmb
    · exact intervalIntegrable_const
    · exact intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)
    · intro a ha
      exact Real.rpow_le_rpow (by positivity) (hb2.trans ha.1) hkappa
  have hsub : (∫ a in m..delta + h, a ^ kappa) ≤
      ∫ a in delta..delta + h, a ^ kappa := by
    apply intervalIntegral.integral_mono_interval hdm hmb le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      exact Real.rpow_nonneg (hdelta.trans ha.1.le) _
    · apply Continuous.intervalIntegrable
      fun_prop
  calc
    h / 2 * ((delta + h) / 2) ^ kappa =
        ∫ _a in m..delta + h, ((delta + h) / 2) ^ kappa := by
      rw [intervalIntegral.integral_const]
      dsimp [m]
      ring
    _ ≤ ∫ a in m..delta + h, a ^ kappa := hconst
    _ ≤ ∫ a in delta..delta + h, a ^ kappa := hsub

/-- The local stratum-window probability has the uniform polynomial lower
bound obtained by integrating over the upper half of the window. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
-- @node: localWindowWeight_integral_lower
lemma localWindowWeight_integral_lower {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcminus : 0 < cminus) (hcplus : 0 ≤ cplus)
    (hpmin : 0 < pmin) (x : Fin J) (hdelta : 0 ≤ delta) (hh : 0 < h)
    (hupper : delta + h ≤ 1) :
    pmin * (cminus * ((delta + h) / 2) ^ kappa * (h / 2)) ≤
      ∫ o, localWindowWeight x delta h o ∂P.dataMeasure := by
  let T : Set ℝ := Set.Icc delta (delta + h)
  have hT : T ⊆ Set.Icc (0 : ℝ) 1 := by
    intro a ha
    exact ⟨hdelta.trans ha.1, ha.2.trans hupper⟩
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
  have hpiT : IntegrableOn (P.pi x) T volume :=
    hpiInt.mono_measure (Measure.restrict_mono_set volume hT)
  have hthinT : ∀ᵐ a ∂volume.restrict T, cminus * a ^ kappa ≤ P.pi x a :=
    ((hmodel.thinning x).filter_mono
      (ae_mono (Measure.restrict_mono_set volume hT))).mono
        (fun _ ha => ha.1)
  have hpowT : IntegrableOn (fun a : ℝ => a ^ kappa) T volume := by
    dsimp [T]
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)
  have hlower : cminus * (h / 2 * ((delta + h) / 2) ^ kappa) ≤
      ∫ a in T, P.pi x a := by
    calc
      cminus * (h / 2 * ((delta + h) / 2) ^ kappa) ≤
          cminus * (∫ a in delta..delta + h, a ^ kappa) := by
        exact mul_le_mul_of_nonneg_left
          (integral_rpow_window_lower hdelta hh hkappa) hcminus.le
      _ = ∫ a in T, cminus * a ^ kappa := by
        dsimp [T]
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_const_mul]
      _ ≤ ∫ a in T, P.pi x a :=
        integral_mono_ae (hpowT.const_mul cminus) hpiT hthinT
  rw [localWindowWeight_integral_eq P hmodel x hh hT]
  have hpx : pmin ≤ P.px x := (hmodel.stratumMass x).2
  have hfactor : 0 ≤ cminus * ((delta + h) / 2) ^ kappa * (h / 2) := by
    positivity
  calc
    pmin * (cminus * ((delta + h) / 2) ^ kappa * (h / 2)) ≤
        P.px x * (cminus * ((delta + h) / 2) ^ kappa * (h / 2)) :=
      mul_le_mul_of_nonneg_right hpx hfactor
    _ ≤ P.px x * ∫ a in T, P.pi x a := by
      have hlower' : cminus * ((delta + h) / 2) ^ kappa * (h / 2) ≤
          ∫ a in T, P.pi x a := by
        nlinarith [hlower]
      exact mul_le_mul_of_nonneg_left hlower' (hpmin.le.trans hpx)

/-- A local-window Gram entry is the corresponding density-weighted monomial
integral over the original treatment window. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hh` condition](hyp:hh), [the `hwindow` condition](hyp:hwindow). [This is the stated conclusion](goal).
-/
-- @node: localWindowGramEntry_integral_eq
lemma localWindowGramEntry_integral_eq {J ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) (hh : 0 < h)
    (hwindow : Set.Icc delta (delta + h) ⊆ Set.Icc (0 : ℝ) 1)
    (j k : Fin (ell + 1)) :
    (∫ o, localWindowWeight x delta h o *
        localWindowFeature delta h j o * localWindowFeature delta h k o
        ∂P.dataMeasure) =
      P.px x * ∫ a in Set.Icc delta (delta + h),
        P.pi x a * monomialVec ell ((a - delta) / h) j *
          monomialVec ell ((a - delta) / h) k := by
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
  let f : ℝ → ℝ := fun a =>
    if (a - delta) / h ∈ Set.Icc (0 : ℝ) 1 then
      monomialVec ell ((a - delta) / h) j *
        monomialVec ell ((a - delta) / h) k else 0
  have hfmeas : Measurable f := by
    dsimp [f]
    apply Measurable.ite
    · exact (((measurable_id.sub measurable_const).div_const _)
        measurableSet_Icc)
    · exact (((measurable_id.sub measurable_const).div_const _).pow_const _).mul
        (((measurable_id.sub measurable_const).div_const _).pow_const _)
    · exact measurable_const
  have hfbound : ∀ a, |f a| ≤ 1 := by
    intro a
    by_cases ha : (a - delta) / h ∈ Set.Icc (0 : ℝ) 1
    · simp only [f, if_pos ha, monomialVec, abs_mul, abs_pow]
      have habs : |(a - delta) / h| ≤ 1 := by
        rw [abs_of_nonneg ha.1]
        exact ha.2
      calc
        |(a - delta) / h| ^ (j : ℕ) * |(a - delta) / h| ^ (k : ℕ) ≤
            1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg _) habs)
              (pow_le_one₀ (abs_nonneg _) habs)
              (pow_nonneg (abs_nonneg _) _) (by norm_num)
        _ = 1 := by norm_num
    · simp only [f, if_neg ha, abs_zero]
      norm_num
  have hcondFinite : IsFiniteMeasure (conditionalTreatmentMeasure P x) := by
    refine ⟨?_⟩
    simp only [conditionalTreatmentMeasure]
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    exact lt_of_le_of_lt (lintegral_mono fun a => Real.ofReal_le_enorm _)
      hpiInt.hasFiniteIntegral
  letI : IsFiniteMeasure (conditionalTreatmentMeasure P x) := hcondFinite
  have hfint : Integrable f (conditionalTreatmentMeasure P x) :=
    Integrable.of_bound hfmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hfbound a)
  have hfun : (fun o => localWindowWeight x delta h o *
      localWindowFeature delta h j o * localWindowFeature delta h k o) =
      Set.indicator {o : ClampObs J | o.X = x} (fun o => f o.A) := by
        funext o
        by_cases hx : o.X = x
        · by_cases hu : scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1
          · rw [show localWindowWeight x delta h o = 1 by
                rw [localWindowWeight, if_pos ⟨hx, hu⟩],
              show localWindowFeature delta h j o = monomialVec ell
                  (scaledDose delta h o) j by
                rw [localWindowFeature, if_pos hu],
              show localWindowFeature delta h k o = monomialVec ell
                  (scaledDose delta h o) k by
                rw [localWindowFeature, if_pos hu],
              Set.indicator_of_mem (show o ∈ {o : ClampObs J | o.X = x} from hx)]
            change (1 * monomialVec ell ((o.A - delta) / h) j *
              monomialVec ell ((o.A - delta) / h) k) = f o.A
            have hu' : (o.A - delta) / h ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [scaledDose] using hu
            dsimp [f]
            rw [if_pos hu']
            ring
          · rw [show localWindowWeight x delta h o = 0 by
                rw [localWindowWeight, if_neg (fun H => hu H.2)],
              zero_mul, zero_mul,
              Set.indicator_of_mem (show o ∈ {o : ClampObs J | o.X = x} from hx)]
            have hu' : ¬((o.A - delta) / h ∈ Set.Icc (0 : ℝ) 1) := by
              simpa [scaledDose] using hu
            dsimp [f]
            rw [if_neg hu']
        · simp [localWindowWeight, hx]
  rw [hfun]
  rw [stratumTreatment_integral_eq P hmodel.toBridge hkappa hcplus hpmin x f hfint,
    conditionalTreatment_integral_eq_density P hmodel.toBridge x f]
  congr 1
  rw [← MeasureTheory.integral_indicator
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)),
    ← MeasureTheory.integral_indicator
      (measurableSet_Icc : MeasurableSet (Set.Icc delta (delta + h)))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro a
  by_cases hw : a ∈ Set.Icc delta (delta + h)
  · have hu := (scaledDose_mem_Icc_iff (J := J) hh ⟨x, a, 0⟩).2 hw
    have hu' : (a - delta) / h ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [scaledDose] using hu
    have ha01 : a ∈ Set.Icc (0 : ℝ) 1 := hwindow hw
    rw [Set.indicator_of_mem ha01, Set.indicator_of_mem hw]
    dsimp [f]
    rw [if_pos hu']
    ring
  · have hu : ¬((a - delta) / h ∈ Set.Icc (0 : ℝ) 1) := by
      intro hu
      exact hw ((scaledDose_mem_Icc_iff (J := J) hh ⟨x, a, 0⟩).1 hu)
    rw [Set.indicator_of_notMem hw]
    by_cases ha01 : a ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ha01]
      dsimp [f]
      rw [if_neg hu, mul_zero]
    · rw [Set.indicator_of_notMem ha01]

/-- The population local-window Gram dominates `lambdaStar` times its own
local mass, using only the two-sided polynomial density envelope. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper). [This is the stated conclusion](goal).
-/
-- @node: localWindow_populationGram_coercive
lemma localWindow_populationGram_coercive {J ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcminus : 0 < cminus) (hcplus : 0 < cplus)
    (hpmin : 0 < pmin) (x : Fin J) (hdelta : 0 ≤ delta) (hh : 0 < h)
    (hupper : delta + h ≤ 1) (v : Fin (ell + 1) → ℝ) :
    lambdaStar ell kappa cminus cplus *
        (∫ o, localWindowWeight x delta h o ∂P.dataMeasure) *
        (∑ j, (v j) ^ 2) ≤
      ∑ j, ∑ k, v j * v k *
        ∫ o, localWindowWeight x delta h o *
          localWindowFeature (J := J) delta h j o *
          localWindowFeature (J := J) delta h k o ∂P.dataMeasure := by
  let T : Set ℝ := Set.Icc delta (delta + h)
  let poly : ℝ → ℝ := fun a => ∑ j, v j * ((a - delta) / h) ^ (j : ℕ)
  have hT : T ⊆ Set.Icc (0 : ℝ) 1 := by
    intro a ha
    exact ⟨hdelta.trans ha.1, ha.2.trans hupper⟩
  have hpx : 0 ≤ P.px x := hpmin.le.trans (hmodel.stratumMass x).2
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
            (Real.rpow_le_one ha.1 ha.2 hkappa) hcplus.le
  have hpiT : IntegrableOn (P.pi x) T volume :=
    hpiInt.mono_measure (Measure.restrict_mono_set volume hT)
  have hpowT : IntegrableOn (fun a : ℝ => a ^ kappa) T volume := by
    dsimp [T]
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)
  have hmassUpper :
      (∫ o, localWindowWeight x delta h o ∂P.dataMeasure) ≤
        P.px x * (cplus * ∫ a in T, a ^ kappa) := by
    rw [localWindowWeight_integral_eq P hmodel x hh hT]
    apply mul_le_mul_of_nonneg_left _ hpx
    calc
      (∫ a in T, P.pi x a) ≤ ∫ a in T, cplus * a ^ kappa := by
        apply integral_mono_ae hpiT (hpowT.const_mul cplus)
        exact ((hmodel.thinning x).filter_mono
          (ae_mono (Measure.restrict_mono_set volume hT))).mono (fun _ ha => ha.2)
      _ = cplus * ∫ a in T, a ^ kappa := by rw [integral_const_mul]
  have hpolyMeas : AEStronglyMeasurable poly (volume.restrict T) := by
    apply Measurable.aestronglyMeasurable
    dsimp [poly]
    fun_prop
  have hpolyBound : ∀ᵐ a ∂volume.restrict T,
      ‖poly a ^ 2‖ ≤ (∑ j, |v j|) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    have hu : (a - delta) / h ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr ha.1) hh.le
      · exact (div_le_iff₀ hh).2 (by linarith [ha.2])
    have habs : |poly a| ≤ ∑ j, |v j| := by
      dsimp [poly]
      calc
        |∑ j, v j * ((a - delta) / h) ^ (j : ℕ)| ≤
            ∑ j, |v j * ((a - delta) / h) ^ (j : ℕ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |v j| := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (by
            rw [abs_pow, abs_of_nonneg hu.1]
            exact pow_le_one₀ hu.1 hu.2)
    have hsumNonneg : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [Real.norm_eq_abs, abs_sq, sq_le_sq]
    simpa [abs_of_nonneg hsumNonneg] using habs
  have hpolyPi : IntegrableOn (fun a => poly a ^ 2 * P.pi x a) T volume :=
    hpiT.bdd_mul (hpolyMeas.pow 2) hpolyBound
  have hquadIdentity :
      (∑ j, ∑ k, v j * v k *
        ∫ o, localWindowWeight x delta h o *
          localWindowFeature (J := J) delta h j o *
          localWindowFeature (J := J) delta h k o ∂P.dataMeasure) =
        P.px x * ∫ a in T, poly a ^ 2 * P.pi x a := by
    simp_rw [localWindowGramEntry_integral_eq P hmodel hkappa hcplus.le hpmin x hh hT]
    simp_rw [show ∀ (j k : Fin (ell + 1)) (I : ℝ),
        v j * v k * (P.px x * I) = P.px x * (v j * v k * I) by
      intros; ring]
    simp_rw [← Finset.mul_sum]
    congr 1
    have hterm (j k : Fin (ell + 1)) : IntegrableOn
        (fun a => v j * v k * (P.pi x a * monomialVec ell ((a - delta) / h) j *
          monomialVec ell ((a - delta) / h) k)) T volume := by
      have hb : AEStronglyMeasurable (fun a => v j * v k *
          (monomialVec ell ((a - delta) / h) j *
            monomialVec ell ((a - delta) / h) k)) (volume.restrict T) := by
        simp only [monomialVec]
        fun_prop
      have hbound : ∀ᵐ a ∂volume.restrict T,
          ‖v j * v k * (monomialVec ell ((a - delta) / h) j *
            monomialVec ell ((a - delta) / h) k)‖ ≤ |v j * v k| := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
        have hu : (a - delta) / h ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · exact div_nonneg (sub_nonneg.mpr ha.1) hh.le
          · exact (div_le_iff₀ hh).2 (by linarith [ha.2])
        rw [Real.norm_eq_abs]
        calc
          |v j * v k * (monomialVec ell ((a - delta) / h) j *
              monomialVec ell ((a - delta) / h) k)| ≤ |v j * v k| * 1 := by
            simp only [monomialVec, abs_mul, abs_pow, abs_of_nonneg hu.1]
            gcongr
            have hj : ((a - delta) / h) ^ (j : ℕ) ≤ 1 := pow_le_one₀ hu.1 hu.2
            have hk : ((a - delta) / h) ^ (k : ℕ) ≤ 1 := pow_le_one₀ hu.1 hu.2
            simpa using mul_le_mul hj hk (pow_nonneg hu.1 _) (by norm_num : (0 : ℝ) ≤ 1)
          _ = |v j * v k| := mul_one _
      have hi := hpiT.mul_bdd hb hbound
      apply hi.congr
      filter_upwards with a
      ring
    rw [show (∫ a in T, poly a ^ 2 * P.pi x a) =
        ∫ a in T, ∑ j, ∑ k, v j * v k *
          (P.pi x a * monomialVec ell ((a - delta) / h) j *
            monomialVec ell ((a - delta) / h) k) by
      apply integral_congr_ae
      filter_upwards with a
      dsimp [poly, monomialVec]
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    simp_rw [← integral_const_mul]
    have hinner (j : Fin (ell + 1)) : IntegrableOn
        (fun a => ∑ k, v j * v k *
          (P.pi x a * monomialVec ell ((a - delta) / h) j *
            monomialVec ell ((a - delta) / h) k)) T volume :=
      integrable_finsetSum Finset.univ (fun k _ => hterm j k)
    rw [integral_finsetSum Finset.univ (fun j _ => hinner j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum Finset.univ (fun k _ => hterm j k)]
  have hthinLower :
      P.px x * (cminus * ∫ a in T, poly a ^ 2 * a ^ kappa) ≤
        P.px x * ∫ a in T, poly a ^ 2 * P.pi x a := by
    apply mul_le_mul_of_nonneg_left _ hpx
    rw [← integral_const_mul]
    apply integral_mono_ae
    · simpa [mul_assoc] using
        (hpowT.bdd_mul (hpolyMeas.pow 2) hpolyBound).const_mul cminus
    · exact hpolyPi
    · filter_upwards [ae_restrict_mem measurableSet_Icc,
          (hmodel.thinning x).filter_mono
            (ae_mono (Measure.restrict_mono_set volume hT))] with a ha hthin
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hthin.1 (sq_nonneg (poly a))
  have hscaled :=
    CausalSmith.Stat.LmtpThresholdAtomFrontier.lambdaStar_scaled_power_window_coercive
      ell hkappa hcminus hcplus hdelta hh v
  have hscaledT :
      lambdaStar ell kappa cminus cplus * cplus * (∫ a in T, a ^ kappa) *
          (∑ j, (v j) ^ 2) ≤
        cminus * ∫ a in T, poly a ^ 2 * a ^ kappa := by
    dsimp [T, poly]
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith)]
    simpa [mul_comm] using hscaled
  rw [hquadIdentity]
  calc
    lambdaStar ell kappa cminus cplus *
          (∫ o, localWindowWeight x delta h o ∂P.dataMeasure) *
          (∑ j, (v j) ^ 2) ≤
        P.px x * (lambdaStar ell kappa cminus cplus * cplus *
          (∫ a in T, a ^ kappa) * (∑ j, (v j) ^ 2)) := by
      have hlam : 0 ≤ lambdaStar ell kappa cminus cplus :=
        (lambdaStar_pos ell hkappa hcminus hcplus).le
      calc
        _ ≤ lambdaStar ell kappa cminus cplus *
            (P.px x * (cplus * ∫ a in T, a ^ kappa)) *
              (∑ j, (v j) ^ 2) := by
          gcongr
        _ = _ := by ring
    _ ≤ P.px x * (cminus * ∫ a in T, poly a ^ 2 * a ^ kappa) :=
      mul_le_mul_of_nonneg_left hscaledT hpx
    _ ≤ P.px x * ∫ a in T, poly a ^ 2 * P.pi x a := hthinLower

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
