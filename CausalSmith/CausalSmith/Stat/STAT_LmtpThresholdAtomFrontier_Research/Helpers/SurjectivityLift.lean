/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TCausalBridge
import Causalean.Mathlib.Probability.Kernel.ParameterizedKernelQuantileRealization
import Mathlib.Probability.Kernel.Disintegration.Integral

/-! # Quantile lifts of observed clamp laws -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set
open scoped ENNReal unitInterval

noncomputable section

open Causalean.Mathlib.Probability.Kernel.ParameterizedKernelQuantileRealization

private lemma measurable_clampObs_of_design_outcome {J : ℕ} :
    Measurable (fun p : (Fin J × ℝ) × ℝ => ClampObs.mk p.1.1 p.1.2 p.2) := by
  rw [measurable_comap_iff]
  fun_prop

private lemma measurable_clampUnit : Measurable clampUnit := by
  unfold clampUnit
  fun_prop

private lemma continuous_clampUnit' : Continuous clampUnit := by
  unfold clampUnit
  fun_prop

private lemma clampUnit_in_unit (y : ℝ) : clampUnit y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold clampUnit
  constructor <;> simp

private lemma map_prod_realization_eq_compProd
    {S T U : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (ν : Measure S) [SFinite ν] (ρ : Measure U) [SFinite ρ]
    (κ : ProbabilityTheory.Kernel S T) [ProbabilityTheory.IsSFiniteKernel κ]
    (q : S → U → T) (hq : Measurable (Function.uncurry q))
    (hlaw : ∀ s, Measure.map (q s) ρ = κ s) :
    Measure.map (fun p : S × U => (p.1, q p.1 p.2)) (ν.prod ρ) = ν.compProd κ := by
  have hmap : Measurable (fun p : S × U => (p.1, q p.1 p.2)) := by
    exact measurable_fst.prodMk hq
  ext A hA
  rw [Measure.map_apply hmap hA,
    Measure.compProd_apply hA, Measure.prod_apply (hmap hA)]
  apply lintegral_congr
  intro s
  rw [← hlaw s, Measure.map_apply hq.of_uncurry_left (measurable_prodMk_left hA)]
  rfl

/-- A measurable bounded conditional-regression version can be realized by a
single independent uniform latent variable while preserving the observed law. This uses
[a probability law](hyp:hprob), [bounded outcomes](hyp:hout), [positive stratum masses](hyp:hmass_pos),
[a measurable bounded regression](hyp:m,hm,hm_unit), [the conditional-mean identity](hyp:hcond), and
[stratumwise continuity](hyp:hm_cont); [such a full-data lift exists](goal). -/
lemma exists_fullData_quantile_lift
    {J : ℕ} (P : ClampLaw J) (deltaBar : ℝ)
    (hprob : IsProbabilityMeasure P.dataMeasure)
    (hout : ∀ᵐ o ∂P.dataMeasure, o.Y ∈ Set.Icc (0 : ℝ) 1)
    (hmass_pos : ∀ x : Fin J,
      0 < (P.dataMeasure.map (fun o => o.X)).real {x})
    (m : Fin J × ℝ → ℝ) (hm : Measurable m)
    (hm_unit : ∀ d, m d ∈ Set.Icc (0 : ℝ) 1)
    (hcond : P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => m (o.X, o.A))
    (hm_cont : ∀ x : Fin J,
      ContinuousOn (fun a => m (x, a)) (Set.Icc (0 : ℝ) deltaBar)) :
    ∃ PF : FullDataLaw J,
      PF.observedMargin = P ∧ LatentResponseConsistency PF ∧
        LatentExchangeability PF ∧ FullDataResponseContinuity PF deltaBar := by
  let _ := hprob
  let D : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
  let Y : ClampObs J → ℝ := fun o => o.Y
  have hD : Measurable D := clampDesign_measurable
  have hY : Measurable Y := clampOutcome_measurable
  let ν : Measure (Fin J × ℝ) := P.dataMeasure.map D
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hD.aemeasurable
  let κraw : ProbabilityTheory.Kernel (Fin J × ℝ) ℝ :=
    ProbabilityTheory.condDistrib Y D P.dataMeasure
  letI : ProbabilityTheory.IsMarkovKernel κraw := inferInstance
  let κ0 : ProbabilityTheory.Kernel (Fin J × ℝ) ℝ := κraw.map clampUnit
  letI : ProbabilityTheory.IsMarkovKernel κ0 :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map κraw measurable_clampUnit
  let fiberMean : Fin J × ℝ → ℝ := fun d => ∫ y, y ∂κ0 d
  have hκraw_κ0 : (κraw : (Fin J × ℝ) → Measure ℝ) =ᵐ[ν] κ0 := by
    have hclamp : (fun o : ClampObs J => clampUnit (Y o)) =ᵐ[P.dataMeasure] Y := by
      filter_upwards [hout] with o ho
      simp only [Y]
      unfold clampUnit
      simp [ho.1, ho.2]
    have hc : (ProbabilityTheory.condDistrib (clampUnit ∘ Y) D P.dataMeasure :
          ProbabilityTheory.Kernel (Fin J × ℝ) ℝ) =ᵐ[ν]
        (ProbabilityTheory.condDistrib Y D P.dataMeasure).map clampUnit :=
      ProbabilityTheory.condDistrib_comp (μ := P.dataMeasure)
        (X := D) hY.aemeasurable measurable_clampUnit
    have heq : ProbabilityTheory.condDistrib (clampUnit ∘ Y) D P.dataMeasure = κraw :=
      ProbabilityTheory.condDistrib_congr_left hclamp
    rw [heq] at hc
    simpa only [ν, κ0, κraw] using hc
  have hfiber_meas : Measurable fiberMean := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  have hfiber_ae : fiberMean =ᵐ[ν] m := by
    have hce := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
      hD hY.aemeasurable stronglyMeasurable_id
      (Integrable.of_bound hY.aestronglyMeasurable 1 <| hout.mono fun o ho => by
        change |o.Y| ≤ 1
        exact abs_le.2 ⟨by linarith [ho.1], ho.2⟩)
    have hraw : (fun o => ∫ y, y ∂κraw (D o)) =ᵐ[P.dataMeasure]
        fun o => m (D o) := hce.symm.trans hcond
    have hzero : (fun d => ∫ y, y ∂κraw d) =ᵐ[ν] fiberMean :=
      hκraw_κ0.mono fun d hd => by simp only [fiberMean, hd]
    have hpull : (fun o => fiberMean (D o)) =ᵐ[P.dataMeasure] fun o => m (D o) :=
      (hzero.comp_tendsto (Measure.tendsto_ae_map hD.aemeasurable)).symm.trans hraw
    exact (MeasureTheory.ae_map_iff hD.aemeasurable
      (measurableSet_eq_fun hfiber_meas hm)).mpr hpull
  let bad : Set (Fin J × ℝ) := {d | fiberMean d ≠ m d}
  have hbad : MeasurableSet bad := (measurableSet_eq_fun hfiber_meas hm).compl
  let κdirac : ProbabilityTheory.Kernel (Fin J × ℝ) ℝ :=
    ProbabilityTheory.Kernel.deterministic m hm
  letI : ProbabilityTheory.IsMarkovKernel κdirac := inferInstance
  let κ : ProbabilityTheory.Kernel (Fin J × ℝ) ℝ :=
    ProbabilityTheory.Kernel.piecewise hbad κdirac κ0
  letI : ProbabilityTheory.IsMarkovKernel κ := inferInstance
  have hκ_ae : (κ : (Fin J × ℝ) → Measure ℝ) =ᵐ[ν] κ0 := by
    filter_upwards [hfiber_ae] with d hd
    simp [κ, bad, ProbabilityTheory.Kernel.piecewise_apply, hd]
  have hκ_support : SupportedOnUnitInterval κ := by
    intro d
    by_cases hd : d ∈ bad
    · rw [ProbabilityTheory.Kernel.piecewise_apply, if_pos hd]
      rw [ProbabilityTheory.Kernel.deterministic_apply]
      simp [hm_unit d]
    · rw [ProbabilityTheory.Kernel.piecewise_apply, if_neg hd]
      simp only [κ, κ0]
      rw [ProbabilityTheory.Kernel.map_apply' κraw measurable_clampUnit d measurableSet_Icc]
      have hpre : clampUnit ⁻¹' Set.Icc (0 : ℝ) 1 = Set.univ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_univ, iff_true]
        exact clampUnit_in_unit y
      rw [hpre]
      haveI : IsProbabilityMeasure (κraw d) := inferInstance
      exact measure_univ
  have hκ_mean : ∀ d, (∫ y, y ∂κ d) = m d := by
    intro d
    by_cases hd : d ∈ bad
    · rw [ProbabilityTheory.Kernel.integral_piecewise, if_pos hd]
      simp [κ, κdirac]
    · rw [ProbabilityTheory.Kernel.integral_piecewise, if_neg hd]
      exact not_ne_iff.mp hd
  let q : (Fin J × ℝ) → unitInterval → ℝ := fun d u => kernelUnitQuantile κ d u
  have hq : Measurable (Function.uncurry q) := by
    exact measurable_subtype_coe.comp (measurable_kernelUnitQuantile κ)
  have hqlaw : ∀ d, Measure.map (q d) volume = κ d := by
    intro d
    exact map_kernelUnitQuantile κ hκ_support d
  let base : Measure ((Fin J × ℝ) × unitInterval) := ν.prod volume
  letI : IsProbabilityMeasure base := inferInstance
  let H : ((Fin J × ℝ) × unitInterval) → (Fin J × ℝ) × ℝ :=
    fun p => (p.1, q p.1 p.2)
  have hH : Measurable H := measurable_fst.prodMk hq
  have hbase_joint : Measure.map H base = ν.compProd κ := by
    exact map_prod_realization_eq_compProd ν volume κ q hq hqlaw
  have hκraw_joint : ν.compProd κraw = Measure.map (fun o => (D o, Y o)) P.dataMeasure :=
    ProbabilityTheory.compProd_map_condDistrib hY.aemeasurable
  have hκraw_κ : (κraw : (Fin J × ℝ) → Measure ℝ) =ᵐ[ν] κ :=
    hκraw_κ0.trans hκ_ae.symm
  have hjoint : Measure.map H base = Measure.map (fun o => (D o, Y o)) P.dataMeasure := by
    rw [hbase_joint, Measure.compProd_congr hκraw_κ.symm, hκraw_joint]
  let obsMk : (Fin J × ℝ) × ℝ → ClampObs J :=
    fun p => ClampObs.mk p.1.1 p.1.2 p.2
  have hobsMk : Measurable obsMk := measurable_clampObs_of_design_outcome
  have hobs_joint : Measure.map obsMk (Measure.map H base) = P.dataMeasure := by
    rw [hjoint, Measure.map_map hobsMk (hD.prodMk hY)]
    have hid : obsMk ∘ (fun o : ClampObs J => (D o, Y o)) = id := by
      funext o
      rfl
    rw [hid, Measure.map_id]
  let F : ((Fin J × ℝ) × unitInterval) → ClampObs J × unitInterval :=
    fun p => (obsMk (H p), p.2)
  have hF : Measurable F := (hobsMk.comp hH).prodMk measurable_snd
  have hmargin : (Measure.map F base).map Prod.fst = P.dataMeasure := by
    rw [Measure.map_map measurable_fst hF]
    have hcomp : Prod.fst ∘ F = obsMk ∘ H := by funext p; rfl
    rw [hcomp, ← Measure.map_map hobsMk hH, hobs_joint]
  let potfun : ℝ → (ClampObs J × unitInterval) → ℝ :=
    fun a z => q (z.1.X, a) z.2
  have hpotfun : Measurable (Function.uncurry potfun) := by
    change Measurable (Function.uncurry q ∘
      fun p : ℝ × (ClampObs J × unitInterval) => ((p.2.1.X, p.1), p.2.2))
    have hXobs : Measurable (fun o : ClampObs J => o.X) :=
      measurable_fst.comp (Measurable.of_comap_le le_rfl)
    have hX : Measurable (fun p : ℝ × (ClampObs J × unitInterval) => p.2.1.X) :=
      hXobs.comp (measurable_fst.comp measurable_snd)
    have ha : Measurable (fun p : ℝ × (ClampObs J × unitInterval) => p.1) :=
      measurable_fst
    have hu : Measurable (fun p : ℝ × (ClampObs J × unitInterval) => p.2.2) :=
      measurable_snd.comp measurable_snd
    exact hq.comp ((hX.prodMk ha).prodMk hu)
  have hgmeas : ∀ x : Fin J,
      Measurable (fun z : Set.Icc (0 : ℝ) 1 × unitInterval => q (x, z.1) z.2) := by
    intro x
    change Measurable (Function.uncurry q ∘
      fun z : Set.Icc (0 : ℝ) 1 × unitInterval => ((x, (z.1 : ℝ)), z.2))
    exact hq.comp <| ((measurable_const.prodMk
      (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd)
  have hactual : ∀ᵐ z ∂Measure.map F base,
      z.1.Y = q (z.1.X, z.1.A) z.2 := by
    have hleft : Measurable (fun z : ClampObs J × unitInterval => z.1.Y) :=
      clampOutcome_measurable.comp measurable_fst
    have hright : Measurable (fun z : ClampObs J × unitInterval =>
        q (z.1.X, z.1.A) z.2) := by
      change Measurable (Function.uncurry q ∘ fun z : ClampObs J × unitInterval =>
        ((z.1.X, z.1.A), z.2))
      exact hq.comp ((clampDesign_measurable.comp measurable_fst).prodMk measurable_snd)
    rw [MeasureTheory.ae_map_iff hF.aemeasurable (measurableSet_eq_fun hleft hright)]
    exact Filter.Eventually.of_forall fun p => rfl
  let PF : FullDataLaw J := {
    latentCarrier := unitInterval
    observedMargin := P
    fullMeasure := Measure.map F base
    probability := Measure.isProbabilityMeasure_map hF.aemeasurable
    margin_eq := hmargin
    g := fun x a u => q (x, a) u
    pot := potfun
    pot_jointlyMeasurable := hpotfun
  }
  refine ⟨PF, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact hgmeas
    · intro x a u ha
      exact (kernelUnitQuantile κ (x, a) u).property
    · filter_upwards [hactual] with z hz
      exact ⟨fun a _ => rfl, hz⟩
  · intro x f g hf hg _ _
    let sx : Set (Fin J × ℝ) := {d | d.1 = x}
    let sz : Set (ClampObs J × unitInterval) := {z | z.1.X = x}
    have hsx : MeasurableSet sx := measurable_fst (measurableSet_singleton x)
    have hsz : MeasurableSet sz :=
      ((measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst)
        (measurableSet_singleton x)
    let Af : ℝ := ∫ d, sx.indicator (fun d => f d.2) d ∂ν
    let Gu : ℝ := ∫ u, g u ∂volume
    have hfi : Measurable (sx.indicator (fun d => f d.2)) :=
      (hf.comp measurable_snd).indicator hsx
    have hone : Measurable (sx.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hsx
    have hjoint : (∫ z in sz, f z.1.A * g z.2 ∂Measure.map F base) = Af * Gu := by
      rw [← integral_indicator hsz]
      have hi : Measurable (sz.indicator (fun z => f z.1.A * g z.2)) :=
        ((hf.comp ((measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))).comp measurable_fst)).mul
          (hg.comp measurable_snd)).indicator hsz
      rw [integral_map hF.aemeasurable hi.aestronglyMeasurable]
      change (∫ p : (Fin J × ℝ) × unitInterval,
          sz.indicator (fun z => f z.1.A * g z.2) (F p) ∂base) = _
      have heq : (fun p : (Fin J × ℝ) × unitInterval =>
          sz.indicator (fun z => f z.1.A * g z.2) (F p)) =
          fun p => sx.indicator (fun d => f d.2) p.1 * g p.2 := by
        funext p
        by_cases hp : p.1.1 = x <;> simp [sx, sz, F, H, obsMk, Set.indicator, hp]
      rw [heq, show base = ν.prod volume from rfl, integral_prod_mul]
    have hfint : (∫ z in sz, f z.1.A ∂Measure.map F base) = Af := by
      rw [← integral_indicator hsz]
      have hi : Measurable (sz.indicator (fun z => f z.1.A)) :=
        (hf.comp ((measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))).comp measurable_fst)).indicator hsz
      rw [integral_map hF.aemeasurable hi.aestronglyMeasurable]
      change (∫ p : (Fin J × ℝ) × unitInterval,
          sz.indicator (fun z => f z.1.A) (F p) ∂base) = _
      have heq : (fun p : (Fin J × ℝ) × unitInterval =>
          sz.indicator (fun z => f z.1.A) (F p)) =
          fun p => sx.indicator (fun d => f d.2) p.1 * (1 : ℝ) := by
        funext p
        by_cases hp : p.1.1 = x <;> simp [sx, sz, F, H, obsMk, Set.indicator, hp]
      rw [heq, show base = ν.prod volume from rfl]
      calc
        _ = (∫ d, sx.indicator (fun d => f d.2) d ∂ν) *
            ∫ _u : unitInterval, (1 : ℝ) ∂volume := by
          exact integral_prod_mul
            (μ := ν) (ν := volume)
            (sx.indicator (fun d => f d.2)) (fun _ : unitInterval => (1 : ℝ))
        _ = Af := by simp [Af]
    have hgint : (∫ z in sz, g z.2 ∂Measure.map F base) =
        ν.real sx * Gu := by
      rw [← integral_indicator hsz]
      have hi : Measurable (sz.indicator (fun z => g z.2)) :=
        (hg.comp measurable_snd).indicator hsz
      rw [integral_map hF.aemeasurable hi.aestronglyMeasurable]
      change (∫ p : (Fin J × ℝ) × unitInterval,
          sz.indicator (fun z => g z.2) (F p) ∂base) = _
      have heq : (fun p : (Fin J × ℝ) × unitInterval =>
          sz.indicator (fun z => g z.2) (F p)) =
          fun p => sx.indicator (fun _ => (1 : ℝ)) p.1 * g p.2 := by
        funext p
        by_cases hp : p.1.1 = x <;> simp [sx, sz, F, H, obsMk, Set.indicator, hp]
      rw [heq, show base = ν.prod volume from rfl, integral_prod_mul]
      have honeint : (∫ d, sx.indicator (fun _ => (1 : ℝ)) d ∂ν) =
          ν.real sx := by
        rw [show (fun _ : Fin J × ℝ => (1 : ℝ)) = 1 from rfl]
        exact integral_indicator_one hsx
      rw [honeint]
    have hmass : fullDataStratumMass PF x = ν.real sx := by
      simp only [fullDataStratumMass, PF]
      rw [show P.dataMeasure.map (fun o => o.X) = ν.map Prod.fst by
        simp only [ν]
        rw [Measure.map_map measurable_fst hD]
        rfl]
      unfold Measure.real
      rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
      rfl
    change fullDataStratumMass PF x *
        (∫ z in sz, f z.1.A * g z.2 ∂Measure.map F base) =
      (∫ z in sz, f z.1.A ∂Measure.map F base) *
        ∫ z in sz, g z.2 ∂Measure.map F base
    rw [hmass, hjoint, hfint, hgint]
    ring
  · intro x
    have hX : Measurable (fun z : ClampObs J × unitInterval => z.1.X) :=
      (measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst
    have hs : MeasurableSet {z : ClampObs J × unitInterval | z.1.X = x} :=
      hX (measurableSet_singleton x)
    have hqsec (a : ℝ) : Measurable (fun u : unitInterval => q (x, a) u) := by
      change Measurable (Function.uncurry q ∘
        fun u : unitInterval => ((x, a), u))
      exact hq.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
    have hqint (a : ℝ) : ∫ u, q (x, a) u ∂volume = m (x, a) := by
      calc
        _ = ∫ y, y ∂Measure.map (q (x, a)) volume := by
          simpa only [id_eq] using
            (integral_map (μ := volume) (φ := q (x, a))
              (hqsec a).aemeasurable
              stronglyMeasurable_id.aestronglyMeasurable).symm
        _ = ∫ y, y ∂κ (x, a) := by rw [hqlaw]
        _ = _ := hκ_mean (x, a)
    have hmass : fullDataStratumMass PF x =
        ν.real {d : Fin J × ℝ | d.1 = x} := by
      simp only [fullDataStratumMass, PF]
      rw [show P.dataMeasure.map (fun o => o.X) = ν.map Prod.fst by
        simp only [ν]
        rw [Measure.map_map measurable_fst hD]
        rfl]
      unfold Measure.real
      rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
      rfl
    have hpos : 0 < ν.real {d : Fin J × ℝ | d.1 = x} := by
      rw [← hmass]
      simpa only [fullDataStratumMass, PF] using hmass_pos x
    apply hm_cont x |>.congr
    intro a ha
    change (fullDataStratumMass PF x)⁻¹ *
        (∫ z in {z : ClampObs J × unitInterval | z.1.X = x},
          q (x, a) z.2 ∂Measure.map F base) = m (x, a)
    rw [hmass]
    have hsetint : (∫ z in {z : ClampObs J × unitInterval | z.1.X = x},
        q (x, a) z.2 ∂Measure.map F base) =
        ν.real {d : Fin J × ℝ | d.1 = x} * m (x, a) := by
      rw [← integral_indicator hs]
      have hiMeas : Measurable (fun z : ClampObs J × unitInterval =>
          {z : ClampObs J × unitInterval | z.1.X = x}.indicator
            (fun z => q (x, a) z.2) z) :=
        ((hqsec a).comp measurable_snd).indicator hs
      rw [integral_map hF.aemeasurable hiMeas.aestronglyMeasurable]
      have heq : (fun p : (Fin J × ℝ) × unitInterval =>
          {z : ClampObs J × unitInterval | z.1.X = x}.indicator
            (fun z => q (x, a) z.2) (F p)) =
          fun p => ({d : Fin J × ℝ | d.1 = x}.indicator
            (fun _ => (1 : ℝ)) p.1) * q (x, a) p.2 := by
        funext p
        by_cases hp : p.1.1 = x <;> simp [F, H, obsMk, Set.indicator, hp]
      rw [heq]
      rw [show base = ν.prod volume from rfl, integral_prod_mul, hqint]
      rw [show (fun _ : Fin J × ℝ => (1 : ℝ)) = 1 from rfl]
      exact congrArg (fun t : ℝ => t * m (x, a))
        (integral_indicator_one (μ := ν) (s := {d : Fin J × ℝ | d.1 = x})
          (measurable_fst (measurableSet_singleton x)))
    rw [hsetint]
    field_simp [ne_of_gt hpos]

/-- Fixed-Hölder observed laws have a quantile full-data lift. The result uses [the `hP` condition](hyp:hP), [the `hJ` condition](hyp:hJ), [the `hpmin` condition](hyp:hpmin), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma exists_fullData_holder_lift
    {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin deltaBar : ℝ}
    (hP : ClampModel P beta kappa L cminus cplus pmin)
    (hJ : 0 < J) (hpmin : 0 < pmin) (hdelta : deltaBar ≤ 1) :
    ∃ PF : FullDataLaw J,
      FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
        PF.observedMargin = P := by
  let m : Fin J × ℝ → ℝ := clampRegressionExtension P
  have hm : Measurable m := clampRegressionExtension_measurable P hP.holder
  have hm_unit : ∀ d, m d ∈ Set.Icc (0 : ℝ) 1 :=
    clampRegressionExtension_mem_Icc P hP.holder
  have hcond : P.dataMeasure[(fun o : ClampObs J => o.Y) |
      MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => m (o.X, o.A) :=
    (hP.holder ⟨0, hJ⟩).2.2.1.trans
      (clampRegressionExtension_ae_eq_mu P hP).symm
  have hm_cont : ∀ x : Fin J,
      ContinuousOn (fun a => m (x, a)) (Set.Icc (0 : ℝ) deltaBar) := by
    intro x
    apply (hP.holder x).1.mono (Set.Icc_subset_Icc le_rfl hdelta) |>.congr
    intro a ha
    unfold m
    exact clampRegressionExtension_eq P x ⟨ha.1, ha.2.trans hdelta⟩
  have hmass_pos : ∀ x : Fin J,
      0 < (P.dataMeasure.map (fun o => o.X)).real {x} := by
    intro x
    rw [← (hP.stratumMass x).1]
    exact hpmin.trans_le (hP.stratumMass x).2
  obtain ⟨PF, hmargin, hcons, hexch, hcont⟩ :=
    exists_fullData_quantile_lift P deltaBar hP.probability hP.outcomeSupport
      hmass_pos m hm hm_unit hcond hm_cont
  refine ⟨PF, ?_, hmargin⟩
  exact ⟨hmargin ▸ hP, hcons, hexch, hcont⟩

/-- Continuity-only observed laws have the same quantile full-data lift. The result uses [the `hP` condition](hyp:hP), [the `hpmin` condition](hyp:hpmin). [This is the stated conclusion](goal).
-/
lemma exists_fullData_cont_lift
    {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin deltaBar : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hpmin : 0 < pmin) :
    ∃ PF : FullDataLaw J,
      ContFullDataClampModel PF kappa cminus cplus pmin deltaBar ∧
        PF.observedMargin = P := by
  let _ := hP.probability
  let D : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
  let Y : ClampObs J → ℝ := fun o => o.Y
  have hD : Measurable D := clampDesign_measurable
  have hY : Measurable Y := clampOutcome_measurable
  let ν : Measure (Fin J × ℝ) := P.dataMeasure.map D
  let κraw : ProbabilityTheory.Kernel (Fin J × ℝ) ℝ :=
    ProbabilityTheory.condDistrib Y D P.dataMeasure
  letI : ProbabilityTheory.IsMarkovKernel κraw := inferInstance
  let κ0 : ProbabilityTheory.Kernel (Fin J × ℝ) ℝ := κraw.map clampUnit
  let r : Fin J × ℝ → ℝ := fun d => ∫ y, y ∂κ0 d
  have hr_meas : Measurable r := stronglyMeasurable_id.integral_kernel.measurable
  have hr_unit : ∀ d, r d ∈ Set.Icc (0 : ℝ) 1 := by
    intro d
    have hi : Integrable clampUnit (κraw d) := by
      refine Integrable.of_bound measurable_clampUnit.aestronglyMeasurable 1 ?_
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clampUnit_in_unit y).1]
        exact (clampUnit_in_unit y).2
    have hr : r d = ∫ y, clampUnit y ∂κraw d := by
      simp only [r, κ0]
      rw [ProbabilityTheory.Kernel.map_apply κraw measurable_clampUnit d]
      simpa only [id_eq] using
        (integral_map measurable_clampUnit.aemeasurable
          stronglyMeasurable_id.aestronglyMeasurable)
    rw [hr]
    constructor
    · exact integral_nonneg fun y => (clampUnit_in_unit y).1
    · calc
        _ ≤ ∫ _y : ℝ, (1 : ℝ) ∂κraw d :=
          integral_mono hi (integrable_const 1) fun y => (clampUnit_in_unit y).2
        _ = 1 := by simp
  let mu := contRegression P kappa cminus cplus pmin deltaBar hP
  have hmu_cont : ∀ x, ContinuousOn (mu x) (Set.Icc (0 : ℝ) deltaBar) :=
    (Classical.choose_spec hP.continuousVersion).1
  have hmu_ce : P.dataMeasure[(fun o : ClampObs J => o.Y) |
      MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => mu o.X o.A :=
    (Classical.choose_spec hP.continuousVersion).2
  let c : Fin J × ℝ → ℝ := fun d =>
    if d.2 ∈ Set.Icc (0 : ℝ) deltaBar then clampUnit (mu d.1 d.2) else 0
  have hc_meas : Measurable c := by
    apply measurable_from_prod_countable_right
    intro x
    have hcOn : ContinuousOn (fun a => clampUnit (mu x a))
        (Set.Icc (0 : ℝ) deltaBar) :=
      continuous_clampUnit'.comp_continuousOn (hmu_cont x)
    have hzOn : ContinuousOn (fun _a : ℝ => (0 : ℝ))
        (Set.Icc (0 : ℝ) deltaBar)ᶜ := continuous_const.continuousOn
    convert hcOn.measurable_piecewise hzOn measurableSet_Icc using 1
    funext a
    by_cases ha : a ∈ Set.Icc (0 : ℝ) deltaBar <;>
      simp_all [c, Set.piecewise]
  let E : Set (Fin J × ℝ) := {d | d.2 ∈ Set.Icc (0 : ℝ) deltaBar}
  have hE : MeasurableSet E := measurable_snd measurableSet_Icc
  let m : Fin J × ℝ → ℝ := E.piecewise c r
  have hm : Measurable m := hc_meas.piecewise hE hr_meas
  have hm_unit : ∀ d, m d ∈ Set.Icc (0 : ℝ) 1 := by
    intro d
    by_cases hd : d ∈ E
    · rw [show m d = if d ∈ E then c d else r d by rfl, if_pos hd]
      have hd' : d.2 ∈ Set.Icc (0 : ℝ) deltaBar := hd
      rw [show c d = if d.2 ∈ Set.Icc (0 : ℝ) deltaBar then
        clampUnit (mu d.1 d.2) else 0 by rfl, if_pos hd']
      exact clampUnit_in_unit _
    · rw [show m d = if d ∈ E then c d else r d by rfl, if_neg hd]
      exact hr_unit d
  have hraw_κ0 : (κraw : (Fin J × ℝ) → Measure ℝ) =ᵐ[ν] κ0 := by
    have hclamp : (fun o : ClampObs J => clampUnit (Y o)) =ᵐ[P.dataMeasure] Y := by
      filter_upwards [hP.outcomeSupport] with o ho
      simp only [Y]
      unfold clampUnit
      simp [ho.1, ho.2]
    have hc' : (ProbabilityTheory.condDistrib (clampUnit ∘ Y) D P.dataMeasure :
          ProbabilityTheory.Kernel (Fin J × ℝ) ℝ) =ᵐ[ν]
        (ProbabilityTheory.condDistrib Y D P.dataMeasure).map clampUnit :=
      ProbabilityTheory.condDistrib_comp (μ := P.dataMeasure)
        (X := D) hY.aemeasurable measurable_clampUnit
    have heq : ProbabilityTheory.condDistrib (clampUnit ∘ Y) D P.dataMeasure = κraw :=
      ProbabilityTheory.condDistrib_congr_left hclamp
    rw [heq] at hc'
    simpa only [ν, κ0, κraw] using hc'
  have hce := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    hD hY.aemeasurable stronglyMeasurable_id
    (Integrable.of_bound hY.aestronglyMeasurable 1 <|
      hP.outcomeSupport.mono fun o ho => by
        change |o.Y| ≤ 1
        exact abs_le.2 ⟨by linarith [ho.1], ho.2⟩)
  have hraw_mu : (fun o => ∫ y, y ∂κraw (D o)) =ᵐ[P.dataMeasure]
      fun o => mu o.X o.A := hce.symm.trans hmu_ce
  have hr_mu : (fun o => r (D o)) =ᵐ[P.dataMeasure] fun o => mu o.X o.A := by
    have hmeans : (fun d => ∫ y, y ∂κraw d) =ᵐ[ν] r :=
      hraw_κ0.mono fun d hd => by simp only [r, hd]
    have hpull := hmeans.comp_tendsto (Measure.tendsto_ae_map hD.aemeasurable)
    exact hpull.symm.trans hraw_mu
  have hcond : P.dataMeasure[(fun o : ClampObs J => o.Y) |
      MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => m (o.X, o.A) := by
    filter_upwards [hmu_ce, hr_mu] with o hceo hro
    rw [hceo]
    by_cases ho : D o ∈ E
    · rw [show m (o.X, o.A) = if D o ∈ E then c (D o) else r (D o) by rfl,
        if_pos ho]
      rw [show c (D o) = if D o ∈ E then clampUnit (mu o.X o.A) else 0 by rfl,
        if_pos ho, ← hro]
      rw [show clampUnit (r (D o)) = r (D o) by
        unfold clampUnit
        rw [max_eq_right (hr_unit (D o)).1, min_eq_right (hr_unit (D o)).2]]
    · rw [show m (o.X, o.A) = if D o ∈ E then c (D o) else r (D o) by rfl,
        if_neg ho]
      exact hro.symm
  have hm_cont : ∀ x : Fin J,
      ContinuousOn (fun a => m (x, a)) (Set.Icc (0 : ℝ) deltaBar) := by
    intro x
    have hclamp : ContinuousOn (fun a => clampUnit (mu x a))
        (Set.Icc (0 : ℝ) deltaBar) :=
      continuous_clampUnit'.comp_continuousOn (hmu_cont x)
    apply hclamp.congr
    intro a ha
    change m (x, a) = clampUnit (mu x a)
    rw [show m (x, a) = if (x, a) ∈ E then c (x, a) else r (x, a) by rfl,
      if_pos (show (x, a) ∈ E by exact ha)]
    rw [show c (x, a) = if a ∈ Set.Icc (0 : ℝ) deltaBar then
      clampUnit (mu x a) else 0 by rfl, if_pos ha]
  have hmass_pos : ∀ x : Fin J,
      0 < (P.dataMeasure.map (fun o => o.X)).real {x} := by
    intro x
    rw [← (hP.stratumMass x).1]
    exact hpmin.trans_le (hP.stratumMass x).2
  obtain ⟨PF, hmargin, hcons, hexch, hcont⟩ :=
    exists_fullData_quantile_lift P deltaBar hP.probability hP.outcomeSupport
      hmass_pos m hm hm_unit hcond hm_cont
  refine ⟨PF, ?_, hmargin⟩
  exact ⟨hmargin ▸ hP, hcons, hexch, hcont⟩

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
