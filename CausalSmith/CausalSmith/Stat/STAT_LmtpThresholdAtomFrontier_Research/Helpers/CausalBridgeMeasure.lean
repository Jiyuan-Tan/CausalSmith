/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.LocalWindowGram
import Mathlib.Probability.Independence.Integration

/-!
# Conditional full-data stratum measure helpers

This module derives the normalized stratum product law and continuity of the
full-data response mean used by the causal clamp bridge.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- After restriction to a positive-mass stratum and normalization, treatment
and the latent response coordinate are independent. The result uses [the `hexch` condition](hyp:hexch), [the `hpx` condition](hyp:hpx), [the `hmass` condition](hyp:hmass). [This is the stated conclusion](goal).
-/
lemma conditional_stratum_treatment_latent_indep
    (J : ℕ)
    (PF : FullDataLaw J)
    (hexch : LatentExchangeability (PF := PF)) (x : Fin J)
    (hpx : 0 < PF.observedMargin.px x)
    (hmass : fullDataStratumMass PF x = PF.observedMargin.px x) :
    ProbabilityTheory.IndepFun
      (fun z : ClampObs J × PF.latentCarrier => z.1.A) (fun z => z.2)
      ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
        PF.fullMeasure.restrict {z | z.1.X = x}) := by
  letI : IsProbabilityMeasure PF.fullMeasure := PF.probability
  have hX : Measurable (fun o : ClampObs J => o.X) := by
    exact measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hfullX : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.X) :=
    hX.comp measurable_fst
  have hA : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.A) := by
    have hAo : Measurable (fun o : ClampObs J => o.A) := by
      exact measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
    exact hAo.comp measurable_fst
  have hU : Measurable (fun z : ClampObs J × PF.latentCarrier => z.2) := measurable_snd
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have he := hexch x (s.indicator (fun _ => (1 : ℝ)))
    (t.indicator (fun _ => (1 : ℝ)))
  have hfs : Measurable (s.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hs
  have hgt : Measurable (t.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator ht
  specialize he hfs hgt
    ⟨1, fun a => by by_cases ha : a ∈ s <;> simp [Set.indicator, ha]⟩
    ⟨1, fun u => by by_cases hu : u ∈ t <;> simp [Set.indicator, hu]⟩
  rw [hmass] at he
  have hSx : MeasurableSet {z : ClampObs J × PF.latentCarrier | z.1.X = x} :=
    hfullX (measurableSet_singleton x)
  have hAs : MeasurableSet ((fun z : ClampObs J × PF.latentCarrier => z.1.A) ⁻¹' s) := hA hs
  have hUt : MeasurableSet ((fun z : ClampObs J × PF.latentCarrier => z.2) ⁻¹' t) := hU ht
  have hIfg : (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
      s.indicator (fun _ => (1 : ℝ)) z.1.A * t.indicator (fun _ => (1 : ℝ)) z.2
        ∂PF.fullMeasure) =
      PF.fullMeasure.real ({z : ClampObs J × PF.latentCarrier | z.1.X = x} ∩
        ((fun z => z.1.A) ⁻¹' s ∩ (fun z => z.2) ⁻¹' t)) := by
    rw [← integral_indicator hSx]
    rw [← integral_indicator_one (hSx.inter (hAs.inter hUt))]
    congr 1
    funext z
    by_cases hx : z.1.X = x <;> by_cases ha : z.1.A ∈ s <;>
      by_cases hu : z.2 ∈ t <;> simp [Set.indicator, hx, ha, hu]
  have hIf : (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
      s.indicator (fun _ => (1 : ℝ)) z.1.A ∂PF.fullMeasure) =
      PF.fullMeasure.real ({z : ClampObs J × PF.latentCarrier | z.1.X = x} ∩
        (fun z => z.1.A) ⁻¹' s) := by
    rw [← integral_indicator hSx]
    rw [← integral_indicator_one (hSx.inter hAs)]
    congr 1
    funext z
    by_cases hx : z.1.X = x <;> by_cases ha : z.1.A ∈ s <;>
      simp [Set.indicator, hx, ha]
  have hIg : (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
      t.indicator (fun _ => (1 : ℝ)) z.2 ∂PF.fullMeasure) =
      PF.fullMeasure.real ({z : ClampObs J × PF.latentCarrier | z.1.X = x} ∩
        (fun z => z.2) ⁻¹' t) := by
    rw [← integral_indicator hSx]
    rw [← integral_indicator_one (hSx.inter hUt)]
    congr 1
    funext z
    by_cases hx : z.1.X = x <;> by_cases hu : z.2 ∈ t <;>
      simp [Set.indicator, hx, hu]
  rw [hIfg, hIf, hIg] at he
  have he' : PF.observedMargin.px x *
        PF.fullMeasure.real ((fun z : ClampObs J × PF.latentCarrier => z.2) ⁻¹' t ∩
          ({z | z.1.X = x} ∩ (fun z => z.1.A) ⁻¹' s)) =
      PF.fullMeasure.real ({z | z.1.X = x} ∩ (fun z => z.1.A) ⁻¹' s) *
        PF.fullMeasure.real ((fun z => z.2) ⁻¹' t ∩ {z | z.1.X = x}) := by
    convert he using 1 <;> congr 2 <;> ext z <;>
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] <;> tauto
  have hscalar : (ENNReal.ofReal (PF.observedMargin.px x))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hpx])
  have hfinite (u : Set (ClampObs J × PF.latentCarrier)) :
      (ENNReal.ofReal (PF.observedMargin.px x))⁻¹ *
        (PF.fullMeasure.restrict {z | z.1.X = x}) u ≠ ⊤ :=
    ENNReal.mul_ne_top hscalar (measure_ne_top _ _)
  apply (ENNReal.toReal_eq_toReal_iff' (hfinite _)
    (ENNReal.mul_ne_top (hfinite _) (hfinite _))).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hpx.le]
  rw [Measure.restrict_apply (hAs.inter hUt), Measure.restrict_apply hAs,
    Measure.restrict_apply hUt]
  simp only [Set.inter_left_comm, Set.inter_comm]
  change (PF.observedMargin.px x)⁻¹ *
      PF.fullMeasure.real ((fun z : ClampObs J × PF.latentCarrier => z.2) ⁻¹' t ∩
        ({z | z.1.X = x} ∩ (fun z => z.1.A) ⁻¹' s)) =
    ((PF.observedMargin.px x)⁻¹ *
        PF.fullMeasure.real ({z | z.1.X = x} ∩ (fun z => z.1.A) ⁻¹' s)) *
      ((PF.observedMargin.px x)⁻¹ *
        PF.fullMeasure.real ((fun z => z.2) ⁻¹' t ∩ {z | z.1.X = x}))
  calc
    _ = (PF.observedMargin.px x)⁻¹ ^ 2 *
        (PF.observedMargin.px x *
          PF.fullMeasure.real ((fun z : ClampObs J × PF.latentCarrier => z.2) ⁻¹' t ∩
            ({z | z.1.X = x} ∩ (fun z => z.1.A) ⁻¹' s))) := by
          field_simp [ne_of_gt hpx]
    _ = (PF.observedMargin.px x)⁻¹ ^ 2 *
        (PF.fullMeasure.real ({z | z.1.X = x} ∩ (fun z => z.1.A) ⁻¹' s) *
          PF.fullMeasure.real ((fun z => z.2) ⁻¹' t ∩ {z | z.1.X = x})) := by
          rw [he']
    _ = _ := by ring

/-- The treatment marginal of the normalized full-data stratum is the declared
conditional treatment law. The result uses [the `hmodel` condition](hyp:hmodel), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin). [This is the stated conclusion](goal).
-/
lemma conditional_stratum_treatment_law
    (J : ℕ)
    (kappa cminus cplus pmin : ℝ)
    (PF : FullDataLaw J)
    (hmodel : BridgeClampModel PF.observedMargin kappa cminus cplus pmin)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) :
    Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A)
        ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
          PF.fullMeasure.restrict {z | z.1.X = x}) =
      conditionalTreatmentMeasure PF.observedMargin x := by
  have hpx : 0 < PF.observedMargin.px x :=
    lt_of_lt_of_le hpmin (hmodel.stratumMass x).2
  have hfst : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1) := measurable_fst
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hA : Measurable (fun o : ClampObs J => o.A) :=
    measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hrestrict :
      Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1)
          (PF.fullMeasure.restrict {z | z.1.X = x}) =
        PF.observedMargin.dataMeasure.restrict {o | o.X = x} := by
    let s : Set (ClampObs J) := (fun o => o.X) ⁻¹' {x}
    change Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1)
        (PF.fullMeasure.restrict ((fun z => z.1) ⁻¹' s)) =
      PF.observedMargin.dataMeasure.restrict s
    calc
      _ = (Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1) PF.fullMeasure).restrict s :=
        (Measure.restrict_map hfst (hX (measurableSet_singleton x))).symm
      _ = _ := by rw [PF.margin_eq]
  have hunscaled :
      Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A)
          (PF.fullMeasure.restrict {z | z.1.X = x}) =
        ENNReal.ofReal (PF.observedMargin.px x) •
          conditionalTreatmentMeasure PF.observedMargin x := by
    rw [← stratumTreatmentMeasure_eq PF.observedMargin hmodel hkappa hcplus hpmin x]
    rw [← hrestrict, Measure.map_map hA hfst]
    rfl
  rw [Measure.map_smul, hunscaled, smul_smul]
  have hz : ENNReal.ofReal (PF.observedMargin.px x) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hpx
  rw [ENNReal.inv_mul_cancel hz ENNReal.ofReal_ne_top, one_smul]

/-- A bounded measurable function of treatment and the latent coordinate
integrates by iterated integration under the normalized stratum law. The result uses [the `hmodel` condition](hyp:hmodel), [the `hexch` condition](hyp:hexch), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hF` condition](hyp:hF), [the `hM` condition](hyp:hM). [This is the stated conclusion](goal).
-/
lemma conditional_stratum_integral_prod
    (J : ℕ)
    (kappa cminus cplus pmin : ℝ)
    (PF : FullDataLaw J)
    (hmodel : BridgeClampModel PF.observedMargin kappa cminus cplus pmin)
    (hexch : LatentExchangeability (PF := PF))
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) (F : ℝ × PF.latentCarrier → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) :
    (PF.observedMargin.px x)⁻¹ *
        (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x}, F (z.1.A, z.2) ∂PF.fullMeasure) =
      ∫ a, ∫ u, F (a, u)
          ∂Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2)
            ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
              PF.fullMeasure.restrict {z | z.1.X = x})
        ∂conditionalTreatmentMeasure PF.observedMargin x := by
  let μ := (ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
    PF.fullMeasure.restrict {z : ClampObs J × PF.latentCarrier | z.1.X = x}
  have hpx : 0 < PF.observedMargin.px x :=
    lt_of_lt_of_le hpmin (hmodel.stratumMass x).2
  have hmass : fullDataStratumMass PF x = PF.observedMargin.px x :=
    (hmodel.stratumMass x).1.symm
  have hA : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.A) := by
    have hAo : Measurable (fun o : ClampObs J => o.A) :=
      measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
    exact hAo.comp measurable_fst
  have hU : Measurable (fun z : ClampObs J × PF.latentCarrier => z.2) := measurable_snd
  have hpair : Measurable (fun z : ClampObs J × PF.latentCarrier => (z.1.A, z.2)) :=
    Measurable.prod hA hU
  letI : IsProbabilityMeasure PF.fullMeasure := PF.probability
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    dsimp [μ]
    apply ENNReal.mul_lt_top
    · rw [ENNReal.inv_lt_top]
      exact ENNReal.ofReal_pos.mpr hpx
    · exact measure_lt_top _ _
  have hFind : Integrable (fun z : ClampObs J × PF.latentCarrier => F (z.1.A, z.2)) μ :=
    Integrable.of_bound (hF.comp hpair).aestronglyMeasurable M
      (ae_of_all _ fun z => hM (z.1.A, z.2))
  have hind := conditional_stratum_treatment_latent_indep J PF hexch x hpx hmass
  have hjoint : Measure.map (fun z : ClampObs J × PF.latentCarrier => (z.1.A, z.2)) μ =
      (Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A) μ).prod
        (Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2) μ) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hA.aemeasurable hU.aemeasurable).mp hind
  have hprodInt : Integrable F
      ((Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A) μ).prod
        (Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2) μ)) := by
    rw [← hjoint]
    exact (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).2 hFind
  have hAlaw : Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A) μ =
      conditionalTreatmentMeasure PF.observedMargin x := by
    simpa [μ] using conditional_stratum_treatment_law J kappa cminus
      cplus pmin PF hmodel hkappa hcplus hpmin x
  calc
    _ = ∫ z, F (z.1.A, z.2) ∂μ := by
      rw [show μ = (ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
        PF.fullMeasure.restrict {z : ClampObs J × PF.latentCarrier | z.1.X = x} from rfl,
        integral_smul_measure]
      simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hpx.le, smul_eq_mul]
    _ = ∫ w, F w ∂Measure.map (fun z : ClampObs J × PF.latentCarrier => (z.1.A, z.2)) μ := by
      exact (integral_map hpair.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ w, F w ∂(Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A) μ).prod
        (Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2) μ) := by rw [hjoint]
    _ = ∫ a, ∫ u, F (a, u) ∂Measure.map
        (fun z : ClampObs J × PF.latentCarrier => z.2) μ
        ∂Measure.map (fun z : ClampObs J × PF.latentCarrier => z.1.A) μ :=
      integral_prod F hprodInt
    _ = _ := by rw [hAlaw]

/-- The latent-coordinate integral under the normalized stratum law is the
full-data response mean. The result uses [the `hmodel` condition](hyp:hmodel), [the `hpmin` condition](hyp:hpmin), [the `hcons` condition](hyp:hcons), [the `ha` condition](hyp:ha). [This is the stated conclusion](goal).
-/
lemma conditional_stratum_latent_integral_eq_mean
    (J : ℕ)
    (kappa cminus cplus pmin : ℝ)
    (PF : FullDataLaw J)
    (hmodel : BridgeClampModel PF.observedMargin kappa cminus cplus pmin)
    (hpmin : 0 < pmin)
    (hcons : LatentResponseConsistency (PF := PF))
    (x : Fin J) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u, PF.g x a u
      ∂Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2)
        ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
          PF.fullMeasure.restrict {z | z.1.X = x})) =
      fullDataResponseMean (PF := PF) (x := x) (a := a) := by
  have hpx : 0 < PF.observedMargin.px x := by
    exact lt_of_lt_of_le hpmin (hmodel.stratumMass x).2
  have hmass : fullDataStratumMass PF x = PF.observedMargin.px x :=
    (hmodel.stratumMass x).1.symm
  have hg : Measurable (fun u : PF.latentCarrier => PF.g x a u) := by
    exact (hcons.1 x).comp (by fun_prop : Measurable fun u : PF.latentCarrier =>
      ((⟨a, ha⟩ : Set.Icc (0 : ℝ) 1), u))
  rw [integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,
    integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hpx.le, smul_eq_mul,
    fullDataResponseMean]
  rw [hmass]

/-- Conditional L1 response distance bounds the distance between full-data
response means. The result uses [the `hmodel` condition](hyp:hmodel), [the `hpmin` condition](hyp:hpmin), [the `hcons` condition](hyp:hcons), [the `hs` condition](hyp:hs), [the `ht` condition](hyp:ht). [This is the stated conclusion](goal).
-/
lemma fullDataResponseMean_dist_le
    (J : ℕ)
    (beta kappa L cminus cplus pmin : ℝ)
    (PF : FullDataLaw J)
    (hmodel : ClampModel PF.observedMargin beta kappa L cminus cplus pmin)
    (hpmin : 0 < pmin) (hcons : LatentResponseConsistency (PF := PF))
    (x : Fin J) (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (fullDataResponseMean (PF := PF) (x := x) (a := t))
        (fullDataResponseMean (PF := PF) (x := x) (a := s)) ≤
      (PF.observedMargin.px x)⁻¹ *
        ∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
          |PF.pot t z - PF.pot s z| ∂PF.fullMeasure := by
  letI : IsProbabilityMeasure PF.fullMeasure := PF.probability
  have hpx : 0 < PF.observedMargin.px x :=
    lt_of_lt_of_le hpmin (hmodel.stratumMass x).2
  have hmass : fullDataStratumMass PF x = PF.observedMargin.px x :=
    (hmodel.stratumMass x).1.symm
  have hg (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      Measurable (fun z : ClampObs J × PF.latentCarrier => PF.g x a z.2) := by
    exact ((hcons.1 x).comp (by fun_prop : Measurable fun z : ClampObs J × PF.latentCarrier =>
      ((⟨a, ha⟩ : Set.Icc (0 : ℝ) 1), z.2)))
  have hgInt (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      Integrable (fun z : ClampObs J × PF.latentCarrier => PF.g x a z.2)
        (PF.fullMeasure.restrict {z | z.1.X = x}) := by
    apply Integrable.of_bound (hg a ha).aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hcons.2.1 x a z.2 ha).1],
        (hcons.2.1 x a z.2 ha).2⟩
  have hpotg (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      (fun z : ClampObs J × PF.latentCarrier => PF.pot a z) =ᵐ[
        PF.fullMeasure.restrict {z | z.1.X = x}]
        (fun z => PF.g x a z.2) := by
    filter_upwards [ae_restrict_of_ae hcons.2.2,
      ae_restrict_mem (by
        have hXm : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.X) :=
          (measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst
        exact hXm (measurableSet_singleton x))] with z hz hzx
    simpa [hzx] using hz.1 a ha
  have hpotInt (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      Integrable (fun z : ClampObs J × PF.latentCarrier => PF.pot a z)
        (PF.fullMeasure.restrict {z | z.1.X = x}) :=
    (hgInt a ha).congr (hpotg a ha).symm
  rw [fullDataResponseMean, fullDataResponseMean, Real.dist_eq]
  rw [hmass]
  calc
    |(PF.observedMargin.px x)⁻¹ *
          (∫ z in {z | z.1.X = x}, PF.g x t z.2 ∂PF.fullMeasure) -
        (PF.observedMargin.px x)⁻¹ *
          (∫ z in {z | z.1.X = x}, PF.g x s z.2 ∂PF.fullMeasure)| =
        (PF.observedMargin.px x)⁻¹ *
          |(∫ z in {z | z.1.X = x}, PF.g x t z.2 ∂PF.fullMeasure) -
            (∫ z in {z | z.1.X = x}, PF.g x s z.2 ∂PF.fullMeasure)| := by
              rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hpx.le)]
    _ = (PF.observedMargin.px x)⁻¹ *
          |∫ z in {z | z.1.X = x},
            (PF.g x t z.2 - PF.g x s z.2) ∂PF.fullMeasure| := by
              rw [integral_sub (hgInt t ht) (hgInt s hs)]
    _ = (PF.observedMargin.px x)⁻¹ *
          |∫ z in {z | z.1.X = x},
            (PF.pot t z - PF.pot s z) ∂PF.fullMeasure| := by
              congr 2
              apply integral_congr_ae
              filter_upwards [hpotg t ht, hpotg s hs] with z htz hsz
              rw [htz, hsz]
    _ ≤ _ := mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
      (inv_nonneg.mpr hpx.le)

/-- The full-data mean-continuity member is exactly continuity of the
structural response mean on the declared threshold interval. The result uses [the `hcont` condition](hyp:hcont). [This is the stated conclusion](goal).
-/
lemma fullDataResponseMean_continuousOn
    (J : ℕ) (PF : FullDataLaw J) (deltaBar : ℝ)
    (hcont : FullDataResponseContinuity PF deltaBar) (x : Fin J) :
    ContinuousOn (fun a => fullDataResponseMean (PF := PF) (x := x) (a := a))
      (Set.Icc (0 : ℝ) deltaBar) := by
  exact hcont x

/-- Two continuous conditional-regression versions on the threshold interval
coincide there under the positive polynomial treatment-density envelope. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hcont₁` condition](hyp:hcont₁), [the `hcont₂` condition](hyp:hcont₂), [the `hver₁` condition](hyp:hver₁), [the `hver₂` condition](hyp:hver₂). [This is the stated conclusion](goal).
-/
-- @node: lem:continuity-regression-extension-unique
lemma cont_regression_extension_unique
    (P : ClampLaw J) (kappa cminus cplus pmin deltaBar : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (mu₁ mu₂ : Fin J → ℝ → ℝ)
    (hcont₁ : ∀ x, ContinuousOn (mu₁ x) (Set.Icc (0 : ℝ) deltaBar))
    (hcont₂ : ∀ x, ContinuousOn (mu₂ x) (Set.Icc (0 : ℝ) deltaBar))
    (hver₁ : P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => mu₁ o.X o.A)
    (hver₂ : P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => mu₂ o.X o.A) :
    ∀ x, Set.EqOn (mu₁ x) (mu₂ x) (Set.Icc (0 : ℝ) deltaBar) := by
  rcases hreg with ⟨_, hkappa, hcminus, _, hcplus, hpmin, _, hdeltaBar, hdeltaBar_lt⟩
  intro x
  have hversions :
      (fun o : ClampObs J => mu₁ o.X o.A) =ᵐ[P.dataMeasure]
        fun o => mu₂ o.X o.A := hver₁.symm.trans hver₂
  have hpx : 0 < P.px x := lt_of_lt_of_le hpmin (hP.stratumMass x).2
  let f₁ : ℝ → ℝ := fun a => if a ∈ Set.Icc (0 : ℝ) deltaBar then mu₁ x a else 0
  let f₂ : ℝ → ℝ := fun a => if a ∈ Set.Icc (0 : ℝ) deltaBar then mu₂ x a else 0
  have hf₁ : Measurable f₁ := by
    let g : ℝ → ℝ := fun _ => 0
    have hg : ContinuousOn g (Set.Icc (0 : ℝ) deltaBar)ᶜ :=
      continuous_const.continuousOn
    change Measurable ((Set.Icc (0 : ℝ) deltaBar).piecewise (mu₁ x) g)
    exact (hcont₁ x).measurable_piecewise hg measurableSet_Icc
  have hf₂ : Measurable f₂ := by
    let g : ℝ → ℝ := fun _ => 0
    have hg : ContinuousOn g (Set.Icc (0 : ℝ) deltaBar)ᶜ :=
      continuous_const.continuousOn
    change Measurable ((Set.Icc (0 : ℝ) deltaBar).piecewise (mu₂ x) g)
    exact (hcont₂ x).measurable_piecewise hg measurableSet_Icc
  let B : Set ℝ := {a | f₁ a ≠ f₂ a}
  have hB : MeasurableSet B := (measurableSet_eq_fun hf₁ hf₂).compl
  have hBthreshold : B ⊆ Set.Icc (0 : ℝ) deltaBar := by
    intro a ha
    by_contra hnot
    change (if a ∈ Set.Icc (0 : ℝ) deltaBar then mu₁ x a else 0) ≠
      (if a ∈ Set.Icc (0 : ℝ) deltaBar then mu₂ x a else 0) at ha
    simp only [if_neg hnot] at ha
    exact ha rfl
  have hBunit : B ⊆ Set.Icc (0 : ℝ) 1 := by
    intro a ha
    exact ⟨(hBthreshold ha).1, (hBthreshold ha).2.trans hdeltaBar_lt.le⟩
  have hbadNull : P.dataMeasure
      {o : ClampObs J | o.X = x ∧ o.A ∈ B} = 0 := by
    apply measure_mono_null _ (ae_iff.mp hversions)
    intro o ho
    have ha := hBthreshold ho.2
    have hneq : mu₁ x o.A ≠ mu₂ x o.A := by
      intro heq
      apply ho.2
      change (if o.A ∈ Set.Icc (0 : ℝ) deltaBar then mu₁ x o.A else 0) =
        (if o.A ∈ Set.Icc (0 : ℝ) deltaBar then mu₂ x o.A else 0)
      simpa only [if_pos ha] using heq
    exact fun heq => hneq (by simpa [ho.1] using heq)
  have hdensity := (hP.condDensity.2.2 x).2 B hB hBunit
  have hleft : P.dataMeasure.real
      {o : ClampObs J | o.X = x ∧ o.A ∈ B} = 0 := by
    simp [Measure.real, hbadNull]
  rw [hleft] at hdensity
  have hintegral : (∫ a in B, P.pi x a) = 0 := by
    nlinarith
  have hcplus0 : 0 ≤ cplus := le_trans (by linarith) hcplus
  have hpiInt : IntegrableOn (P.pi x) B volume := by
    apply IntegrableOn.of_bound (lt_of_le_of_lt (measure_mono hBunit) measure_Icc_lt_top)
    · exact ((aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
        (hP.condDensity.1 x)).mono_measure
          (Measure.restrict_mono_set volume hBunit)).aestronglyMeasurable
    · filter_upwards [(hP.condDensity.2.1 x).filter_mono
          (ae_mono (Measure.restrict_mono_set volume hBunit)),
        (hP.thinning x).filter_mono
          (ae_mono (Measure.restrict_mono_set volume hBunit)),
        ae_restrict_mem hB] with a hnon hthin ha
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      calc
        P.pi x a ≤ cplus * a ^ kappa := hthin.2
        _ ≤ cplus := by
          exact mul_le_of_le_one_right hcplus0
            (Real.rpow_le_one (hBunit ha).1 (hBunit ha).2 hkappa)
  have hnonneg : 0 ≤ᵐ[volume.restrict B] P.pi x :=
    (hP.condDensity.2.1 x).filter_mono
      (ae_mono (Measure.restrict_mono_set volume hBunit))
  have hpizero : P.pi x =ᵐ[volume.restrict B] (fun _ : ℝ => (0 : ℝ)) :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hnonneg hpiInt).mp hintegral
  have hnezero : ∀ᵐ a ∂volume.restrict B, a ≠ 0 :=
    (volume.ae_ne 0).filter_mono (ae_mono Measure.restrict_le_self)
  have hfalse : ∀ᵐ _a ∂volume.restrict B, False := by
    filter_upwards [hpizero, hnezero,
      (hP.thinning x).filter_mono
        (ae_mono (Measure.restrict_mono_set volume hBunit)),
      ae_restrict_mem hB] with a hzero ha0 hthin ha
    have haPos : 0 < a := lt_of_le_of_ne (hBunit ha).1 (Ne.symm ha0)
    have hpiPos : 0 < P.pi x a := lt_of_lt_of_le
      (mul_pos hcminus (Real.rpow_pos_of_pos haPos kappa)) hthin.1
    linarith
  have hBnull : volume B = 0 := by
    have hu : (volume.restrict B) Set.univ = 0 := by
      simpa using (ae_iff.mp hfalse)
    simpa [Measure.restrict_apply_univ] using hu
  have houtside : ∀ᵐ a ∂volume, a ∉ B := by
    rw [ae_iff]
    convert hBnull using 1
    congr 1
    ext a
    simp
  have hglobal : f₁ =ᵐ[volume] f₂ := by
    filter_upwards [houtside] with a ha
    exact not_ne_iff.mp ha
  have hthreshold : mu₁ x =ᵐ[volume.restrict (Set.Icc (0 : ℝ) deltaBar)] mu₂ x := by
    filter_upwards [ae_restrict_of_ae hglobal,
      ae_restrict_mem measurableSet_Icc] with a heq ha
    simpa only [f₁, f₂, if_pos ha] using heq
  exact volume.eqOn_Icc_of_ae_eq (ne_of_lt hdeltaBar) hthreshold
    (hcont₁ x) (hcont₂ x)

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
