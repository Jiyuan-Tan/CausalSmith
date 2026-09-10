/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.CausalBridgeMeasure
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.RegressionVersion
import Causalean.Mathlib.MeasureTheory.PartitionIntegral

/-!
# Identification identities for the causal clamp bridge

This file turns the normalized-stratum product law into the conditional
integral identity and the pathwise decomposition used by the two causal bridge
theorems.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set

noncomputable section

/-- A globally measurable extension of a structural response map from its
declared unit-dose domain. -/
-- @node: structuralResponseExtension
def structuralResponseExtension (PF : FullDataLaw J)
    (hcons : LatentResponseConsistency PF) (x : Fin J) :
    ℝ × PF.latentCarrier → ℝ :=
  Function.extend
    (fun z : Set.Icc (0 : ℝ) 1 × PF.latentCarrier => (z.1.1, z.2))
    (fun z => PF.g x z.1.1 z.2) 0

/-- The structural-response extension is measurable. The result uses [the `hcons` condition](hyp:hcons). [This is the stated conclusion](goal).
-/
-- @node: structuralResponseExtension_measurable
lemma structuralResponseExtension_measurable (PF : FullDataLaw J)
    (hcons : LatentResponseConsistency PF) (x : Fin J) :
    Measurable (structuralResponseExtension PF hcons x) := by
  let e : Set.Icc (0 : ℝ) 1 × PF.latentCarrier → ℝ × PF.latentCarrier :=
    fun z => (z.1.1, z.2)
  have he : MeasurableEmbedding e :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).prodMap
      MeasurableEmbedding.id
  exact he.measurable_extend (hcons.1 x) measurable_const

/-- On the unit dose interval, the measurable extension equals the original
structural response. The result uses [the `hcons` condition](hyp:hcons), [the `ha` condition](hyp:ha). [This is the stated conclusion](goal).
-/
-- @node: structuralResponseExtension_eq
lemma structuralResponseExtension_eq (PF : FullDataLaw J)
    (hcons : LatentResponseConsistency PF) (x : Fin J) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (u : PF.latentCarrier) :
    structuralResponseExtension PF hcons x (a, u) = PF.g x a u := by
  let e : Set.Icc (0 : ℝ) 1 × PF.latentCarrier → ℝ × PF.latentCarrier :=
    fun z => (z.1.1, z.2)
  have he : Function.Injective e :=
    ((MeasurableEmbedding.subtype_coe measurableSet_Icc).prodMap
      MeasurableEmbedding.id).injective
  simp only [structuralResponseExtension]
  exact he.extend_apply (fun z => PF.g x z.1.1 z.2) 0 (⟨a, ha⟩, u)

/-- The full-data stratum conditional mean satisfies the same design-cell
integral identity as the observed regression. The result uses [the `hPF` condition](hyp:hPF), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hB` condition](hyp:hB), [the `hBunit` condition](hyp:hBunit). [This is the stated conclusion](goal).
-/
-- @node: fullDataResponseMean_setIntegral
lemma fullDataResponseMean_setIntegral
    (J : ℕ) (kappa cminus cplus pmin deltaBar : ℝ)
    (PF : FullDataLaw J)
    (hPF : BridgeFullDataClampModel PF kappa cminus cplus pmin deltaBar)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (x : Fin J) (B : Set ℝ) (hB : MeasurableSet B)
    (hBunit : B ⊆ Set.Icc (0 : ℝ) 1) :
    (PF.observedMargin.px x)⁻¹ *
        (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x ∧ z.1.A ∈ B},
          z.1.Y ∂PF.fullMeasure) =
      ∫ a in B, fullDataResponseMean PF x a * PF.observedMargin.pi x a := by
  classical
  let μU := Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2)
    ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
      PF.fullMeasure.restrict {z | z.1.X = x})
  let F : ℝ × PF.latentCarrier → ℝ := fun w =>
    if w.1 ∈ B then structuralResponseExtension PF hPF.consistency x w else 0
  have hF : Measurable F := by
    exact (structuralResponseExtension_measurable PF hPF.consistency x).piecewise
      (hB.preimage measurable_fst) measurable_const
  have hFbound : ∀ w, ‖F w‖ ≤ (1 : ℝ) := by
    intro w
    by_cases hw : w.1 ∈ B
    · have hunit := hBunit hw
      rw [show F w = PF.g x w.1 w.2 by
        simp [F, hw, structuralResponseExtension_eq PF hPF.consistency x w.1 hunit w.2]]
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hPF.consistency.2.1 x w.1 w.2 hunit).1],
        (hPF.consistency.2.1 x w.1 w.2 hunit).2⟩
    · simp [F, hw]
  have hprod := conditional_stratum_integral_prod J kappa cminus cplus
    pmin PF hPF.observedModel hPF.exchangeability hkappa hcplus hpmin x F hF 1 hFbound
  have hcell : MeasurableSet
      {z : ClampObs J × PF.latentCarrier | z.1.X = x ∧ z.1.A ∈ B} := by
    have hX : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.X) :=
      (measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst
    have hA : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.A) :=
      (measurable_fst.comp (measurable_snd.comp
        (Measurable.of_comap_le le_rfl))).comp measurable_fst
    exact (measurableSet_eq_fun
      hX measurable_const).inter (hB.preimage hA)
  have hstratum : MeasurableSet
      {z : ClampObs J × PF.latentCarrier | z.1.X = x} := by
    have hX : Measurable (fun z : ClampObs J × PF.latentCarrier => z.1.X) :=
      (measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst
    exact measurableSet_eq_fun
      hX measurable_const
  have hcellEq :
      (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x ∧ z.1.A ∈ B},
          z.1.Y ∂PF.fullMeasure) =
        ∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
          F (z.1.A, z.2) ∂PF.fullMeasure := by
    rw [← integral_indicator hcell, ← integral_indicator hstratum]
    apply integral_congr_ae
    filter_upwards [hPF.consistency.2.2] with z hz
    by_cases hx : z.1.X = x
    · by_cases hBa : z.1.A ∈ B
      · have ha : z.1.A ∈ Set.Icc (0 : ℝ) 1 := hBunit hBa
        simp only [Set.indicator_of_mem
          (show z ∈ {z : ClampObs J × PF.latentCarrier | z.1.X = x ∧ z.1.A ∈ B}
            from ⟨hx, hBa⟩),
          Set.indicator_of_mem
            (show z ∈ {z : ClampObs J × PF.latentCarrier | z.1.X = x} from hx)]
        rw [show F (z.1.A, z.2) = PF.g x z.1.A z.2 by
          simp [F, hBa,
            structuralResponseExtension_eq PF hPF.consistency x z.1.A ha z.2],
          ← hx, ← hz.2]
      · simp [F, hx, hBa]
    · simp [F, hx]
  have hsupp : ∀ᵐ a ∂conditionalTreatmentMeasure PF.observedMargin x,
      a ∈ Set.Icc (0 : ℝ) 1 := by
    unfold conditionalTreatmentMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Icc)
  calc
    _ = (PF.observedMargin.px x)⁻¹ *
        (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
          F (z.1.A, z.2) ∂PF.fullMeasure) := by rw [hcellEq]
    _ = ∫ a, ∫ u, F (a, u) ∂μU
          ∂conditionalTreatmentMeasure PF.observedMargin x := hprod
    _ = ∫ a, B.indicator (fullDataResponseMean PF x) a
          ∂conditionalTreatmentMeasure PF.observedMargin x := by
      apply integral_congr_ae
      filter_upwards [hsupp] with a ha
      by_cases hBa : a ∈ B
      · rw [Set.indicator_of_mem hBa]
        simp only [F, if_pos hBa]
        rw [integral_congr_ae (ae_of_all _ fun u =>
          structuralResponseExtension_eq PF hPF.consistency x a ha u)]
        exact conditional_stratum_latent_integral_eq_mean J kappa cminus
          cplus pmin PF hPF.observedModel hpmin hPF.consistency x a ha
      · rw [show (fun u => F (a, u)) = fun _ => 0 by
          funext u
          simp [F, hBa], integral_zero, Set.indicator_of_notMem hBa]
    _ = ∫ a in Set.Icc (0 : ℝ) 1,
        PF.observedMargin.pi x a * B.indicator (fullDataResponseMean PF x) a :=
      conditionalTreatment_integral_eq_density PF.observedMargin
        hPF.observedModel x _
    _ = ∫ a in B, fullDataResponseMean PF x a * PF.observedMargin.pi x a := by
      rw [← integral_indicator measurableSet_Icc, ← integral_indicator hB]
      apply integral_congr_ae
      filter_upwards with a
      by_cases hBa : a ∈ B
      · have ha := hBunit hBa
        simp [Set.indicator_of_mem hBa, ha, mul_comm]
      · by_cases ha : a ∈ Set.Icc (0 : ℝ) 1 <;>
          simp [Set.indicator_of_notMem hBa, ha]

/-- A continuous regression times the polynomially bounded treatment density
is integrable on the threshold interval. The result uses [the `hcond` condition](hyp:hcond), [the `hthin` condition](hyp:hthin), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hdelta` condition](hyp:hdelta), [the `hmu` condition](hyp:hmu). [This is the stated conclusion](goal).
-/
-- @node: continuous_mul_treatmentDensity_integrable
lemma continuous_mul_treatmentDensity_integrable
    (P : ClampLaw J) (kappa cminus cplus deltaBar : ℝ)
    (hcond : CondDensityLaw P)
    (hthin : PolynomialThinning P kappa cminus cplus)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus)
    (hdelta : deltaBar ≤ 1) (x : Fin J) (mu : ℝ → ℝ)
    (hmu : ContinuousOn mu (Set.Icc (0 : ℝ) deltaBar)) :
    IntegrableOn (fun a => mu a * P.pi x a) (Set.Icc (0 : ℝ) deltaBar) volume := by
  have hmuInt : IntegrableOn mu (Set.Icc (0 : ℝ) deltaBar) volume :=
    hmu.integrableOn_Icc
  have hpiMeas : AEStronglyMeasurable (P.pi x)
      (volume.restrict (Set.Icc (0 : ℝ) deltaBar)) := by
    exact (aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
      (hcond.1 x)).mono_measure
        (Measure.restrict_mono_set volume (Set.Icc_subset_Icc_right hdelta)) |>.aestronglyMeasurable
  have hpiBound : ∀ᵐ a ∂volume.restrict (Set.Icc (0 : ℝ) deltaBar),
      ‖P.pi x a‖ ≤ cplus := by
    filter_upwards [hcond.2.1 x |>.filter_mono
        (ae_mono (Measure.restrict_mono_set volume (Set.Icc_subset_Icc_right hdelta))),
      hthin x |>.filter_mono
        (ae_mono (Measure.restrict_mono_set volume (Set.Icc_subset_Icc_right hdelta))),
      ae_restrict_mem measurableSet_Icc] with a hnon henv ha
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact henv.2.trans (mul_le_of_le_one_right hcplus
      (Real.rpow_le_one ha.1 (ha.2.trans hdelta) hkappa))
  have h := hmuInt.bdd_mul hpiMeas hpiBound
  simpa only [IntegrableOn, mul_comm] using h

/-- Equality of all density-weighted cell integrals identifies two continuous
regressions pointwise on the threshold interval. The result uses [the `hcond` condition](hyp:hcond), [the `hthin` condition](hyp:hthin), [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hdelta` condition](hyp:hdelta), [the `hdeltaOne` condition](hyp:hdeltaOne), [the `hcont₁` condition](hyp:hcont₁), [the `hcont₂` condition](hyp:hcont₂), [the `hint₁` condition](hyp:hint₁), [the `hint₂` condition](hyp:hint₂), [the `hint` condition](hyp:hint). [This is the stated conclusion](goal).
-/
-- @node: continuous_regression_eq_of_density_integrals
lemma continuous_regression_eq_of_density_integrals
    (P : ClampLaw J) (kappa cminus cplus deltaBar : ℝ)
    (hcond : CondDensityLaw P)
    (hthin : PolynomialThinning P kappa cminus cplus)
    (hkappa : 0 ≤ kappa) (hcminus : 0 < cminus) (hcplus : 0 ≤ cplus)
    (hdelta : 0 < deltaBar) (hdeltaOne : deltaBar ≤ 1)
    (x : Fin J) (mu₁ mu₂ : ℝ → ℝ)
    (hcont₁ : ContinuousOn mu₁ (Set.Icc (0 : ℝ) deltaBar))
    (hcont₂ : ContinuousOn mu₂ (Set.Icc (0 : ℝ) deltaBar))
    (hint₁ : IntegrableOn (fun a => mu₁ a * P.pi x a)
      (Set.Icc (0 : ℝ) deltaBar) volume)
    (hint₂ : IntegrableOn (fun a => mu₂ a * P.pi x a)
      (Set.Icc (0 : ℝ) deltaBar) volume)
    (hint : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Icc (0 : ℝ) deltaBar →
      (∫ a in B, mu₁ a * P.pi x a) = ∫ a in B, mu₂ a * P.pi x a) :
    Set.EqOn mu₁ mu₂ (Set.Icc (0 : ℝ) deltaBar) := by
  have haeProd : (fun a => mu₁ a * P.pi x a) =ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) deltaBar)]
      fun a => mu₂ a * P.pi x a := by
    refine Integrable.ae_eq_of_forall_setIntegral_eq
      (fun a => mu₁ a * P.pi x a) (fun a => mu₂ a * P.pi x a)
      hint₁ hint₂ ?_
    intro S hS _
    rw [Measure.restrict_restrict hS]
    exact hint (S ∩ Set.Icc (0 : ℝ) deltaBar)
      (hS.inter measurableSet_Icc) inter_subset_right
  have hpiPos : ∀ᵐ a ∂volume.restrict (Set.Icc (0 : ℝ) deltaBar),
      0 < P.pi x a := by
    filter_upwards [hthin x |>.filter_mono
        (ae_mono (Measure.restrict_mono_set volume
          (Set.Icc_subset_Icc_right hdeltaOne))),
      ae_restrict_mem measurableSet_Icc,
      (volume.ae_ne 0).filter_mono (ae_mono Measure.restrict_le_self)] with a henv ha ha0
    have haPos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    exact lt_of_lt_of_le (mul_pos hcminus (Real.rpow_pos_of_pos haPos kappa)) henv.1
  have hae : mu₁ =ᵐ[volume.restrict (Set.Icc (0 : ℝ) deltaBar)] mu₂ := by
    filter_upwards [haeProd, hpiPos] with a heq hpos
    exact (mul_right_cancel₀ (ne_of_gt hpos)) heq
  exact volume.eqOn_Icc_of_ae_eq (ne_of_lt hdelta) hae hcont₁ hcont₂

/-- Set integrals of observed-coordinate functions agree under a full-data
law and its observed margin. The result uses [the `hS` condition](hyp:hS), [the `hf` condition](hyp:hf). [This is the stated conclusion](goal).
-/
-- @node: fullData_observed_setIntegral
lemma fullData_observed_setIntegral (PF : FullDataLaw J) (S : Set (ClampObs J))
    (hS : MeasurableSet S) (f : ClampObs J → ℝ) (hf : Measurable f) :
    (∫ z in (fun z : ClampObs J × PF.latentCarrier => z.1) ⁻¹' S,
      f z.1 ∂PF.fullMeasure) =
      ∫ o in S, f o ∂PF.observedMargin.dataMeasure := by
  rw [← integral_indicator (hS.preimage measurable_fst), ← integral_indicator hS]
  rw [← PF.margin_eq]
  exact (integral_map measurable_fst.aemeasurable
    (hf.indicator hS).aestronglyMeasurable).symm

/-- Full-data and fixed-Hölder observed regressions agree pointwise on the
declared threshold interval. The result uses [the `hPF` condition](hyp:hPF), [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: fullDataResponseMean_eq_mu
lemma fullDataResponseMean_eq_mu
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (PF : FullDataLaw J)
    (hPF : FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∀ (x : Fin J) (a : ℝ), a ∈ Set.Icc (0 : ℝ) deltaBar →
      fullDataResponseMean PF x a = PF.observedMargin.mu x a := by
  have hreg' := hreg
  rcases hreg' with
    ⟨_, _, hkappa, _, hcminus, _, hcplusLower, hpmin, _, hdelta,
      hdeltaOne, _, _⟩
  have hcplus : 0 ≤ cplus := le_trans (by linarith) hcplusLower
  intro x a ha
  have hEq : Set.EqOn (fullDataResponseMean PF x) (PF.observedMargin.mu x)
      (Set.Icc (0 : ℝ) deltaBar) := by
    apply continuous_regression_eq_of_density_integrals PF.observedMargin kappa
      cminus cplus deltaBar hPF.observedModel.condDensity
      hPF.observedModel.thinning hkappa hcminus hcplus hdelta hdeltaOne.le x
    · exact hPF.responseContinuity x
    · exact (hPF.observedModel.holder x).1.mono
        (Set.Icc_subset_Icc_right hdeltaOne.le)
    · exact continuous_mul_treatmentDensity_integrable PF.observedMargin kappa
        cminus cplus deltaBar hPF.observedModel.condDensity
        hPF.observedModel.thinning hkappa hcplus hdeltaOne.le x _
        (hPF.responseContinuity x)
    · exact continuous_mul_treatmentDensity_integrable PF.observedMargin kappa
        cminus cplus deltaBar hPF.observedModel.condDensity
        hPF.observedModel.thinning hkappa hcplus hdeltaOne.le x _
        ((hPF.observedModel.holder x).1.mono
          (Set.Icc_subset_Icc_right hdeltaOne.le))
    · intro B hB hBdelta
      have hBunit : B ⊆ Set.Icc (0 : ℝ) 1 :=
        hBdelta.trans (Set.Icc_subset_Icc_right hdeltaOne.le)
      have hfull := fullDataResponseMean_setIntegral J kappa cminus
        cplus pmin deltaBar PF hPF.toBridge hkappa hcplus hpmin x B hB hBunit
      have hobs := holderRegression_setIntegral PF.observedMargin
        hPF.observedModel hkappa hcplus hpmin x B hB hBunit
      have hmargin :
          (∫ z in {z : ClampObs J × PF.latentCarrier |
              z.1.X = x ∧ z.1.A ∈ B}, z.1.Y ∂PF.fullMeasure) =
            ∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B},
              o.Y ∂PF.observedMargin.dataMeasure := by
        exact fullData_observed_setIntegral PF
          {o : ClampObs J | o.X = x ∧ o.A ∈ B}
          (by
            exact (measurableSet_eq_fun
              (measurable_fst.comp (Measurable.of_comap_le le_rfl)) measurable_const).inter
              (hB.preimage (measurable_fst.comp (measurable_snd.comp
                (Measurable.of_comap_le le_rfl))))) _ clampOutcome_measurable
      have hpx : 0 < PF.observedMargin.px x :=
        lt_of_lt_of_le hpmin (hPF.observedModel.stratumMass x).2
      calc
        (∫ a in B, fullDataResponseMean PF x a * PF.observedMargin.pi x a) =
            (PF.observedMargin.px x)⁻¹ *
              (∫ z in {z : ClampObs J × PF.latentCarrier |
                z.1.X = x ∧ z.1.A ∈ B}, z.1.Y ∂PF.fullMeasure) := hfull.symm
        _ = (PF.observedMargin.px x)⁻¹ *
              (∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B},
                o.Y ∂PF.observedMargin.dataMeasure) := by rw [hmargin]
        _ = (PF.observedMargin.px x)⁻¹ * (PF.observedMargin.px x *
              ∫ a in B, PF.observedMargin.mu x a * PF.observedMargin.pi x a) := by
                rw [hobs]
        _ = ∫ a in B, PF.observedMargin.mu x a * PF.observedMargin.pi x a := by
          field_simp
  exact hEq ha

/-- Full-data and continuity-only observed regressions agree pointwise on the
declared threshold interval. The result uses [the `hPF` condition](hyp:hPF), [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: fullDataResponseMean_eq_contRegression
lemma fullDataResponseMean_eq_contRegression
    (J : ℕ) (kappa cminus cplus pmin deltaBar : ℝ)
    (PF : FullDataLaw J)
    (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar) :
    ∀ (x : Fin J) (a : ℝ), a ∈ Set.Icc (0 : ℝ) deltaBar →
      fullDataResponseMean PF x a =
        contRegression PF.observedMargin kappa cminus cplus pmin deltaBar
          hPF.observedModel x a := by
  rcases hreg with ⟨_, hkappa, hcminus, _, hcplusLower, hpmin, _, hdelta, hdeltaOne⟩
  have hcplus : 0 ≤ cplus := le_trans (by linarith) hcplusLower
  let mu := contRegression PF.observedMargin kappa cminus cplus pmin deltaBar
    hPF.observedModel
  have hcont : ∀ x, ContinuousOn (mu x) (Set.Icc (0 : ℝ) deltaBar) := by
    simpa [mu, contRegression] using
      (Classical.choose_spec hPF.observedModel.continuousVersion).1
  have hver : PF.observedMargin.dataMeasure[(fun o : ClampObs J => o.Y) |
      MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[PF.observedMargin.dataMeasure] fun o => mu o.X o.A := by
    simpa [mu, contRegression] using
      (Classical.choose_spec hPF.observedModel.continuousVersion).2
  intro x a ha
  apply continuous_regression_eq_of_density_integrals PF.observedMargin kappa
    cminus cplus deltaBar hPF.observedModel.condDensity hPF.observedModel.thinning
    hkappa hcminus hcplus hdelta hdeltaOne.le x
      (fullDataResponseMean PF x) (mu x)
      (hPF.responseContinuity x) (hcont x)
  · exact continuous_mul_treatmentDensity_integrable PF.observedMargin kappa
      cminus cplus deltaBar hPF.observedModel.condDensity hPF.observedModel.thinning
      hkappa hcplus hdeltaOne.le x _ (hPF.responseContinuity x)
  · exact continuous_mul_treatmentDensity_integrable PF.observedMargin kappa
      cminus cplus deltaBar hPF.observedModel.condDensity hPF.observedModel.thinning
      hkappa hcplus hdeltaOne.le x _ (hcont x)
  · intro B hB hBdelta
    have hBunit : B ⊆ Set.Icc (0 : ℝ) 1 :=
      hBdelta.trans (Set.Icc_subset_Icc_right hdeltaOne.le)
    have hfull := fullDataResponseMean_setIntegral J kappa cminus cplus pmin
      deltaBar PF hPF.toBridge hkappa hcplus hpmin x B hB hBunit
    have hweighted := continuous_mul_treatmentDensity_integrable PF.observedMargin
      kappa cminus cplus deltaBar hPF.observedModel.condDensity
      hPF.observedModel.thinning hkappa hcplus hdeltaOne.le x (mu x) (hcont x)
    have hmuInt : Integrable (B.indicator (mu x))
        (conditionalTreatmentMeasure PF.observedMargin x) := by
      unfold conditionalTreatmentMeasure
      have hpiAe : AEMeasurable (fun t : ℝ => ENNReal.ofReal
          (PF.observedMargin.pi x t))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
          (hPF.observedModel.condDensity.1 x)).ennreal_ofReal
      refine (integrable_withDensity_iff_integrable_smul₀' hpiAe
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2 ?_
      have hi := (hweighted.mono_set hBdelta).integrable_indicator hB
      have hir := hi.mono_measure
        (Measure.restrict_le_self (μ := volume) (s := Set.Icc (0 : ℝ) 1))
      apply hir.congr
      filter_upwards [hPF.observedModel.condDensity.2.1 x] with t ht
      simp [Set.indicator, ht, mul_comm]
    have hobs := regressionVersion_setIntegral PF.observedMargin
      hPF.observedModel.toBridge hkappa hcplus hpmin mu hver x B hB hBunit hmuInt
    have hmargin := fullData_observed_setIntegral PF
      {o : ClampObs J | o.X = x ∧ o.A ∈ B}
      ((measurableSet_eq_fun
        (measurable_fst.comp (Measurable.of_comap_le le_rfl)) measurable_const).inter
        (hB.preimage (measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))))) _ clampOutcome_measurable
    have hmargin' :
        (∫ z in {z : ClampObs J × PF.latentCarrier |
            z.1.X = x ∧ z.1.A ∈ B}, z.1.Y ∂PF.fullMeasure) =
          ∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B},
            o.Y ∂PF.observedMargin.dataMeasure := by
      have hs : {z : ClampObs J × PF.latentCarrier |
          z.1.X = x ∧ z.1.A ∈ B} =
          (fun z : ClampObs J × PF.latentCarrier => z.1) ⁻¹'
            {o : ClampObs J | o.X = x ∧ o.A ∈ B} := by
        ext z
        rfl
      rw [hs]
      exact hmargin
    have hpx : 0 < PF.observedMargin.px x :=
      lt_of_lt_of_le hpmin (hPF.observedModel.stratumMass x).2
    calc
      (∫ t in B, fullDataResponseMean PF x t * PF.observedMargin.pi x t) =
          (PF.observedMargin.px x)⁻¹ *
            (∫ z in {z : ClampObs J × PF.latentCarrier |
              z.1.X = x ∧ z.1.A ∈ B}, z.1.Y ∂PF.fullMeasure) := hfull.symm
      _ = (PF.observedMargin.px x)⁻¹ *
            (∫ o in {o : ClampObs J | o.X = x ∧ o.A ∈ B},
              o.Y ∂PF.observedMargin.dataMeasure) := by rw [hmargin']
      _ = (PF.observedMargin.px x)⁻¹ * (PF.observedMargin.px x *
            ∫ t in B, mu x t * PF.observedMargin.pi x t) := by rw [hobs]
      _ = ∫ t in B, mu x t * PF.observedMargin.pi x t := by field_simp
  · exact ha

/-- Simultaneous consistency gives the pathwise lower-clamp decomposition. The result uses [the `hcons` condition](hyp:hcons), [the `hsupp` condition](hyp:hsupp), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: causalClamp_pathwise
lemma causalClamp_pathwise
    (PF : FullDataLaw J) (hcons : LatentResponseConsistency PF)
    (hsupp : ∀ᵐ o ∂PF.observedMargin.dataMeasure, o.A ∈ Set.Icc (0 : ℝ) 1)
    (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂PF.fullMeasure,
      PF.pot (clampPolicy delta z.1.A) z =
        (if delta < z.1.A then z.1.Y else 0) +
          (if z.1.A ≤ delta then PF.pot delta z else 0) := by
  have hsuppFull : ∀ᵐ z ∂PF.fullMeasure, z.1.A ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← PF.margin_eq] at hsupp
    exact (MeasureTheory.ae_map_iff
      (show AEMeasurable (fun z : ClampObs J × PF.latentCarrier => z.1) PF.fullMeasure
        from measurable_fst.aemeasurable)
      (measurableSet_Icc.preimage
        (measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))))).mp hsupp
  filter_upwards [hcons.2.2, hsuppFull] with z hz ha
  by_cases hlt : delta < z.1.A
  · have hclamp : clampPolicy delta z.1.A = z.1.A := by
      simp [clampPolicy, max_eq_left hlt.le]
    rw [if_pos hlt, if_neg (not_le.mpr hlt), hclamp, hz.1 z.1.A ha, hz.2]
    ring
  · have hle : z.1.A ≤ delta := le_of_not_gt hlt
    have hclamp : clampPolicy delta z.1.A = delta := by
      simp [clampPolicy, max_eq_right hle]
    rw [if_neg hlt, if_pos hle, hclamp]
    ring

/-- The expectation of the clamped atom contribution is the finite-stratum
sum of atom masses times full-data response means. The result uses [the `hPF` condition](hyp:hPF), [the `hkappa` condition](hyp:hkappa), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hdeltaBarOne` condition](hyp:hdeltaBarOne), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: fullData_clampAtom_integral_eq
lemma fullData_clampAtom_integral_eq
    (J : ℕ) (kappa cminus cplus pmin deltaBar : ℝ)
    (PF : FullDataLaw J)
    (hPF : BridgeFullDataClampModel PF kappa cminus cplus pmin deltaBar)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (hdeltaBarOne : deltaBar ≤ 1)
    (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    (∫ z, if z.1.A ≤ delta then PF.pot delta z else 0 ∂PF.fullMeasure) =
      ∑ x : Fin J, PF.observedMargin.px x *
        atomMass PF.observedMargin x delta * fullDataResponseMean PF x delta := by
  classical
  have hdeltaUnit : delta ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hdelta.1, hdelta.2.trans hdeltaBarOne⟩
  let f : ClampObs J × PF.latentCarrier → ℝ := fun z =>
    if z.1.A ≤ delta then PF.pot delta z else 0
  have hfMeas : Measurable f := by
    have hpot : Measurable (fun z : ClampObs J × PF.latentCarrier => PF.pot delta z) :=
      PF.pot_jointlyMeasurable.comp (measurable_const.prodMk measurable_id)
    exact hpot.piecewise
      (measurableSet_Iic.preimage
        ((measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))).comp measurable_fst)) measurable_const
  have hfInt : Integrable f PF.fullMeasure := by
    let _ := PF.probability
    refine Integrable.of_bound hfMeas.aestronglyMeasurable 1 ?_
    filter_upwards [hPF.consistency.2.2] with z hz
    by_cases hle : z.1.A ≤ delta
    · simp only [f, if_pos hle, Real.norm_eq_abs]
      rw [hz.1 delta hdeltaUnit]
      exact abs_le.2 ⟨by linarith [(hPF.consistency.2.1 z.1.X delta z.2 hdeltaUnit).1],
        (hPF.consistency.2.1 z.1.X delta z.2 hdeltaUnit).2⟩
    · simp [f, hle]
  have hXMeas : ∀ x : Fin J, MeasurableSet
      ((fun z : ClampObs J × PF.latentCarrier => z.1.X) ⁻¹' {x}) := by
    intro x
    exact (measurableSet_singleton x).preimage
      ((measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst)
  rw [show (∫ z, if z.1.A ≤ delta then PF.pot delta z else 0 ∂PF.fullMeasure) =
      ∫ z, f z ∂PF.fullMeasure from rfl,
    Causalean.Mathlib.MeasureTheory.integral_eq_sum_setIntegral_fiber hXMeas hfInt]
  apply Finset.sum_congr rfl
  intro x _
  let F : ℝ × PF.latentCarrier → ℝ := fun w =>
    if w.1 ≤ delta then structuralResponseExtension PF hPF.consistency x (delta, w.2) else 0
  have hF : Measurable F := by
    have hg : Measurable (fun w : ℝ × PF.latentCarrier =>
        structuralResponseExtension PF hPF.consistency x (delta, w.2)) :=
      (structuralResponseExtension_measurable PF hPF.consistency x).comp
        (measurable_const.prodMk measurable_snd)
    exact hg.piecewise (measurableSet_Iic.preimage measurable_fst) measurable_const
  have hFbound : ∀ w, ‖F w‖ ≤ (1 : ℝ) := by
    intro w
    by_cases hle : w.1 ≤ delta
    · simp only [F, if_pos hle]
      rw [structuralResponseExtension_eq PF hPF.consistency x delta hdeltaUnit w.2,
        Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hPF.consistency.2.1 x delta w.2 hdeltaUnit).1],
        (hPF.consistency.2.1 x delta w.2 hdeltaUnit).2⟩
    · simp [F, hle]
  have hprod := conditional_stratum_integral_prod J kappa cminus cplus
    pmin PF hPF.observedModel hPF.exchangeability hkappa hcplus hpmin x F hF 1 hFbound
  have hstratum : MeasurableSet
      {z : ClampObs J × PF.latentCarrier | z.1.X = x} := by
    exact measurableSet_eq_fun
      ((measurable_fst.comp (Measurable.of_comap_le le_rfl)).comp measurable_fst)
      measurable_const
  have hcell : (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x}, f z
      ∂PF.fullMeasure) =
      ∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x}, F (z.1.A, z.2)
        ∂PF.fullMeasure := by
    apply setIntegral_congr_ae hstratum
    exact hPF.consistency.2.2.mono (fun z hz hx => by
      by_cases hle : z.1.A ≤ delta
      · simp only [f, F, if_pos hle]
        rw [structuralResponseExtension_eq PF hPF.consistency x delta hdeltaUnit z.2,
          ← hx, ← hz.1 delta hdeltaUnit]
      · simp [f, F, hle])
  change (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x}, f z
      ∂PF.fullMeasure) = _
  rw [hcell]
  have hrhs : (∫ a, ∫ u, F (a, u)
      ∂Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2)
        ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
          PF.fullMeasure.restrict {z | z.1.X = x})
      ∂conditionalTreatmentMeasure PF.observedMargin x) =
      atomMass PF.observedMargin x delta * fullDataResponseMean PF x delta := by
    rw [show (∫ a, ∫ u, F (a, u)
        ∂Measure.map (fun z : ClampObs J × PF.latentCarrier => z.2)
          ((ENNReal.ofReal (PF.observedMargin.px x))⁻¹ •
            PF.fullMeasure.restrict {z | z.1.X = x})
        ∂conditionalTreatmentMeasure PF.observedMargin x) =
        ∫ a, Set.indicator (Set.Iic delta) (fun _ => fullDataResponseMean PF x delta) a
          ∂conditionalTreatmentMeasure PF.observedMargin x by
      apply integral_congr_ae
      filter_upwards with a
      by_cases hle : a ≤ delta
      · simp only [F, if_pos hle, Set.indicator_of_mem
          (show a ∈ Set.Iic delta from hle)]
        rw [integral_congr_ae (ae_of_all _ fun u =>
          structuralResponseExtension_eq PF hPF.consistency x delta hdeltaUnit u)]
        exact conditional_stratum_latent_integral_eq_mean J kappa cminus
          cplus pmin PF hPF.observedModel hpmin hPF.consistency x delta hdeltaUnit
      · simp [F, hle],
      conditionalTreatment_integral_eq_density PF.observedMargin hPF.observedModel x]
    simp only [atomMass]
    rw [← integral_indicator measurableSet_Icc]
    calc
      (∫ a, (Set.Icc (0 : ℝ) 1).indicator
          (fun a => PF.observedMargin.pi x a *
            (Set.Iic delta).indicator (fun _ => fullDataResponseMean PF x delta) a) a) =
          ∫ a, (Set.Icc (0 : ℝ) delta).indicator
            (fun a => PF.observedMargin.pi x a * fullDataResponseMean PF x delta) a := by
        congr 1
        funext a
        by_cases ha : a ∈ Set.Icc (0 : ℝ) delta
        · have haUnit : a ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨ha.1, ha.2.trans hdeltaUnit.2⟩
          have hIic : a ∈ Set.Iic delta := ha.2
          simp [Set.indicator, ha, haUnit, hIic]
        · by_cases haUnit : a ∈ Set.Icc (0 : ℝ) 1
          · by_cases hle : a ≤ delta
            · exact False.elim (ha ⟨haUnit.1, hle⟩)
            · have hnotIic : a ∉ Set.Iic delta := hle
              simp [Set.indicator, ha, haUnit, hnotIic]
          · simp [Set.indicator, ha, haUnit]
      _ = ∫ a in Set.Icc (0 : ℝ) delta,
          PF.observedMargin.pi x a * fullDataResponseMean PF x delta :=
        integral_indicator measurableSet_Icc
      _ = (∫ a in Set.Icc (0 : ℝ) delta, PF.observedMargin.pi x a) *
          fullDataResponseMean PF x delta := by rw [integral_mul_const]
  have hpx : 0 < PF.observedMargin.px x :=
    lt_of_lt_of_le hpmin (hPF.observedModel.stratumMass x).2
  rw [hrhs] at hprod
  field_simp at hprod ⊢
  exact hprod

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
