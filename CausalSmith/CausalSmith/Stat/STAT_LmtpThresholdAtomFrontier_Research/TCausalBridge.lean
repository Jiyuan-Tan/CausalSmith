/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.CausalBridgeIdentification
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.RegressionVersion
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Full-data to observed-data clamp bridge

The theorem includes the stratumwise product identity, pointwise identification,
support, simultaneous pathwise clamp decomposition, and target equality.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set

noncomputable section


/-- Latent randomization and structural-mean continuity identify the observed
continuous regression on the declared threshold range and hence identify the
clamp mean. Joint measurability of the potential-outcome process is part of
`FullDataLaw`, and all remaining causal conditions are supplied by the bundled
full-data model membership. The result uses [the `hPF` condition](hyp:hPF), [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: prop:causal-bridge
theorem causal_bridge
    (J : ℕ)
    (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (PF : FullDataLaw J)
    (hPF : FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    (∀ (x : Fin J) (B : Set ℝ), MeasurableSet B → B ⊆ Set.Icc (0 : ℝ) 1 →
      (PF.observedMargin.px x)⁻¹ *
          (∫ z in
            {z : ClampObs J × PF.latentCarrier | z.1.X = x ∧ z.1.A ∈ B},
            z.1.Y ∂PF.fullMeasure) =
        ∫ a in B, fullDataResponseMean PF x a * PF.observedMargin.pi x a) ∧
    (∀ (x : Fin J) (a : ℝ), a ∈ Set.Icc (0 : ℝ) deltaBar →
      fullDataResponseMean PF x a = PF.observedMargin.mu x a) ∧
    ∀ delta : ℝ, delta ∈ Set.Icc (0 : ℝ) deltaBar →
      (∀ x : Fin J, ∀ᵐ a ∂conditionalTreatmentMeasure PF.observedMargin x,
        IsConditionalSupportPoint (conditionalTreatmentMeasure PF.observedMargin x)
          (clampPolicy delta a)) ∧
      (∀ᵐ z ∂PF.fullMeasure,
        PF.pot (clampPolicy delta z.1.A) z =
          (if delta < z.1.A then z.1.Y else 0) +
            (if z.1.A ≤ delta then PF.pot delta z else 0)) ∧
      causalClampMean PF delta =
          retainedMean PF.observedMargin delta +
            ∑ x : Fin J, PF.observedMargin.px x *
              atomMass PF.observedMargin x delta * PF.observedMargin.mu x delta ∧
      causalClampMean PF delta = clampFunctional PF.observedMargin delta := by
  have hreg' := hreg
  rcases hreg' with
    ⟨_, _, hkappa, _, _, _, hcplusLower, hpmin, _, _, hdeltaBarOne, _, _⟩
  have hcplus : 0 ≤ cplus := le_trans (by linarith) hcplusLower
  have hmean := fullDataResponseMean_eq_mu J beta kappa L cminus cplus pmin
    deltaBar alpha PF hPF hreg
  refine ⟨?_, hmean, ?_⟩
  · intro x B hB hBunit
    exact fullDataResponseMean_setIntegral J kappa cminus cplus pmin deltaBar
      PF hPF.toBridge hkappa hcplus hpmin x B hB hBunit
  · intro delta hdelta
    have hdeltaUnit : delta ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨hdelta.1, hdelta.2.trans hdeltaBarOne.le⟩
    have hsupport : ∀ x : Fin J, ∀ᵐ a ∂conditionalTreatmentMeasure PF.observedMargin x,
        IsConditionalSupportPoint (conditionalTreatmentMeasure PF.observedMargin x)
          (clampPolicy delta a) := fun x =>
      clamp_policy_support PF.observedMargin beta kappa L cminus cplus pmin
        deltaBar alpha hPF.observedModel hreg x delta hdelta
    have hpath := causalClamp_pathwise PF hPF.consistency
      hPF.observedModel.treatmentSupport delta hdeltaUnit
    refine ⟨hsupport, hpath, ?_⟩
    have hYFull : ∀ᵐ z ∂PF.fullMeasure, z.1.Y ∈ Set.Icc (0 : ℝ) 1 := by
      have hsupp := hPF.observedModel.outcomeSupport
      rw [← PF.margin_eq] at hsupp
      exact (MeasureTheory.ae_map_iff measurable_fst.aemeasurable
        (measurableSet_Icc.preimage clampOutcome_measurable)).mp
          hsupp
    let fRet : ClampObs J × PF.latentCarrier → ℝ := fun z =>
      if delta < z.1.A then z.1.Y else 0
    let fAtom : ClampObs J × PF.latentCarrier → ℝ := fun z =>
      if z.1.A ≤ delta then PF.pot delta z else 0
    have hfRetMeas : Measurable fRet := by
      exact (clampOutcome_measurable.comp measurable_fst).piecewise
        (measurableSet_Ioi.preimage
          ((measurable_fst.comp (measurable_snd.comp
            (Measurable.of_comap_le le_rfl))).comp measurable_fst)) measurable_const
    have hfAtomMeas : Measurable fAtom := by
      have hp : Measurable (fun z : ClampObs J × PF.latentCarrier => PF.pot delta z) :=
        PF.pot_jointlyMeasurable.comp (measurable_const.prodMk measurable_id)
      exact hp.piecewise
        (measurableSet_Iic.preimage
          ((measurable_fst.comp (measurable_snd.comp
            (Measurable.of_comap_le le_rfl))).comp measurable_fst)) measurable_const
    let _ := PF.probability
    have hfRetInt : Integrable fRet PF.fullMeasure := by
      refine Integrable.of_bound hfRetMeas.aestronglyMeasurable 1 ?_
      filter_upwards [hYFull] with z hY
      by_cases hlt : delta < z.1.A
      · simp only [fRet, if_pos hlt, Real.norm_eq_abs]
        exact abs_le.2 ⟨by linarith [hY.1], hY.2⟩
      · simp [fRet, hlt]
    have hfAtomInt : Integrable fAtom PF.fullMeasure := by
      refine Integrable.of_bound hfAtomMeas.aestronglyMeasurable 1 ?_
      filter_upwards [hPF.consistency.2.2] with z hz
      by_cases hle : z.1.A ≤ delta
      · simp only [fAtom, if_pos hle, Real.norm_eq_abs]
        rw [hz.1 delta hdeltaUnit]
        exact abs_le.2 ⟨by
            linarith [(hPF.consistency.2.1 z.1.X delta z.2 hdeltaUnit).1],
          (hPF.consistency.2.1 z.1.X delta z.2 hdeltaUnit).2⟩
      · simp [fAtom, hle]
    have hret : (∫ z, fRet z ∂PF.fullMeasure) =
        retainedMean PF.observedMargin delta := by
      have hm : Measurable (fun o : ClampObs J =>
          if delta < o.A then o.Y else 0) := by
        exact clampOutcome_measurable.piecewise
          (measurableSet_Ioi.preimage
            (measurable_fst.comp (measurable_snd.comp
              (Measurable.of_comap_le le_rfl)))) measurable_const
      have h := fullData_observed_setIntegral PF Set.univ MeasurableSet.univ
        (fun o : ClampObs J => if delta < o.A then o.Y else 0) hm
      simpa [fRet, retainedMean, Set.indicator] using h
    have hatom := fullData_clampAtom_integral_eq J kappa cminus cplus
      pmin deltaBar PF hPF.toBridge hkappa hcplus hpmin hdeltaBarOne.le delta hdelta
    have hpsi : causalClampMean PF delta =
        retainedMean PF.observedMargin delta +
          ∑ x : Fin J, PF.observedMargin.px x *
            atomMass PF.observedMargin x delta * fullDataResponseMean PF x delta := by
      calc
        causalClampMean PF delta = ∫ z, fRet z + fAtom z ∂PF.fullMeasure := by
          apply integral_congr_ae
          exact hpath.mono (fun z hz => by simpa [causalClampMean, fRet, fAtom] using hz)
        _ = (∫ z, fRet z ∂PF.fullMeasure) + ∫ z, fAtom z ∂PF.fullMeasure := by
          rw [integral_add hfRetInt hfAtomInt]
        _ = _ := by rw [hret, hatom]
    have htarget : causalClampMean PF delta =
        retainedMean PF.observedMargin delta +
          ∑ x : Fin J, PF.observedMargin.px x *
            atomMass PF.observedMargin x delta * PF.observedMargin.mu x delta := by
      rw [hpsi]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [hmean x delta hdelta]
    exact ⟨htarget, by simpa [clampFunctional] using htarget⟩

/-! PRIOR PROOF (carry-over): the preceding scaffold proved the analogous
fixed-carrier statement from conditional-L1 path continuity on all of `[0,1]`.
That proof is intentionally not reused as a proof of this weaker, differently
typed mean-continuity statement; its measure-factorization lemmas remain in
`Helpers.CausalBridgeMeasure`. -/

/-- The same latent-response argument identifies the qualitative continuous
regression version and the continuity-only clamp functional, without imposing
a fixed-Hölder observed model or a shared latent carrier. The result uses [the `hPF` condition](hyp:hPF), [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: prop:continuity-causal-bridge
theorem continuity_causal_bridge
    (J : ℕ) (kappa cminus cplus pmin deltaBar : ℝ)
    (PF : FullDataLaw J)
    (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar) :
    (∀ (x : Fin J) (a : ℝ), a ∈ Set.Icc (0 : ℝ) deltaBar →
      fullDataResponseMean PF x a =
        contRegression PF.observedMargin kappa cminus cplus pmin deltaBar
          hPF.observedModel x a) ∧
    ∀ delta : ℝ, delta ∈ Set.Icc (0 : ℝ) deltaBar →
      causalClampMean PF delta =
        contClampFunctional PF.observedMargin kappa cminus cplus pmin deltaBar
          hPF.observedModel delta := by
  have hreg' := hreg
  rcases hreg' with
    ⟨_, hkappa, _, _, hcplusLower, hpmin, _, _, hdeltaBarOne⟩
  have hcplus : 0 ≤ cplus := le_trans (by linarith) hcplusLower
  have hmean := fullDataResponseMean_eq_contRegression J kappa cminus cplus
    pmin deltaBar PF hPF hreg
  refine ⟨hmean, ?_⟩
  intro delta hdelta
  have hdeltaUnit : delta ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hdelta.1, hdelta.2.trans hdeltaBarOne.le⟩
  have hpath := causalClamp_pathwise PF hPF.consistency
    hPF.observedModel.treatmentSupport delta hdeltaUnit
  have hYFull : ∀ᵐ z ∂PF.fullMeasure, z.1.Y ∈ Set.Icc (0 : ℝ) 1 := by
    have hsupp := hPF.observedModel.outcomeSupport
    rw [← PF.margin_eq] at hsupp
    exact (MeasureTheory.ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Icc.preimage clampOutcome_measurable)).mp hsupp
  let fRet : ClampObs J × PF.latentCarrier → ℝ := fun z =>
    if delta < z.1.A then z.1.Y else 0
  let fAtom : ClampObs J × PF.latentCarrier → ℝ := fun z =>
    if z.1.A ≤ delta then PF.pot delta z else 0
  have hfRetMeas : Measurable fRet := by
    exact (clampOutcome_measurable.comp measurable_fst).piecewise
      (measurableSet_Ioi.preimage
        ((measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))).comp measurable_fst)) measurable_const
  have hfAtomMeas : Measurable fAtom := by
    have hp : Measurable (fun z : ClampObs J × PF.latentCarrier => PF.pot delta z) :=
      PF.pot_jointlyMeasurable.comp (measurable_const.prodMk measurable_id)
    exact hp.piecewise
      (measurableSet_Iic.preimage
        ((measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))).comp measurable_fst)) measurable_const
  let _ := PF.probability
  have hfRetInt : Integrable fRet PF.fullMeasure := by
    refine Integrable.of_bound hfRetMeas.aestronglyMeasurable 1 ?_
    filter_upwards [hYFull] with z hY
    by_cases hlt : delta < z.1.A
    · simp only [fRet, if_pos hlt, Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [hY.1], hY.2⟩
    · simp [fRet, hlt]
  have hfAtomInt : Integrable fAtom PF.fullMeasure := by
    refine Integrable.of_bound hfAtomMeas.aestronglyMeasurable 1 ?_
    filter_upwards [hPF.consistency.2.2] with z hz
    by_cases hle : z.1.A ≤ delta
    · simp only [fAtom, if_pos hle, Real.norm_eq_abs]
      rw [hz.1 delta hdeltaUnit]
      exact abs_le.2 ⟨by
          linarith [(hPF.consistency.2.1 z.1.X delta z.2 hdeltaUnit).1],
        (hPF.consistency.2.1 z.1.X delta z.2 hdeltaUnit).2⟩
    · simp [fAtom, hle]
  have hret : (∫ z, fRet z ∂PF.fullMeasure) =
      retainedMean PF.observedMargin delta := by
    have hm : Measurable (fun o : ClampObs J =>
        if delta < o.A then o.Y else 0) := by
      exact clampOutcome_measurable.piecewise
        (measurableSet_Ioi.preimage
          (measurable_fst.comp (measurable_snd.comp
            (Measurable.of_comap_le le_rfl)))) measurable_const
    have h := fullData_observed_setIntegral PF Set.univ MeasurableSet.univ
      (fun o : ClampObs J => if delta < o.A then o.Y else 0) hm
    simpa [fRet, retainedMean, Set.indicator] using h
  have hatom := fullData_clampAtom_integral_eq J kappa cminus cplus pmin
    deltaBar PF hPF.toBridge hkappa hcplus hpmin hdeltaBarOne.le delta hdelta
  have hpsi : causalClampMean PF delta =
      retainedMean PF.observedMargin delta +
        ∑ x : Fin J, PF.observedMargin.px x *
          atomMass PF.observedMargin x delta * fullDataResponseMean PF x delta := by
    calc
      causalClampMean PF delta = ∫ z, fRet z + fAtom z ∂PF.fullMeasure := by
        apply integral_congr_ae
        exact hpath.mono (fun z hz => by
          simpa [causalClampMean, fRet, fAtom] using hz)
      _ = (∫ z, fRet z ∂PF.fullMeasure) + ∫ z, fAtom z ∂PF.fullMeasure := by
        rw [integral_add hfRetInt hfAtomInt]
      _ = _ := by rw [hret, hatom]
  rw [hpsi]
  unfold contClampFunctional
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [hmean x delta hdelta]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
