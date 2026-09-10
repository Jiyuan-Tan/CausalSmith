/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxMembership
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core

/-!
# Continuity-only canonical witnesses

This file places the canonical Bernoulli regression laws in the qualitative
continuity model without imposing a common modulus of continuity.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set

noncomputable section

private lemma measurable_obs_design_cont {J : ℕ} :
    Measurable (fun o : ClampObs J => (o.X, o.A)) := by
  let h : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_fst.comp h).prodMk (measurable_fst.comp (measurable_snd.comp h))

/-- A bounded continuous Bernoulli regression on the canonical design law is
a member of the continuity-only model. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hqmeas` condition](hyp:hqmeas), [the `hqbound` condition](hyp:hqbound), [the `hcont` condition](hyp:hcont). [This is the stated conclusion](goal).
-/
lemma minimaxClampModel_continuous
    (J : ℕ) (kappa cminus cplus pmin deltaBar : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (hcminus : cminus ≤ kappa + 1) (hcplus : kappa + 1 ≤ cplus)
    (hpmin : pmin ≤ 1 / (J : ℝ))
    (q : ℝ → ℝ) (hqmeas : Measurable q) (hqbound : ∀ a, |q a| ≤ 1 / 2)
    (hcont : ContinuousOn (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) deltaBar)) :
    ContClampModel (minimaxClampLaw J kappa (fun p => q p.2))
      kappa cminus cplus pmin deltaBar := by
  let g : Fin J × ℝ → ℝ := fun p => q p.2
  have hgmeas : Measurable g := hqmeas.comp measurable_snd
  have hgbound : ∀ p, |g p| ≤ 1 / 2 := fun p => hqbound p.2
  have hprob := minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa g hgmeas hgbound
  refine ⟨hprob, minimaxDataMeasure_ae_treatment J kappa g hgmeas hgbound,
    (minimaxDataMeasure_ae_bernoulli J kappa g hgmeas).mono (fun o ho => by
      rcases ho with ho | ho <;> simp [ho]), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      fun_prop
    · intro x
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      exact mul_nonneg (by linarith) (Real.rpow_nonneg ha.1 _)
    · intro x
      constructor
      · change 1 / (J : ℝ) = _
        change 1 / (J : ℝ) =
          (Measure.map (fun o : ClampObs J => o.X)
            (minimaxDataMeasure J kappa g)).real {x}
        rw [minimaxDataMeasure_map_X J kappa hJ hkappa g hgmeas hgbound]
        exact (minimaxStratumMeasure_real_singleton J hJ x).symm
      · intro B hB hsub
        have hevent : {o : ClampObs J | o.X = x ∧ o.A ∈ B} =
            (fun o => (o.X, o.A)) ⁻¹' ({x} ×ˢ B) := by ext o; simp
        rw [hevent]
        have hrect : MeasurableSet (({x} : Set (Fin J)) ×ˢ B) :=
          (measurableSet_singleton x).prod hB
        change (minimaxDataMeasure J kappa g).real
          {o : ClampObs J | o.X = x ∧ o.A ∈ B} = _
        rw [hevent, measureReal_def, ← Measure.map_apply measurable_obs_design_cont hrect,
          minimaxDataMeasure_map_design J kappa g hgmeas hgbound]
        change (minimaxDesignMeasure J kappa).real ({x} ×ˢ B) = _
        rw [minimaxDesignMeasure_real_rectangle J kappa hJ hkappa x B hB hsub]
        rfl
  · intro x
    constructor
    · change 1 / (J : ℝ) = _
      change 1 / (J : ℝ) =
        (Measure.map (fun o : ClampObs J => o.X)
          (minimaxDataMeasure J kappa g)).real {x}
      rw [minimaxDataMeasure_map_X J kappa hJ hkappa g hgmeas hgbound]
      exact (minimaxStratumMeasure_real_singleton J hJ x).symm
    · exact hpmin
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    constructor
    · exact mul_le_mul_of_nonneg_right hcminus (Real.rpow_nonneg ha.1 _)
    · exact mul_le_mul_of_nonneg_right hcplus (Real.rpow_nonneg ha.1 _)
  · refine ⟨fun _ => 1 / 2 + q, fun _ => hcont, ?_⟩
    let μ := minimaxDataMeasure J kappa g
    let design : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
    let m : ClampObs J → ℝ := fun o => 1 / 2 + q o.A
    letI : IsProbabilityMeasure μ := hprob
    have hdesign : Measurable design := measurable_obs_design_cont
    have hY : Integrable (fun o : ClampObs J => o.Y) μ := by
      refine Integrable.of_bound
        (measurable_snd.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))).aestronglyMeasurable 1 ?_
      filter_upwards [minimaxDataMeasure_ae_bernoulli J kappa g hgmeas] with o ho
      rcases ho with ho | ho <;> rw [ho] <;> norm_num
    have hm_meas : Measurable m := by
      dsimp [m]
      exact measurable_const.add (hqmeas.comp
        (measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))))
    have hm : Integrable m μ := by
      refine Integrable.of_bound hm_meas.aestronglyMeasurable 1 ?_
      filter_upwards with o
      rw [Real.norm_eq_abs]
      dsimp [m]
      have hb := hqbound o.A
      rw [abs_le] at hb
      exact abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hm_design :
        AEStronglyMeasurable[MeasurableSpace.comap design inferInstance] m μ := by
      have hfactor : m = (fun p : Fin J × ℝ => 1 / 2 + q p.2) ∘ design := rfl
      rw [hfactor]
      exact ((measurable_const.add (hqmeas.comp measurable_snd)).comp
        (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
    have hintegral : ∀ T : Set (Fin J × ℝ), MeasurableSet T →
        (∫ o in design ⁻¹' T, o.Y ∂μ) = ∫ o in design ⁻¹' T, m o ∂μ := by
      intro T hT
      rw [minimaxDataMeasure_integral_Y_design J kappa hJ hkappa g hgmeas hgbound T hT]
      rw [← integral_indicator (hT.preimage hdesign), ← integral_indicator hT]
      rw [← minimaxDataMeasure_map_design J kappa g hgmeas hgbound,
        integral_map hdesign.aemeasurable]
      · rfl
      · exact ((measurable_const.add hgmeas).indicator hT).aestronglyMeasurable
    exact Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
      μ design hdesign (fun o => o.Y) m hY hm hm_design hintegral

/-- Constant shifts belong to the continuity-only model. The result uses [the `hreg` condition](hyp:hreg), [the `heps` condition](hyp:heps). [This is the stated conclusion](goal).
-/
lemma minimaxConstant_mem_cont_model
    (J : ℕ) (kappa cminus cplus pmin deltaBar eps : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (heps : |eps| ≤ 1 / 2) :
    ContClampModel (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps))
      kappa cminus cplus pmin deltaBar := by
  rcases hreg with ⟨hJ, hkappa, hcminus, hcminus_le, hcplus, hpmin,
    hpmin_le, hdeltaBar, hdeltaBar_one⟩
  apply minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar hJ hkappa
    hcminus_le hcplus hpmin_le (fun _ => eps) measurable_const (fun _ => heps)
  fun_prop

/-- A fixed-height bump with an arbitrarily small positive width belongs to
the same continuity-only class.  In particular, the class membership carries
no width-dependent Hölder radius. The result uses [the `hreg` condition](hyp:hreg), [the `hh` condition](hyp:hh), [the `hamp` condition](hyp:hamp), [the `hamp_le` condition](hyp:hamp_le). [This is the stated conclusion](goal).
-/
lemma minimaxDoseBump_mem_cont_model
    (J : ℕ) (kappa cminus cplus pmin deltaBar delta h amplitude : ℝ)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hh : 0 < h) (hamp : 0 ≤ amplitude) (hamp_le : amplitude ≤ 1 / 4) :
    let q := fun a : ℝ => amplitude *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
    ContClampModel (minimaxClampLaw J kappa (fun p => q p.2))
      kappa cminus cplus pmin deltaBar := by
  dsimp only
  rcases hreg with ⟨hJ, hkappa, hcminus, hcminus_le, hcplus, hpmin,
    hpmin_le, hdeltaBar, hdeltaBar_one⟩
  let q := fun a : ℝ => amplitude *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  apply minimaxClampModel_continuous J kappa cminus cplus pmin deltaBar hJ hkappa
    hcminus_le hcplus hpmin_le q
  · dsimp [q]
    fun_prop
  · intro a
    have hb0 := CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg
      ((a - delta) / h)
    have hb1 := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one
      ((a - delta) / h)
    rw [abs_of_nonneg (mul_nonneg hamp hb0)]
    nlinarith
  · apply Continuous.continuousOn
    dsimp [q]
    have hb : Continuous CausalSmith.Stat.DoseResponseMinimax.doseBump := by
      unfold CausalSmith.Stat.DoseResponseMinimax.doseBump
      exact (CausalSmith.Stat.DoseResponseMinimax.doseContDiffBump.contDiff
        (n := ⊤)).continuous
    exact continuous_const.add (continuous_const.mul
      (hb.comp ((continuous_id.sub continuous_const).div_const h)))

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
