/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxRegression
import Causalean.Mathlib.MeasureTheory.CondExpPreimage

/-! # Model membership of canonical Bernoulli witnesses -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set

noncomputable section

private lemma measurable_obs_design {J : ℕ} :
    Measurable (fun o : ClampObs J => (o.X, o.A)) := by
  let h : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_fst.comp h).prodMk (measurable_fst.comp (measurable_snd.comp h))

private lemma measurable_obs_X {J : ℕ} : Measurable (fun o : ClampObs J => o.X) := by
  exact measurable_fst.comp (Measurable.of_comap_le le_rfl)

/-- [the stated minimax clamp model of taylor property holds](goal) for [the specified `J` input](hyp:J), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hJ` input](hyp:hJ), [the specified `hbeta` input](hyp:hbeta), [the specified `hkappa` input](hyp:hkappa), [the specified `hcminus` input](hyp:hcminus), [the specified `hcplus` input](hyp:hcplus), [the specified `hpmin` input](hyp:hpmin), [the specified `q` input](hyp:q), [the specified `hqmeas` input](hyp:hqmeas), [the specified `hqbound` input](hyp:hqbound), [the specified `hcont` input](hyp:hcont), [the specified `hrange` input](hyp:hrange), [the specified `htaylor` input](hyp:htaylor). -/
lemma minimaxClampModel_of_taylor
    (J : ℕ) (beta kappa L cminus cplus pmin : ℝ)
    (hJ : 0 < J) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hcminus : cminus ≤ kappa + 1) (hcplus : kappa + 1 ≤ cplus)
    (hpmin : pmin ≤ 1 / (J : ℝ))
    (q : ℝ → ℝ) (hqmeas : Measurable q) (hqbound : ∀ a, |q a| ≤ 1 / 2)
    (hcont : ContinuousOn (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) 1))
    (hrange : ∀ a ∈ Set.Icc (0 : ℝ) 1, 1 / 2 + q a ∈ Set.Icc (0 : ℝ) 1)
    (htaylor : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(1 / 2 + q t) - ∑ j ∈ Finset.range (ellOf beta + 1),
          iteratedDerivWithin j (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) 1) s *
            (t - s) ^ j / (Nat.factorial j : ℝ)| ≤ L * |t - s| ^ beta) :
    ClampModel (minimaxClampLaw J kappa (fun p => q p.2))
      beta kappa L cminus cplus pmin := by
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
        rw [hevent, measureReal_def, ← Measure.map_apply measurable_obs_design hrect,
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
  · intro x
    refine ⟨hcont, hrange, ?_, htaylor⟩
    let μ := minimaxDataMeasure J kappa g
    let design : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
    let m : ClampObs J → ℝ := fun o => 1 / 2 + q o.A
    letI : IsProbabilityMeasure μ := hprob
    have hdesign : Measurable design := measurable_obs_design
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
      change |1 / 2 + q o.A| ≤ 1
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
      have hmap := minimaxDataMeasure_map_design J kappa g hgmeas hgbound
      rw [← hmap, integral_map hdesign.aemeasurable]
      · rfl
      · exact ((measurable_const.add hgmeas).indicator hT).aestronglyMeasurable
    exact Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
      μ design hdesign (fun o => o.Y) m hY hm hm_design hintegral

/-- The unperturbed one-half Bernoulli regression is a member of every
admissible clamp model and supplies model-class nonemptiness. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma minimaxCenter_mem_model
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ClampModel (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => 0))
      beta kappa L cminus cplus pmin := by
  rcases hreg with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  apply minimaxClampModel_of_taylor J beta kappa L cminus cplus pmin
    hJ hbeta hkappa hcminus_le hcplus hpmin_le (fun _ => 0)
  · exact measurable_const
  · intro a
    norm_num
  · fun_prop
  · intro a ha
    norm_num
  · intro s hs t ht
    simp_rw [iteratedDerivWithin_const]
    rw [Finset.sum_eq_single 0]
    · simp
      exact mul_nonneg hL.le (Real.rpow_nonneg (abs_nonneg _) _)
    · intro b hb hb0
      simp [hb0]
    · simp

/-- [the stated minimax constant membership model property holds](goal) for [the specified `J` input](hyp:J), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `deltaBar` input](hyp:deltaBar), [the specified `alpha` input](hyp:alpha), [the specified `eps` input](hyp:eps), [the specified `hreg` input](hyp:hreg), [the specified `heps` input](hyp:heps). -/
lemma minimaxConstant_mem_model
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha eps : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (heps : |eps| ≤ 1 / 2) :
    ClampModel (minimaxClampLaw J kappa (fun _ : Fin J × ℝ => eps))
      beta kappa L cminus cplus pmin := by
  rcases hreg with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  apply minimaxClampModel_of_taylor J beta kappa L cminus cplus pmin
    hJ hbeta hkappa hcminus_le hcplus hpmin_le (fun _ => eps)
  · exact measurable_const
  · intro a
    exact heps
  · fun_prop
  · intro a ha
    rw [abs_le] at heps
    constructor <;> linarith
  · intro s hs t ht
    simp_rw [iteratedDerivWithin_const]
    rw [Finset.sum_eq_single 0]
    · simp
      exact mul_nonneg hL.le (Real.rpow_nonneg (abs_nonneg _) _)
    · intro b hb hb0
      simp [hb0]
    · simp

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
