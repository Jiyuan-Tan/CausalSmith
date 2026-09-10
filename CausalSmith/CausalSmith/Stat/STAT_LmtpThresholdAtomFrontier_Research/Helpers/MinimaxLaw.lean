/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxWitness
import Causalean.Mathlib.Probability.SignedTwoPoint
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Bernoulli laws over the canonical minimax design

The centered two-point law on `{-1/2,1/2}` is translated to a genuine
Bernoulli outcome on `{0,1}`.  Keeping this construction as an iterated kernel
makes the common design marginal and regression identities transparent.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

private lemma measurable_clampObs_mk {J : ℕ} (p : Fin J × ℝ) :
    Measurable (fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) := by
  rw [measurable_comap_iff]
  fun_prop

private lemma measurable_clampObs_mk_pair {J : ℕ} :
    Measurable (fun p : (Fin J × ℝ) × ℝ =>
      ClampObs.mk p.1.1 p.1.2 (p.2 + 1 / 2)) := by
  rw [measurable_comap_iff]
  fun_prop

/-- The Bernoulli observation kernel with centered conditional mean `g`. -/
def minimaxOutcomeKernel {J : ℕ} (g : Fin J × ℝ → ℝ)
    (p : Fin J × ℝ) : Measure (ClampObs J) :=
  (Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p)).map
    (fun y => ClampObs.mk p.1 p.2 (y + 1 / 2))

/-- [the stated measurable minimax outcome kernel property holds](goal) for [the specified `J` input](hyp:J), [the specified `g` input](hyp:g), [the specified `hg` input](hyp:hg). -/
lemma measurable_minimaxOutcomeKernel {J : ℕ} (g : Fin J × ℝ → ℝ)
    (hg : Measurable g) : Measurable (minimaxOutcomeKernel g) := by
  classical
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  unfold minimaxOutcomeKernel Causalean.Mathlib.Probability.twoPointMean
  simp_rw [Measure.map_apply (measurable_clampObs_mk _) hS]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  have hplus : Measurable (fun p : Fin J × ℝ =>
      ((fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) ⁻¹' S).indicator
        (1 : ℝ → ℝ≥0∞) (1 / 2)) := by
    rw [show (fun p : Fin J × ℝ =>
        ((fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) ⁻¹' S).indicator
          (1 : ℝ → ℝ≥0∞) (1 / 2)) =
        fun p => if ClampObs.mk p.1 p.2 1 ∈ S then 1 else 0 by
      funext p
      simp [Set.indicator_apply]
      norm_num]
    exact Measurable.ite (hS.preimage (by rw [measurable_comap_iff]; fun_prop))
      measurable_const measurable_const
  have hminus : Measurable (fun p : Fin J × ℝ =>
      ((fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) ⁻¹' S).indicator
        (1 : ℝ → ℝ≥0∞) (-1 / 2)) := by
    rw [show (fun p : Fin J × ℝ =>
        ((fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) ⁻¹' S).indicator
          (1 : ℝ → ℝ≥0∞) (-1 / 2)) =
        fun p => if ClampObs.mk p.1 p.2 0 ∈ S then 1 else 0 by
      funext p
      simp [Set.indicator_apply]
      norm_num]
    exact Measurable.ite (hS.preimage (by rw [measurable_comap_iff]; fun_prop))
      measurable_const measurable_const
  exact ((ENNReal.measurable_ofReal.comp
      (measurable_const.add (hg.div_const _) |>.div_const _)).mul hplus).add
    ((ENNReal.measurable_ofReal.comp
      (measurable_const.sub (hg.div_const _) |>.div_const _)).mul (by
        simpa only [neg_div] using hminus))

/-- Joint observation law induced by the canonical design and centered mean `g`. -/
def minimaxDataMeasure (J : ℕ) (kappa : ℝ) (g : Fin J × ℝ → ℝ) :
    Measure (ClampObs J) :=
  (minimaxDesignMeasure J kappa).bind (minimaxOutcomeKernel g)

/-- Canonical law package associated with a centered Bernoulli regression. -/
def minimaxClampLaw (J : ℕ) (kappa : ℝ) (g : Fin J × ℝ → ℝ) :
    ClampLaw J where
  dataMeasure := minimaxDataMeasure J kappa g
  px := fun _ => 1 / (J : ℝ)
  pi := fun _ a => (kappa + 1) * a ^ kappa
  mu := fun x a => 1 / 2 + g (x, a)

/-- [minimax outcome kernel is a probability measure](goal) for [the specified `J` input](hyp:J), [the specified `g` input](hyp:g), [the specified `hg` input](hyp:hg), [the specified `p` input](hyp:p). -/
lemma minimaxOutcomeKernel_isProbabilityMeasure {J : ℕ}
    {g : Fin J × ℝ → ℝ} (hg : ∀ p, |g p| ≤ 1 / 2) (p : Fin J × ℝ) :
    IsProbabilityMeasure (minimaxOutcomeKernel g p) := by
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p)) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure (by norm_num) (hg p)
  exact Measure.isProbabilityMeasure_map (measurable_clampObs_mk p).aemeasurable

/-- [minimax data measure is a probability measure](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `g` input](hyp:g), [the specified `hgmeas` input](hyp:hgmeas), [the specified `hg` input](hyp:hg). -/
lemma minimaxDataMeasure_isProbabilityMeasure (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (g : Fin J × ℝ → ℝ)
    (hgmeas : Measurable g) (hg : ∀ p, |g p| ≤ 1 / 2) :
    IsProbabilityMeasure (minimaxDataMeasure J kappa g) := by
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  exact isProbabilityMeasure_bind (measurable_minimaxOutcomeKernel g hgmeas).aemeasurable
    (Filter.Eventually.of_forall (minimaxOutcomeKernel_isProbabilityMeasure hg))

private lemma measurable_clampObs_design {J : ℕ} :
    Measurable (fun o : ClampObs J => (o.X, o.A)) := by
  let h : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_fst.comp h).prodMk (measurable_fst.comp (measurable_snd.comp h))

private lemma measurable_clampObs_Y {J : ℕ} :
    Measurable (fun o : ClampObs J => o.Y) := by
  exact measurable_snd.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

/-- [the stated minimax outcome kernel map design property holds](goal) for [the specified `J` input](hyp:J), [the specified `g` input](hyp:g), [the specified `hg` input](hyp:hg), [the specified `p` input](hyp:p). -/
lemma minimaxOutcomeKernel_map_design {J : ℕ}
    {g : Fin J × ℝ → ℝ} (hg : ∀ p, |g p| ≤ 1 / 2) (p : Fin J × ℝ) :
    (minimaxOutcomeKernel g p).map (fun o => (o.X, o.A)) = Measure.dirac p := by
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p)) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure (by norm_num) (hg p)
  unfold minimaxOutcomeKernel
  rw [Measure.map_map measurable_clampObs_design (measurable_clampObs_mk p)]
  have hcomp : ((fun o : ClampObs J => (o.X, o.A)) ∘
      fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) = fun _ : ℝ => p := by
    funext y
    rfl
  rw [hcomp]
  rw [Measure.map_const _ p, measure_univ, one_smul]

/-- [the stated minimax data measure map design property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `g` input](hyp:g), [the specified `hgmeas` input](hyp:hgmeas), [the specified `hg` input](hyp:hg). -/
lemma minimaxDataMeasure_map_design (J : ℕ) (kappa : ℝ)
    (g : Fin J × ℝ → ℝ) (hgmeas : Measurable g)
    (hg : ∀ p, |g p| ≤ 1 / 2) :
    (minimaxDataMeasure J kappa g).map (fun o => (o.X, o.A)) =
      minimaxDesignMeasure J kappa := by
  ext S hS
  rw [Measure.map_apply measurable_clampObs_design hS]
  unfold minimaxDataMeasure
  rw [Measure.bind_apply (hS.preimage measurable_clampObs_design)
    (measurable_minimaxOutcomeKernel g hgmeas).aemeasurable]
  have hfiber (p : Fin J × ℝ) :
      (minimaxOutcomeKernel g p) ((fun o : ClampObs J => (o.X, o.A)) ⁻¹' S) =
        S.indicator (fun _ => (1 : ℝ≥0∞)) p := by
    rw [← Measure.map_apply measurable_clampObs_design hS,
      minimaxOutcomeKernel_map_design hg p]
    by_cases hp : p ∈ S <;> simp [Measure.dirac_apply, Set.indicator, hp]
  simp_rw [hfiber]
  rw [lintegral_indicator hS]
  simp [Pi.one_apply]

/-- [the stated minimax data measure map x property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `g` input](hyp:g), [the specified `hgmeas` input](hyp:hgmeas), [the specified `hg` input](hyp:hg). -/
lemma minimaxDataMeasure_map_X (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (g : Fin J × ℝ → ℝ) (hgmeas : Measurable g)
    (hg : ∀ p, |g p| ≤ 1 / 2) :
    (minimaxDataMeasure J kappa g).map (fun o => o.X) = minimaxStratumMeasure J := by
  letI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  calc
    (minimaxDataMeasure J kappa g).map (fun o => o.X) =
        ((minimaxDataMeasure J kappa g).map (fun o => (o.X, o.A))).map Prod.fst := by
          rw [Measure.map_map measurable_fst measurable_clampObs_design]
          rfl
    _ = (minimaxDesignMeasure J kappa).map Prod.fst := by
      rw [minimaxDataMeasure_map_design J kappa g hgmeas hg]
    _ = minimaxStratumMeasure J := by
      rw [minimaxDesignMeasure, Measure.map_fst_prod, measure_univ, one_smul]

/-- [minimax treatment measure almost everywhere lies in the stated closed interval](goal) for [the specified `kappa` input](hyp:kappa). -/
lemma minimaxTreatmentMeasure_ae_mem_Icc (kappa : ℝ) :
    ∀ᵐ a ∂minimaxTreatmentMeasure kappa, a ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  unfold minimaxTreatmentMeasure
  change ((volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun a => ENNReal.ofReal ((kappa + 1) * a ^ kappa)))
      (Set.Icc (0 : ℝ) 1)ᶜ = 0
  rw [withDensity_apply _ measurableSet_Icc.compl]
  apply setLIntegral_measure_zero
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  simp

/-- [the stated minimax data measure almost everywhere treatment property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `g` input](hyp:g), [the specified `hgmeas` input](hyp:hgmeas), [the specified `hg` input](hyp:hg). -/
lemma minimaxDataMeasure_ae_treatment (J : ℕ) (kappa : ℝ)
    (g : Fin J × ℝ → ℝ) (hgmeas : Measurable g)
    (hg : ∀ p, |g p| ≤ 1 / 2) :
    ∀ᵐ o ∂minimaxDataMeasure J kappa g, o.A ∈ Set.Icc (0 : ℝ) 1 := by
  letI : SFinite (minimaxTreatmentMeasure kappa) := by
    unfold minimaxTreatmentMeasure
    infer_instance
  have hs : MeasurableSet {p : Fin J × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1} :=
    measurableSet_Icc.preimage measurable_snd
  rw [← ae_map_iff measurable_clampObs_design.aemeasurable hs,
    minimaxDataMeasure_map_design J kappa g hgmeas hg]
  rw [ae_iff]
  have hset : {p : Fin J × ℝ | ¬p.2 ∈ Set.Icc (0 : ℝ) 1} =
      (Set.univ : Set (Fin J)) ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ := by ext p; simp
  rw [hset, minimaxDesignMeasure, Measure.prod_prod]
  rw [show minimaxTreatmentMeasure kappa (Set.Icc (0 : ℝ) 1)ᶜ = 0 by
    exact ae_iff.mp (minimaxTreatmentMeasure_ae_mem_Icc kappa)]
  simp

/-- [the stated minimax outcome kernel almost everywhere support property holds](goal) for [the specified `J` input](hyp:J), [the specified `g` input](hyp:g), [the specified `p` input](hyp:p). -/
lemma minimaxOutcomeKernel_ae_support {J : ℕ}
    (g : Fin J × ℝ → ℝ) (p : Fin J × ℝ) :
    ∀ᵐ o ∂minimaxOutcomeKernel g p,
      o.X = p.1 ∧ o.A = p.2 ∧ (o.Y = 0 ∨ o.Y = 1) := by
  unfold minimaxOutcomeKernel
  have hs : MeasurableSet {o : ClampObs J |
      o.X = p.1 ∧ o.A = p.2 ∧ (o.Y = 0 ∨ o.Y = 1)} := by
    have hd : MeasurableSet {o : ClampObs J | (o.X, o.A) = p} :=
      (measurableSet_singleton p).preimage measurable_clampObs_design
    have hy : MeasurableSet {o : ClampObs J | o.Y = 0 ∨ o.Y = 1} :=
      ((measurableSet_singleton (0 : ℝ)).preimage measurable_clampObs_Y).union
        ((measurableSet_singleton (1 : ℝ)).preimage measurable_clampObs_Y)
    convert hd.inter hy using 1 <;> ext o <;> simp [Prod.ext_iff, and_assoc]
  rw [ae_map_iff (measurable_clampObs_mk p).aemeasurable hs]
  rw [ae_iff]
  unfold Causalean.Mathlib.Probability.twoPointMean
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp
  norm_num

/-- [the stated minimax data measure almost everywhere bernoulli property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `g` input](hyp:g), [the specified `hgmeas` input](hyp:hgmeas). -/
lemma minimaxDataMeasure_ae_bernoulli (J : ℕ) (kappa : ℝ)
    (g : Fin J × ℝ → ℝ) (hgmeas : Measurable g) :
    ∀ᵐ o ∂minimaxDataMeasure J kappa g, o.Y = 0 ∨ o.Y = 1 := by
  rw [ae_iff]
  unfold minimaxDataMeasure
  have hbad : MeasurableSet {o : ClampObs J | ¬(o.Y = 0 ∨ o.Y = 1)} := by
    exact (((measurableSet_singleton (0 : ℝ)).preimage measurable_clampObs_Y).union
      ((measurableSet_singleton (1 : ℝ)).preimage measurable_clampObs_Y)).compl
  rw [Measure.bind_apply hbad (measurable_minimaxOutcomeKernel g hgmeas).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [] with p
  exact ae_iff.mp ((minimaxOutcomeKernel_ae_support g p).mono (fun o ho => ho.2.2))


end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
