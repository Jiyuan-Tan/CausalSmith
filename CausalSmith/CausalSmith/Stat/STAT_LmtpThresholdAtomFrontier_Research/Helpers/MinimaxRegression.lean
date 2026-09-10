/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxLaw
import Causalean.Mathlib.MeasureTheory.IntegralBind

/-! # Regression identities for the canonical Bernoulli witnesses -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

private lemma measurable_obs_design {J : ℕ} :
    Measurable (fun o : ClampObs J => (o.X, o.A)) := by
  let h : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_fst.comp h).prodMk (measurable_fst.comp (measurable_snd.comp h))

private lemma measurable_obs_Y {J : ℕ} : Measurable (fun o : ClampObs J => o.Y) := by
  exact measurable_snd.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

private lemma measurable_obs_mk {J : ℕ} (p : Fin J × ℝ) :
    Measurable (fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2)) := by
  rw [measurable_comap_iff]
  fun_prop

private lemma integrable_of_measurable_ae_bound {A : Type*} [MeasurableSpace A]
    {mu : Measure A} [IsFiniteMeasure mu] {f : A → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ᵐ x ∂mu, |f x| ≤ C) : Integrable f mu := by
  refine Integrable.of_bound hf.aestronglyMeasurable (max C 0) ?_
  filter_upwards [hC] with x hx
  simpa [Real.norm_eq_abs] using hx.trans (le_max_left C 0)

/-- Integrating the outcome over a design event integrates the advertised
Bernoulli mean over the common design law. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hgmeas` condition](hyp:hgmeas), [the `hg` condition](hyp:hg), [the `hT` condition](hyp:hT). [This is the stated conclusion](goal).
-/
lemma minimaxDataMeasure_integral_Y_design
    (J : ℕ) (kappa : ℝ) (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (g : Fin J × ℝ → ℝ) (hgmeas : Measurable g)
    (hg : ∀ p, |g p| ≤ 1 / 2) (T : Set (Fin J × ℝ)) (hT : MeasurableSet T) :
    (∫ o in (fun o : ClampObs J => (o.X, o.A)) ⁻¹' T, o.Y
      ∂minimaxDataMeasure J kappa g) =
      ∫ p in T, (1 / 2 + g p) ∂minimaxDesignMeasure J kappa := by
  classical
  let P := minimaxDataMeasure J kappa g
  let D := minimaxDesignMeasure J kappa
  let E : Set (ClampObs J) := (fun o => (o.X, o.A)) ⁻¹' T
  let F : ClampObs J → ℝ := E.indicator (fun o => o.Y)
  haveI : IsProbabilityMeasure P :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa g hgmeas hg
  have hFmeas : Measurable F :=
    measurable_obs_Y.indicator (hT.preimage measurable_obs_design)
  have hFint : Integrable F P := by
    refine integrable_of_measurable_ae_bound hFmeas 1 ?_
    filter_upwards [minimaxDataMeasure_ae_bernoulli J kappa g hgmeas] with o ho
    rcases ho with ho | ho <;>
      by_cases hmem : o ∈ E <;> simp [F, Set.indicator, hmem, ho]
  have hbind := Causalean.Mathlib.MeasureTheory.integral_bind_map
    (m := D)
    (κ := fun p => Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p))
    (g := fun p y => ClampObs.mk p.1 p.2 (y + 1 / 2))
    (f := F) (fun p => measurable_obs_mk p)
    (measurable_minimaxOutcomeKernel g hgmeas) (by
      change Integrable F (minimaxDataMeasure J kappa g)
      exact hFint)
  have hfiber (p : Fin J × ℝ) :
      (∫ y, F (ClampObs.mk p.1 p.2 (y + 1 / 2))
        ∂Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p)) =
        T.indicator (fun p => 1 / 2 + g p) p := by
    by_cases hp : p ∈ T
    · rw [Set.indicator_of_mem hp]
      have hFE : ∀ y : ℝ,
          F (ClampObs.mk p.1 p.2 (y + 1 / 2)) = y + 1 / 2 := by
        intro y
        simp [F, E, Set.indicator, hp]
      simp_rw [hFE]
      rw [Causalean.Mathlib.Probability.twoPointMean_integral (by norm_num) (hg p)]
      ring
    · simp only [Set.indicator, hp, if_false]
      have hzero : ∀ y : ℝ, F (ClampObs.mk p.1 p.2 (y + 1 / 2)) = 0 := by
        intro y
        simp [F, E, Set.indicator, hp]
      simp_rw [hzero]
      simp
  rw [show (∫ o in E, o.Y ∂P) = ∫ o, F o ∂P by
    rw [integral_indicator (hT.preimage measurable_obs_design)]]
  change (∫ o, F o ∂P) = _
  rw [show (∫ o, F o ∂P) =
      ∫ p, ∫ y, F (ClampObs.mk p.1 p.2 (y + 1 / 2))
        ∂Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p) ∂D by
    change (∫ o, F o ∂(minimaxDesignMeasure J kappa).bind
      (fun p => (Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p)).map
        (fun y => ClampObs.mk p.1 p.2 (y + 1 / 2)))) = _
    exact hbind]
  rw [← integral_indicator hT]
  apply integral_congr_ae
  filter_upwards with p
  rw [hfiber]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
