/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Mathlib.Probability.SignedTwoPoint

/-!
# Explicit chi-squared divergence for centered two-point laws

This module evaluates chi-squared divergence for the Bernoulli perturbation around
one half and for its equivalent signed two-point representation.
-/

namespace Causalean.Stat

open MeasureTheory
open Causalean.Mathlib.Probability

/-- For [a perturbation whose magnitude is strictly below one half](hyp:hu), [the
χ²-divergence of the Bernoulli law with success probability one half plus that perturbation,
relative to the centered Bernoulli law, is four times the squared perturbation](goal). -/
theorem chiSqDiv_bernoulliLaw_centerHalf {u : Real} (hu : abs u < 1 / 2) :
    Causalean.Stat.chiSqDiv (bernoulliLaw (1 / 2 + u)) (bernoulliLaw (1 / 2)) =
      4 * u ^ 2 := by
  classical
  let p : ℝ := 1 / 2 + u
  let q : ℝ := 1 / 2
  have hub := abs_lt.mp hu
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  haveI : IsProbabilityMeasure (bernoulliLaw q) :=
    bernoulliLaw_isProbabilityMeasure hq0.le hq1.le
  let g : ℝ → ENNReal := fun x =>
    if x = 1 then ENNReal.ofReal (p / q)
    else ENNReal.ofReal ((1 - p) / (1 - q))
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have hwd : bernoulliLaw p = (bernoulliLaw q).withDensity g := by
    ext s hs
    rw [withDensity_apply _ hs, ← lintegral_indicator hs g]
    unfold bernoulliLaw
    dsimp [g]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp only [lintegral_dirac]
    by_cases h1 : (1 : ℝ) ∈ s
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top,
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top]
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0]
  have hrn : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw q] g := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity _ hg
  change Causalean.Stat.chiSqDiv (bernoulliLaw p) (bernoulliLaw q) = 4 * u ^ 2
  rw [Causalean.Stat.chiSqDiv]
  trans ∫ x, ((g x).toReal - 1) ^ 2 ∂(bernoulliLaw q)
  · exact integral_congr_ae <| hrn.mono fun x hx => by
      dsimp
      rw [hx]
  rw [bernoulliLaw_integral hq0.le hq1.le]
  dsimp [g]
  have hpq_nonneg : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have hcp_nonneg : 0 ≤ (1 - p) / (1 - q) :=
    div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le)
  simp only [if_pos, if_neg zero_ne_one]
  rw [ENNReal.toReal_ofReal hpq_nonneg, ENNReal.toReal_ofReal hcp_nonneg]
  dsimp [p, q]
  ring

/-- For [a mean perturbation whose magnitude is strictly below one half](hyp:hu), [the
χ²-divergence of the symmetric two-point law with that mean, relative to the centered
symmetric two-point law, is four times the squared perturbation](goal). -/
theorem chiSqDiv_twoPointMean_centerHalf {u : Real} (hu : abs u < 1 / 2) :
    Causalean.Stat.chiSqDiv (twoPointMean (1 / 2) u) (twoPointMean (1 / 2) 0) =
      4 * u ^ 2 := by
  let e : ℝ ≃ᵐ ℝ :=
    (affineHomeomorph (2 * (1 / 2 : ℝ)) (-(1 / 2 : ℝ)) (by norm_num)).toMeasurableEquiv
  have hub := abs_lt.mp hu
  haveI : IsProbabilityMeasure (bernoulliLaw (1 / 2 + u)) :=
    bernoulliLaw_isProbabilityMeasure (by linarith [hub.1]) (by linarith [hub.2])
  haveI : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_isProbabilityMeasure (by norm_num) (by norm_num)
  rw [twoPointMean_eq_map_bernoulli (1 / 2) u (by norm_num),
    twoPointMean_eq_map_bernoulli (1 / 2) 0 (by norm_num)]
  have hp : (1 + u / (1 / 2)) / 2 = (1 / 2 + u : ℝ) := by ring
  have hq : (1 + 0 / (1 / 2)) / 2 = (1 / 2 : ℝ) := by ring
  rw [hp, hq]
  change Causalean.Stat.chiSqDiv
      (Measure.map e (bernoulliLaw (1 / 2 + u)))
      (Measure.map e (bernoulliLaw (1 / 2))) = 4 * u ^ 2
  rw [chiSqDiv_map_measurableEquiv]
  exact chiSqDiv_bernoulliLaw_centerHalf hu

end Causalean.Stat
