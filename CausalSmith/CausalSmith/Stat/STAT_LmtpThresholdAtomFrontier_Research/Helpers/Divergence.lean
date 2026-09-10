/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Basic
import Causalean.Mathlib.Probability.BernoulliMeasure
import Causalean.Stat.Minimax.Pinsker

/-!
# Two-sided Bernoulli divergence bridges

The upper inequality uses the Causalean quarter-band lemma. The lower inequality
is the missing direction needed by the one-cell calibration and follows from
the exact Bernoulli formula (or Pinsker with the exact two-atom variation).
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- On the quarter window, Bernoulli KL from `1/2+g` to `1/2` is comparable to
`g^2` in both directions. The result uses [the `hg` condition](hyp:hg). [This is the stated conclusion](goal).
-/
lemma bernoulli_kl_band (g : ℝ) (hg : |g| ≤ (1 : ℝ) / 4) :
    2 * g ^ 2 ≤
        (InformationTheory.klDiv
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + g))
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal ∧
      (InformationTheory.klDiv
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + g))
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal
        ≤ 4 * g ^ 2 := by
  have hp_lo : (1 : ℝ) / 4 ≤ 1 / 2 + g := by
    rw [abs_le] at hg
    linarith
  have hp_hi : 1 / 2 + g ≤ (3 : ℝ) / 4 := by
    rw [abs_le] at hg
    linarith
  have hq_lo : (1 : ℝ) / 4 ≤ 1 / 2 := by norm_num
  have hq_hi : (1 / 2 : ℝ) ≤ 3 / 4 := by norm_num
  have hp0 : 0 ≤ 1 / 2 + g := by linarith
  have hp1 : 1 / 2 + g ≤ 1 := by linarith
  let μ := Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + g)
  let ν := Causalean.Mathlib.Probability.bernoulliLaw (1 / 2)
  haveI : IsProbabilityMeasure μ :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      hp0 hp1
  haveI : IsProbabilityMeasure ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by norm_num) (by norm_num)
  have hac : μ ≪ ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
      (by norm_num) (by norm_num)
  have hKLle :=
    Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
      hp_lo hp_hi hq_lo hq_hi
  have hfinite : InformationTheory.klDiv μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKLle
  have hpinsker := Causalean.Stat.pinskerBound_of_ac_of_ne_top μ ν hac hfinite
  have hgap : |g| ≤ Causalean.Stat.tvDist μ ν := by
    have h := Causalean.Stat.abs_measureReal_sub_le_tvDist
      (μ := μ) (ν := ν) (measurableSet_singleton (1 : ℝ))
    have hμ1 : μ.real {(1 : ℝ)} = 1 / 2 + g := by
      norm_num [μ, Causalean.Mathlib.Probability.bernoulliLaw, Measure.real, hp0]
    have hν1 : ν.real {(1 : ℝ)} = 1 / 2 := by
      simp [ν, Causalean.Mathlib.Probability.bernoulliLaw, Measure.real]
    rw [hμ1, hν1] at h
    simpa [abs_sub_comm] using h
  constructor
  · have hsqrt : |g| ≤ Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) :=
      hgap.trans hpinsker
    have hsq := (sq_le_sq₀ (abs_nonneg g)
      (Real.sqrt_nonneg _)).2 hsqrt
    rw [sq_abs, Real.sq_sqrt (by positivity)] at hsq
    dsimp [μ, ν] at hsq ⊢
    linarith
  · have hboundFinite : ENNReal.ofReal (4 * (1 / 2 + g - 1 / 2) ^ 2) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hreal := (ENNReal.toReal_le_toReal hfinite hboundFinite).2 hKLle
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    simpa [μ, ν] using hreal

/-- Integrating the scalar band against a nonnegative design density preserves
both inequalities, yielding the localized one-observation KL order. The result uses [the `hpi_int` condition](hyp:hpi_int), [the `hgamma_meas` condition](hyp:hgamma_meas), [the `hkl_meas` condition](hyp:hkl_meas), [the `hpi` condition](hyp:hpi), [the `hgamma` condition](hyp:hgamma). [This is the stated conclusion](goal).
-/
lemma localized_design_kl_band (pi gamma : ℝ → ℝ)
    (hpi_int : Integrable pi (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hgamma_meas : Measurable gamma)
    (hkl_meas : Measurable fun a =>
      (InformationTheory.klDiv
        (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
        (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal)
    (hpi : ∀ᵐ a ∂volume.restrict (Set.Icc (0 : ℝ) 1), 0 ≤ pi a)
    (hgamma : ∀ a ∈ Set.Icc (0 : ℝ) 1, |gamma a| ≤ (1 : ℝ) / 4) :
    2 * ∫ a in Set.Icc (0 : ℝ) 1, (gamma a) ^ 2 * pi a ≤
        ∫ a in Set.Icc (0 : ℝ) 1,
          (InformationTheory.klDiv
            (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
            (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal * pi a ∧
      (∫ a in Set.Icc (0 : ℝ) 1,
          (InformationTheory.klDiv
            (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
            (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal * pi a) ≤
        4 * ∫ a in Set.Icc (0 : ℝ) 1, (gamma a) ^ 2 * pi a := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hmem : ∀ᵐ a ∂μ, a ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have hsqInt : Integrable (fun a => gamma a ^ 2 * pi a) μ := by
    apply hpi_int.bdd_mul (c := (1 : ℝ) / 16)
    · fun_prop
    · filter_upwards [hmem] with a ha
      have hb := hgamma a ha
      rw [Real.norm_eq_abs, abs_sq]
      have hs := (sq_le_sq₀ (abs_nonneg (gamma a))
        (by norm_num : (0 : ℝ) ≤ 1 / 4)).2 hb
      rw [sq_abs] at hs
      nlinarith
  have hklInt : Integrable (fun a =>
      (InformationTheory.klDiv
        (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
        (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal * pi a) μ := by
    apply hpi_int.bdd_mul (c := (1 : ℝ) / 4)
    · exact hkl_meas.aestronglyMeasurable
    · filter_upwards [hmem] with a ha
      have hb := (bernoulli_kl_band (gamma a) (hgamma a ha)).2
      have hnonneg : 0 ≤ (InformationTheory.klDiv
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal := ENNReal.toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hgam := hgamma a ha
      have hs := (sq_le_sq₀ (abs_nonneg (gamma a))
        (by norm_num : (0 : ℝ) ≤ 1 / 4)).2 hgam
      rw [sq_abs] at hs
      nlinarith
  constructor
  · rw [← integral_const_mul]
    apply integral_mono_ae (hsqInt.const_mul 2) hklInt
    filter_upwards [hpi, hmem] with a hpa ha
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (bernoulli_kl_band (gamma a) (hgamma a ha)).1 hpa
  · rw [← integral_const_mul]
    apply integral_mono_ae hklInt (hsqInt.const_mul 4)
    filter_upwards [hpi, hmem] with a hpa ha
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (bernoulli_kl_band (gamma a) (hgamma a ha)).2 hpa

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
