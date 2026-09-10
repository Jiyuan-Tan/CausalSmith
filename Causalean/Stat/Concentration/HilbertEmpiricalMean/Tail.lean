/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.HilbertEmpiricalMean.Basic
import Causalean.Mathlib.Probability.ConvergingTogether.CharFunBound
import Causalean.Stat.Concentration.TailBounds.McDiarmid

/-!
# Dimension-free Hilbert empirical-mean concentration

This module turns the Hilbert empirical-mean second-moment identity into an
expected-norm bound and a scalar McDiarmid tail bound.  A unit-norm feature map
therefore has centered empirical mean within the standard dimension-free
radius with high probability in every complete real Hilbert space.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace Causalean.Stat.Concentration.HilbertEmpiricalMean

variable {Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- Under [a probability law](hyp:μ), [a strongly measurable Hilbert-valued
random variable](hyp:g,hg) with [integrable squared norm](hyp:hg_sq) has
[expected norm at most the square root of its expected squared norm](goal). -/
theorem integral_norm_le_sqrt_integral_norm_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → H)
    (hg : StronglyMeasurable g)
    (hg_sq : Integrable (fun ω => ‖g ω‖ ^ 2) μ) :
    ∫ ω, ‖g ω‖ ∂μ ≤ Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  have hg_L2 : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg_sq
  exact
    Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
      μ g hg_L2

/-- For [a probability law](hyp:P), [a strongly measurable Hilbert-valued
feature map](hyp:f,hf) with [unit-norm bound at every observation](hyp:hbound),
and [a nonempty sample size](hyp:hm), [the expected norm of the centered
empirical mean is at most one divided by the square root of the sample size](goal). -/
theorem centeredEmpiricalMean_norm_integral_le_inv_sqrt
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ z : Fin m → X, ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖
        ∂(Measure.pi (fun _ : Fin m => P)) ≤
      1 / Real.sqrt m := by
  let Q : Measure (Fin m → X) := Measure.pi (fun _ : Fin m => P)
  have hf_L2 : MemLp f 2 P := memLp_two_of_norm_le_one P f hf hbound
  have hcoord_L2 (i : Fin m) :
      MemLp (fun z : Fin m → X => f (z i)) 2 Q := by
    change MemLp (f ∘ (Function.eval i : (Fin m → X) → X)) 2 Q
    exact hf_L2.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => P) i)
  have hsum_L2 :
      MemLp (fun z : Fin m → X => ∑ r, f (z r)) 2 Q := by
    simpa only [Finset.sum_apply] using
      memLp_finsetSum Finset.univ (fun i _ => hcoord_L2 i)
  have hmean_L2 : MemLp (centeredEmpiricalMean P f m) 2 Q := by
    unfold centeredEmpiricalMean empiricalMean populationMean
    exact (hsum_L2.const_smul (m : ℝ)⁻¹).sub (memLp_const _)
  have hsum_sm :
      StronglyMeasurable (fun z : Fin m → X => ∑ r, f (z r)) := by
    rw [← Finset.sum_fn]
    apply Finset.stronglyMeasurable_sum
    intro i _
    exact hf.comp_measurable (measurable_pi_apply i)
  have hmean_sm : StronglyMeasurable (centeredEmpiricalMean P f m) := by
    unfold centeredEmpiricalMean empiricalMean populationMean
    exact (hsum_sm.const_smul (m : ℝ)⁻¹).sub stronglyMeasurable_const
  have hmean_sq :
      Integrable (fun z => ‖centeredEmpiricalMean P f m z‖ ^ 2) Q :=
    (memLp_two_iff_integrable_sq_norm hmean_sm.aestronglyMeasurable).1 hmean_L2
  have hraw_sq :
      Integrable (fun x => ‖f x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf_L2
  have hraw : (∫ x, ‖f x‖ ^ 2 ∂P) ≤ 1 := by
    calc
      (∫ x, ‖f x‖ ^ 2 ∂P) ≤ ∫ _x : X, (1 : ℝ) ∂P := by
        apply integral_mono hraw_sq (integrable_const _)
        intro x
        nlinarith [norm_nonneg (f x), hbound x]
      _ = 1 := by simp
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hsecond :
      (∫ z, ‖centeredEmpiricalMean P f m z‖ ^ 2 ∂Q) ≤ (m : ℝ)⁻¹ := by
    calc
      (∫ z, ‖centeredEmpiricalMean P f m z‖ ^ 2 ∂Q)
          ≤ (m : ℝ)⁻¹ * ∫ x, ‖f x‖ ^ 2 ∂P := by
            simpa only [Q] using
              centeredEmpiricalMean_secondMoment_le P f hf hf_L2 hm_pos
      _ ≤ (m : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = (m : ℝ)⁻¹ := mul_one _
  calc
    (∫ z : Fin m → X, ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖
        ∂(Measure.pi (fun _ : Fin m => P)))
        ≤ Real.sqrt (∫ z, ‖centeredEmpiricalMean P f m z‖ ^ 2 ∂Q) := by
          simpa only [Q, centeredEmpiricalMean, empiricalMean, populationMean] using
            integral_norm_le_sqrt_integral_norm_sq Q
              (centeredEmpiricalMean P f m) hmean_sm hmean_sq
    _ ≤ Real.sqrt ((m : ℝ)⁻¹) := Real.sqrt_le_sqrt hsecond
    _ = 1 / Real.sqrt m := by rw [Real.sqrt_inv]; simp

/-- For [a probability law](hyp:P), [a strongly measurable Hilbert-valued
feature map](hyp:f,hf) with [unit-norm bound at every observation](hyp:hbound),
[a nonempty sample size](hyp:hm), and [a confidence level strictly between zero
and one](hyp:δ,hδ,hδ_one), [the probability that the centered empirical mean
exceeds the standard dimension-free radius is at most the confidence level](goal). -/
theorem centeredEmpiricalMean_norm_tail_le
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ < 1) :
    ((Measure.pi (fun _ : Fin m => P))
      {z | 1 / Real.sqrt m +
          Real.sqrt (2 * Real.log (1 / δ) / m) <
        ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖}).toReal ≤ δ := by
  let _ : Nonempty X := nonempty_of_isProbabilityMeasure P
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm_pos
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (one_lt_one_div hδ hδ_one)
  have hrad : 0 ≤ 2 * Real.log (1 / δ) / (m : ℝ) := by positivity
  have hsum :
      (∑ _i : Fin m, (2 / (m : ℝ)) ^ 2) = 4 / (m : ℝ) := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have ht :
      (m : ℝ) / 4 * ∑ _i : Fin m, (2 / (m : ℝ)) ^ 2 ≤ 1 := by
    rw [hsum]
    field_simp
    norm_num
  have hmc := mcdiarmid_inequality_pos'
    (μ := P) (ι := Fin m) (X' := id) measurable_id
    (f' := centeredEmpiricalMeanNorm P f m)
    (c' := fun _ : Fin m => 2 / (m : ℝ))
    (fun i z x' =>
      centeredEmpiricalMeanNorm_boundedDifference P f hbound hm_pos i z x')
    (measurable_centeredEmpiricalMeanNorm P f hf m)
    (ε := Real.sqrt (2 * Real.log (1 / δ) / (m : ℝ)))
    (Real.sqrt_nonneg _)
    (t := (m : ℝ) / 4) ht
  simp only at hmc
  have hInt :
      ∫ z : Fin m → X, centeredEmpiricalMeanNorm P f m z
          ∂(Measure.pi (fun _ : Fin m => P)) ≤ 1 / Real.sqrt m := by
    simpa only [centeredEmpiricalMeanNorm, centeredEmpiricalMean,
      empiricalMean, populationMean] using
      centeredEmpiricalMean_norm_integral_le_inv_sqrt P f hf hbound hm
  calc
    ((Measure.pi (fun _ : Fin m => P))
      {z | 1 / Real.sqrt m +
          Real.sqrt (2 * Real.log (1 / δ) / m) <
        ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖}).toReal
        ≤ ((Measure.pi (fun _ : Fin m => P))
          {z | centeredEmpiricalMeanNorm P f m z -
              ∫ x, centeredEmpiricalMeanNorm P f m x
                ∂(Measure.pi (fun _ : Fin m => P)) ≥
              Real.sqrt (2 * Real.log (1 / δ) / (m : ℝ))}).toReal := by
            apply ENNReal.toReal_mono (measure_ne_top _ _)
            apply measure_mono
            intro z hz
            change Real.sqrt (2 * Real.log (1 / δ) / (m : ℝ)) ≤
              centeredEmpiricalMeanNorm P f m z -
                ∫ x, centeredEmpiricalMeanNorm P f m x
                  ∂(Measure.pi (fun _ : Fin m => P))
            change 1 / Real.sqrt (m : ℝ) +
                Real.sqrt (2 * Real.log (1 / δ) / (m : ℝ)) <
              centeredEmpiricalMeanNorm P f m z at hz
            linarith
    _ ≤ Real.exp
        (-2 * (Real.sqrt (2 * Real.log (1 / δ) / (m : ℝ))) ^ 2 *
          ((m : ℝ) / 4)) := hmc
    _ = δ := by
      rw [Real.sq_sqrt hrad]
      have harg :
          -2 * (2 * Real.log (1 / δ) / (m : ℝ)) * ((m : ℝ) / 4) =
            Real.log δ := by
        rw [show Real.log (1 / δ) = -Real.log δ by
          simp only [one_div, Real.log_inv]]
        field_simp
        ring
      rw [harg, Real.exp_log hδ]

/-- For [a probability law](hyp:P), [a strongly measurable Hilbert-valued
feature map](hyp:f,hf) with [unit-norm bound at every observation](hyp:hbound),
[a nonempty sample size](hyp:hm), and [a confidence level strictly between zero
and one](hyp:δ,hδ,hδ_one), [the centered empirical mean lies within the standard
dimension-free radius with probability at least one minus the confidence level](goal). -/
theorem centeredEmpiricalMean_norm_highProbability
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ < 1) :
    1 - ENNReal.ofReal δ ≤
      (Measure.pi (fun _ : Fin m => P))
        {z | ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖ ≤
          1 / Real.sqrt m + Real.sqrt (2 * Real.log (1 / δ) / m)} := by
  let Q : Measure (Fin m → X) := Measure.pi (fun _ : Fin m => P)
  let bad : Set (Fin m → X) :=
    {z | 1 / Real.sqrt m + Real.sqrt (2 * Real.log (1 / δ) / m) <
      ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖}
  have hbad_meas : MeasurableSet bad := by
    dsimp only [bad]
    simpa only [centeredEmpiricalMeanNorm, centeredEmpiricalMean,
      empiricalMean, populationMean] using
      measurableSet_lt measurable_const
        (measurable_centeredEmpiricalMeanNorm P f hf m)
  have htail : (Q bad).toReal ≤ δ := by
    simpa only [Q, bad] using
      centeredEmpiricalMean_norm_tail_le P f hf hbound hm hδ hδ_one
  have hbad_ne : Q bad ≠ ⊤ := measure_ne_top Q bad
  have hbad : Q bad ≤ ENNReal.ofReal δ := by
    calc
      Q bad = ENNReal.ofReal (Q bad).toReal :=
        (ENNReal.ofReal_toReal hbad_ne).symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal htail
  have hcompl :
      {z | ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖ ≤
          1 / Real.sqrt m + Real.sqrt (2 * Real.log (1 / δ) / m)} =
        badᶜ := by
    ext z
    simp only [bad, Set.mem_ofPred_eq, mem_compl_iff, not_lt]
  rw [show Measure.pi (fun _ : Fin m => P) = Q by rfl, hcompl,
    prob_compl_eq_one_sub hbad_meas]
  exact tsub_le_tsub_left hbad 1

end Causalean.Stat.Concentration.HilbertEmpiricalMean
