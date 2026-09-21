/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.IidMeanVariance
public import Causalean.Stat.Concentration.Chebyshev

/-!
# Empirical weight second moments and Kish effective sample size

This module distinguishes the sample average of squared weights from the scale-invariant Kish
design effect and effective sample size. It proves agreement under realized mean-one
normalization, then gives mean, variance, and product-law lower-tail results for the empirical
weight second moment.
-/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Given [a real-valued weight function](hyp:g), [a sample size](hyp:n), and
[an indexed sample](hyp:sample), [the empirical weight second moment](goal) is the sample average
of the squared weights. -/
def empiricalWeightSecondMoment {Ω : Type*} (g : Ω → ℝ) (n : ℕ)
    (sample : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, g (sample i) ^ 2

/-- Given [a real-valued weight function](hyp:g), [a sample size](hyp:n), and
[an indexed sample](hyp:sample), [this legacy compatibility name](goal) denotes the empirical
weight second moment, not a scale-invariant finite-sample Kish design effect. -/
abbrev empiricalKishDispersion {Ω : Type*} (g : Ω → ℝ) (n : ℕ)
    (sample : Fin n → Ω) : ℝ :=
  empiricalWeightSecondMoment g n sample

/-- Given [a finite vector of realized weights](hyp:w), [the Kish design effect](goal) is zero
when their sum is zero, and otherwise uses the normalized formula.
-/
def kishDesignEffect {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  if ∑ i, w i = 0 then 0
  else ((n : ℝ) * ∑ i, w i ^ 2) / (∑ i, w i) ^ 2

/-- Given [a finite vector of realized weights](hyp:w), [the Kish effective sample size](goal) is
zero when their squared-weight sum is zero, and otherwise uses squared total weight divided by
the squared-weight sum. -/
def kishEffectiveSampleSize {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  if ∑ i, w i ^ 2 = 0 then 0
  else (∑ i, w i) ^ 2 / ∑ i, w i ^ 2

/-- Given [realized weights](hyp:w), [a positive sample size](hyp:hn), and
[realized mean-one normalization](hyp:hsum), [the two quantities agree](goal). -/
lemma kishDesignEffect_eq_empiricalWeightSecondMoment_of_sum_eq
    {n : ℕ} (w : Fin n → ℝ) (hn : 0 < n)
    (hsum : ∑ i, w i = (n : ℝ)) :
    kishDesignEffect w = empiricalWeightSecondMoment id n w := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [kishDesignEffect, if_neg]
  · simp only [empiricalWeightSecondMoment, id_eq, hsum, inv_eq_one_div]
    calc
      (n : ℝ) * (∑ x, w x ^ 2) / (n : ℝ) ^ 2 =
          ((n : ℝ) / (n : ℝ) ^ 2) * ∑ x, w x ^ 2 := by ring
      _ = 1 / (n : ℝ) * ∑ x, w x ^ 2 := by
        congr 1
        field_simp [hnR]
  · simpa [hsum] using hnR

/-- For [a probability measure](hyp:μ), [a real-valued weight](hyp:w),
[square-integrability of the weight](hyp:hw), and [population mean one](hyp:hmean),
[the weight's population second moment is at least one](goal). -/
lemma one_le_secondMoment_of_mean_one
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] (w : 𝒳 → ℝ)
    (hw : MemLp w 2 μ) (hmean : (∫ x, w x ∂μ) = 1) :
    1 ≤ ∫ x, w x ^ 2 ∂μ := by
  have hv := variance_nonneg w μ
  rw [variance_eq_sub hw, hmean] at hv
  norm_num at hv ⊢
  linarith

/-- For [a probability measure](hyp:μ), [a weight function](hyp:g),
[a sample size](hyp:n), [positivity of that size](hyp:hn), and
[integrability of the squared weight](hyp:hF),
[the expected empirical weight second moment equals its population counterpart](goal). -/
lemma empiricalWeightSecondMoment_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (hF : Integrable (fun o => g o ^ 2) μ) :
    (∫ sample : Fin n → Ω, empiricalWeightSecondMoment g n sample
        ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ o, g o ^ 2 ∂μ := by
  simpa [empiricalWeightSecondMoment] using
    Causalean.Mathlib.Probability.iid_average_integral μ n hn
      (fun o => g o ^ 2) hF

/-- For [a probability measure](hyp:μ), [a weight function](hyp:g),
[a sample size](hyp:n), [positivity of that size](hyp:hn), and
[integrability of the squared weight](hyp:hF), [this legacy compatibility theorem](goal) gives the
mean of the empirical weight second moment. -/
lemma empiricalKishDispersion_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (hF : Integrable (fun o => g o ^ 2) μ) :
    (∫ sample : Fin n → Ω, empiricalKishDispersion g n sample
        ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ o, g o ^ 2 ∂μ := by
  exact empiricalWeightSecondMoment_mean μ g n hn hF

/-- For [a probability measure](hyp:μ), [a weight function](hyp:g),
[a sample size](hyp:n), [a weight envelope](hyp:k),
[a population second-moment value](hyp:kappa), [positivity of the sample size](hyp:hn),
[square-integrability of the squared weight](hyp:hF),
[the population second-moment identity](hyp:hkappa), and
[the fourth-moment envelope](hyp:hfourth), [the stated variance bound holds](goal). -/
lemma empiricalWeightSecondMoment_variance_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (k kappa : ℝ) (hn : 0 < n)
    (hF : MemLp (fun o => g o ^ 2) 2 μ)
    (hkappa : (∫ o, g o ^ 2 ∂μ) = kappa)
    (hfourth : ∀ᵐ o ∂μ, g o ^ 4 ≤ 4 * k ^ 2 * g o ^ 2) :
    variance
        (fun sample : Fin n → Ω => empiricalWeightSecondMoment g n sample)
        (Measure.pi (fun _ : Fin n => μ)) ≤
      4 * k ^ 2 * kappa / n := by
  have hvar := Causalean.Mathlib.Probability.iid_average_variance μ n
    (fun o => g o ^ 2) hF
  have hsingle :
      variance (fun o => g o ^ 2) μ ≤ 4 * k ^ 2 * kappa := by
    calc
      variance (fun o => g o ^ 2) μ ≤
          ∫ o, (g o ^ 2) ^ 2 ∂μ :=
        variance_le_expectation_sq hF.aestronglyMeasurable
      _ = ∫ o, g o ^ 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards with o
        ring
      _ ≤ ∫ o, 4 * k ^ 2 * g o ^ 2 ∂μ := by
        have hleft : Integrable (fun o => g o ^ 4) μ := by
          have hpow : (fun o => g o ^ 4) = fun o => (g o ^ 2) ^ 2 := by
            funext o
            ring
          rw [hpow]
          exact hF.integrable_sq
        exact integral_mono_ae hleft
          (hF.integrable (by norm_num) |>.const_mul _) hfourth
      _ = 4 * k ^ 2 * kappa := by
        rw [integral_const_mul, hkappa]
  change variance
      (fun sample : Fin n → Ω =>
        (n : ℝ)⁻¹ * ∑ i, g (sample i) ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) ≤ _
  rw [hvar]
  calc
    (n : ℝ)⁻¹ * variance (fun o => g o ^ 2) μ ≤
        (n : ℝ)⁻¹ * (4 * k ^ 2 * kappa) := by
      gcongr
    _ = 4 * k ^ 2 * kappa / n := by ring

/-- For [a probability measure](hyp:μ), [a weight function](hyp:g),
[a sample size](hyp:n), [a weight envelope](hyp:k),
[a population second-moment value](hyp:kappa), [positivity of the sample size](hyp:hn),
[square-integrability of the squared weight](hyp:hF),
[the population second-moment identity](hyp:hkappa), and
[the fourth-moment envelope](hyp:hfourth), [this legacy compatibility theorem](goal) gives the
variance bound for the empirical weight second moment. -/
lemma empiricalKishDispersion_variance_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (k kappa : ℝ) (hn : 0 < n)
    (hF : MemLp (fun o => g o ^ 2) 2 μ)
    (hkappa : (∫ o, g o ^ 2 ∂μ) = kappa)
    (hfourth : ∀ᵐ o ∂μ, g o ^ 4 ≤ 4 * k ^ 2 * g o ^ 2) :
    variance
        (fun sample : Fin n → Ω => empiricalKishDispersion g n sample)
        (Measure.pi (fun _ : Fin n => μ)) ≤
      4 * k ^ 2 * kappa / n := by
  exact empiricalWeightSecondMoment_variance_le μ g n k kappa hn hF hkappa hfourth

/-- Given [a sample size](hyp:n), [a sampling probability measure](hyp:Q),
[a weight function](hyp:g), [a weight envelope](hyp:k),
[a positive reference mean](hyp:kappa), [positivity of the sample size](hyp:hn),
[positivity of the reference mean](hyp:hkappa),
[square-integrability of the empirical second moment](hyp:hF),
[its assumed exact mean](hyp:hmean), and [its assumed variance bound](hyp:hvar),
[Chebyshev's inequality bounds the probability of falling below half the reference mean](goal). -/
lemma empiricalWeightSecondMoment_lower_tail_le_of_mean_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (Q : Measure (Fin n → Ω)) [IsProbabilityMeasure Q]
    (g : Ω → ℝ) (k kappa : ℝ)
    (hn : 0 < n) (hkappa : 0 < kappa)
    (hF : MemLp (empiricalWeightSecondMoment g n) 2 Q)
    (hmean : (∫ sample, empiricalWeightSecondMoment g n sample ∂Q) = kappa)
    (hvar : variance (empiricalWeightSecondMoment g n) Q ≤
      4 * k ^ 2 * kappa / n) :
    (Q {sample | empiricalWeightSecondMoment g n sample < kappa / 2}).toReal ≤
      16 * k ^ 2 / ((n : ℝ) * kappa) := by
  have hcheb := Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le Q
    (empiricalWeightSecondMoment g n) kappa (4 * k ^ 2 * kappa / n)
      (kappa / 2) hF (half_pos hkappa) hmean hvar
  have hsub :
      {sample | empiricalWeightSecondMoment g n sample < kappa / 2} ⊆
        {sample | kappa / 2 <
          |empiricalWeightSecondMoment g n sample - kappa|} := by
    intro sample hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [abs_of_neg (by linarith)]
    linarith
  calc
    (Q {sample | empiricalWeightSecondMoment g n sample < kappa / 2}).toReal ≤
        (Q {sample | kappa / 2 <
          |empiricalWeightSecondMoment g n sample - kappa|}).toReal :=
      measureReal_mono hsub
    _ ≤ (4 * k ^ 2 * kappa / n) / (kappa / 2) ^ 2 := hcheb
    _ = 16 * k ^ 2 / ((n : ℝ) * kappa) := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [hnR.ne', hkappa.ne']
      ring

/-- Given [a sample size](hyp:n), [a sampling probability measure](hyp:Q),
[a weight function](hyp:g), [a weight envelope](hyp:k),
[a positive reference mean](hyp:kappa), [positivity of the sample size](hyp:hn),
[positivity of the reference mean](hyp:hkappa),
[square-integrability of the empirical second moment](hyp:hF),
[its assumed exact mean](hyp:hmean), and [its assumed variance bound](hyp:hvar),
[this legacy compatibility theorem](goal) is the Chebyshev specialization now named
`empiricalWeightSecondMoment_lower_tail_le_of_mean_variance`. -/
lemma empiricalKishDispersion_lower_tail_le
    {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (Q : Measure (Fin n → Ω)) [IsProbabilityMeasure Q]
    (g : Ω → ℝ) (k kappa : ℝ)
    (hn : 0 < n) (hkappa : 0 < kappa)
    (hF : MemLp (empiricalKishDispersion g n) 2 Q)
    (hmean : (∫ sample, empiricalKishDispersion g n sample ∂Q) = kappa)
    (hvar : variance (empiricalKishDispersion g n) Q ≤
      4 * k ^ 2 * kappa / n) :
    (Q {sample | empiricalKishDispersion g n sample < kappa / 2}).toReal ≤
      16 * k ^ 2 / ((n : ℝ) * kappa) := by
  exact empiricalWeightSecondMoment_lower_tail_le_of_mean_variance
    n Q g k kappa hn hkappa hF hmean hvar

/-- For [a population probability measure](hyp:μ), [a weight function](hyp:g),
[a sample size](hyp:n), [a weight envelope](hyp:k),
[a positive population second-moment value](hyp:kappa),
[positivity of the sample size](hyp:hn), [positivity of that moment](hyp:hkappa),
[square-integrability of the squared weight](hyp:hF),
[the population second-moment identity](hyp:hmoment), and
[the fourth-moment envelope](hyp:hfourth), [the stated product-law lower-tail bound holds](goal). -/
lemma empiricalWeightSecondMoment_lower_tail_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (k kappa : ℝ)
    (hn : 0 < n) (hkappa : 0 < kappa)
    (hF : MemLp (fun o => g o ^ 2) 2 μ)
    (hmoment : (∫ o, g o ^ 2 ∂μ) = kappa)
    (hfourth : ∀ᵐ o ∂μ, g o ^ 4 ≤ 4 * k ^ 2 * g o ^ 2) :
    ((Measure.pi (fun _ : Fin n => μ))
      {sample | empiricalWeightSecondMoment g n sample < kappa / 2}).toReal ≤
      16 * k ^ 2 / ((n : ℝ) * kappa) := by
  have hsample :
      MemLp (empiricalWeightSecondMoment g n) 2
        (Measure.pi (fun _ : Fin n => μ)) := by
    unfold empiricalWeightSecondMoment
    apply MemLp.const_mul
    simpa using memLp_finsetSum Finset.univ fun i _ =>
      hF.comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => μ) i)
  exact empiricalWeightSecondMoment_lower_tail_le_of_mean_variance
    n (Measure.pi (fun _ : Fin n => μ)) g k kappa hn hkappa hsample
    ((empiricalWeightSecondMoment_mean μ g n hn
      (hF.integrable (by norm_num))).trans hmoment)
    (empiricalWeightSecondMoment_variance_le μ g n k kappa hn hF hmoment hfourth)

end

end Causalean.Stat
