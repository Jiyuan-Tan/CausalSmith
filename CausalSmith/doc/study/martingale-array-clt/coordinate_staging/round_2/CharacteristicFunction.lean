/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic
import Causalean.Stat.CLT.MartingaleArray.CompensatedTelescoping
import Causalean.Stat.CLT.MartingaleArray.ConditionalTaylor
import Causalean.Stat.CLT.MartingaleArray.ConditionalTelescoping
import Causalean.Stat.CLT.MartingaleArray.ExponentialBounds
import Causalean.Stat.CLT.MartingaleArray.GaussianBounds
import Causalean.Stat.CLT.MartingaleArray.PredictableVarianceBounds
import Causalean.Stat.CLT.MartingaleArray.ProbabilityBounds
import Causalean.Stat.CLT.MartingaleArray.RemainderBudget
import Causalean.Stat.CLT.MartingaleArray.StoppedArray
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! # Characteristic-function core of the martingale-array CLT

This module isolates the analytic core of the scalar martingale triangular-array
central limit theorem.  It turns predictable-variance normalization and the
conditional Lindeberg condition into pointwise convergence of characteristic
functions.  The final weak-convergence wrapper is in `Main`.
-/

namespace Causalean.Stat

open Complex Filter MeasureTheory ProbabilityTheory Topology

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

private theorem stoppedArray_predictableQuadraticVariation_ae_eq_of_bounds
    [∀ n, IsFiniteMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (η K δ : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂(μ n), A.predictableQuadraticVariation n ω ≤ K →
      A.conditionalLindeberg η n ω ≤ δ →
        (A.stoppedArray η K δ).predictableQuadraticVariation n ω =
          A.predictableQuadraticVariation n ω := by
  have hmoment (k : ℕ) (hk : k < A.rowLength n) :
      (μ n)[fun ω => ((A.stoppedArray η K δ).increment n k ω) ^ 2 |
          (A.stoppedArray η K δ).filtration n k] =ᵐ[μ n]
        fun ω => A.stopMultiplier η K δ n k ω *
          (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω := by
    let M := A.stopMultiplier η K δ n k
    have hsm : StronglyMeasurable[A.filtration n k] M :=
      A.stopMultiplier_stronglyMeasurable η K δ n k hk
    have hsq : Integrable (fun ω => (A.increment n k ω) ^ 2) (μ n) :=
      (A.squareIntegrable n k hk).integrable_sq
    have hprod : Integrable (fun ω => M ω * (A.increment n k ω) ^ 2) (μ n) := by
      refine hsq.bdd_mul (c := 1)
        (hsm.mono ((A.filtration n).le k)).aestronglyMeasurable ?_
      filter_upwards with ω
      dsimp only [M]
      unfold MartingaleDifferenceArray.stopMultiplier
      split_ifs <;> simp
    calc
      (μ n)[fun ω => ((A.stoppedArray η K δ).increment n k ω) ^ 2 |
          (A.stoppedArray η K δ).filtration n k] =ᵐ[μ n]
          (μ n)[fun ω => M ω * (A.increment n k ω) ^ 2 |
            A.filtration n k] := by
              apply condExp_congr_ae
              filter_upwards with ω
              dsimp only [M]
              simp only [MartingaleDifferenceArray.stoppedArray_increment]
              unfold MartingaleDifferenceArray.stopMultiplier
              split_ifs <;> simp
      _ =ᵐ[μ n] fun ω => M ω *
          (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω :=
        condExp_mul_of_stronglyMeasurable_left hsm hprod hsq
  have hmoment_all : ∀ᵐ ω ∂(μ n), ∀ k, k < A.rowLength n →
      (μ n)[fun ω => ((A.stoppedArray η K δ).increment n k ω) ^ 2 |
          (A.stoppedArray η K δ).filtration n k] ω =
        A.stopMultiplier η K δ n k ω *
          (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : k < A.rowLength n
    · exact (hmoment k hk).mono fun ω hω _ => hω
    · exact ae_of_all _ fun _ h => (hk h).elim
  have hx : ∀ᵐ ω ∂(μ n), ∀ k,
      0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω :=
    ae_all_iff.mpr fun k => condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
  have hy : ∀ᵐ ω ∂(μ n), ∀ k, 0 ≤ A.lindebergTerm η n k ω := by
    apply ae_all_iff.mpr
    intro k
    apply condExp_nonneg
    filter_upwards with ω
    split_ifs <;> positivity
  filter_upwards [hmoment_all, hx, hy] with ω hmω hxω hyω
  intro hV hL
  unfold MartingaleDifferenceArray.predictableQuadraticVariation
  simp only [Finset.sum_apply, MartingaleDifferenceArray.stoppedArray_rowLength]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hmω k (Finset.mem_range.mp hk)]
  have hkr : k < A.rowLength n := Finset.mem_range.mp hk
  have hVr : A.predictableQuadraticVariationThrough n k ω ≤
      A.predictableQuadraticVariation n ω := by
    unfold MartingaleDifferenceArray.predictableQuadraticVariationThrough
      MartingaleDifferenceArray.predictableQuadraticVariation
    simp only [Finset.sum_apply]
    rw [min_eq_left (Nat.succ_le_iff.mpr hkr)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_iff.mpr hkr))
      (fun i _ _ => hxω i)
  have hLr : A.conditionalLindebergThrough η n k ω ≤
      A.conditionalLindeberg η n ω := by
    unfold MartingaleDifferenceArray.conditionalLindebergThrough
      MartingaleDifferenceArray.conditionalLindeberg
    simp only [Finset.sum_apply]
    rw [min_eq_left (Nat.succ_le_iff.mpr hkr)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_iff.mpr hkr))
      (fun i _ _ => hyω i)
  have hmul : A.stopMultiplier η K δ n k ω = 1 := by
    rw [MartingaleDifferenceArray.stopMultiplier, if_pos]
    exact ⟨hVr.trans hV, hLr.trans hL⟩
  simp [hmul]

/-- For [a square-integrable martingale-difference triangular array](hyp:A), if [its
predictable quadratic variations converge in probability to one](hyp:hVariance) and [its
conditional Lindeberg sums converge in probability to zero at every positive
threshold](hyp:hLindeberg), then [the characteristic function of each row sum converges
pointwise to the characteristic function of the standard normal law](goal). -/
theorem martingaleArrayCharFun_tendsto
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hVariance : TendstoInProbability μ A.predictableQuadraticVariation 1)
    (hLindeberg : ∀ ε : ℝ, 0 < ε →
      TendstoInProbability μ (A.conditionalLindeberg ε) 0)
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (A.rowSum n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  /-
  Brown--Hall--Heyde characteristic-function argument.

  1. For fixed `t` and truncation level `ε`, stop a row when either accumulated
     predictable variance or accumulated conditional Lindeberg mass leaves a
     deterministic good set.  The two convergence-in-probability hypotheses
     show that stopping changes the characteristic function by `o(1)`.
  2. On the good set, condition successively on `filtration n k`.  The linear
     Taylor term vanishes by `A.condExp_zero`; the quadratic term is the
     conditional variance, and the Taylor remainder is bounded by the
     conditional Lindeberg term plus `O(ε)` times predictable variance.
  3. Telescope the one-step conditional characteristic functions and compare
     their product with `exp (-(t^2)/2)`.  First let the row index tend to
     infinity, then let `ε` tend to zero.
  4. Rewrite the limit using `charFun_gaussianReal`.

  The proof uses no independence: every factorization is through conditional
  expectation at the preceding filtration time.
  -/
  have hPQVMeas (B : MartingaleDifferenceArray Ω μ) (n : ℕ) :
      AEMeasurable (B.predictableQuadraticVariation n) (μ n) := by
    unfold MartingaleDifferenceArray.predictableQuadraticVariation
    apply Finset.aemeasurable_sum
    intro k _
    exact (integrable_condExp : Integrable
      ((μ n)[fun ω => (B.increment n k ω) ^ 2 | B.filtration n k]) (μ n)).aemeasurable
  have hPQVNonneg (B : MartingaleDifferenceArray Ω μ) (n : ℕ) :
      0 ≤ᵐ[μ n] B.predictableQuadraticVariation n := by
    have hall : ∀ᵐ ω ∂(μ n), ∀ k,
        0 ≤ (μ n)[fun ω => (B.increment n k ω) ^ 2 | B.filtration n k] ω :=
      ae_all_iff.mpr fun k =>
        condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (B.increment n k ω))
    filter_upwards [hall] with ω hω
    unfold MartingaleDifferenceArray.predictableQuadraticVariation
    simp only [Finset.sum_apply]
    exact Finset.sum_nonneg fun k _ => hω k
  have hVBad : Tendsto (fun n => (μ n).real
      {ω | 2 < A.predictableQuadraticVariation n ω}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
      ((ENNReal.tendsto_toReal_zero_iff).2 (hVariance 1 zero_lt_one))
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    change 2 < A.predictableQuadraticVariation n ω at hω
    change 1 ≤ |A.predictableQuadraticVariation n ω - 1|
    rw [abs_of_pos (by linarith)]
    linarith
  have hLBad (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      Tendsto (fun n => (μ n).real
        {ω | δ < A.conditionalLindeberg η n ω}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
      ((ENNReal.tendsto_toReal_zero_iff).2 (hLindeberg η hη δ hδ))
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    change δ ≤ |A.conditionalLindeberg η n ω - 0|
    rw [sub_zero, abs_of_pos (hδ.trans hω)]
    exact hω.le
  have hBad (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      Tendsto (fun n => (μ n).real
        ({ω | 2 < A.predictableQuadraticVariation n ω} ∪
          {ω | δ < A.conditionalLindeberg η n ω})) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => measureReal_union_le _ _)
    simpa using hVBad.add (hLBad η δ hη hδ)
  have hStopProb (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      Tendsto (fun n => (μ n).real
        {ω | (A.stoppedArray η 2 δ).rowSum n ω ≠ A.rowSum n ω})
        atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) (hBad η δ hη hδ)
    rw [measureReal_def, measureReal_def]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2
    exact A.measure_stoppedArray_rowSum_ne_le η 2 δ hη n
  have hStoppedVariance (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      TendstoInProbability μ
        (A.stoppedArray η 2 δ).predictableQuadraticVariation 1 := by
    intro ε hε
    rw [← ENNReal.tendsto_toReal_zero_iff]
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
      (by
        have hv := (ENNReal.tendsto_toReal_zero_iff).2 (hVariance ε hε)
        have hb := hVBad.add (hLBad η δ hη hδ)
        simpa only [measureReal_def, add_zero] using hv.add hb)
    let E : Set (Ω n) := {ω |
      ε ≤ |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1|}
    let F : Set (Ω n) := {ω | ε ≤ |A.predictableQuadraticVariation n ω - 1|}
    let G : Set (Ω n) := {ω | 2 < A.predictableQuadraticVariation n ω}
    let H : Set (Ω n) := {ω | δ < A.conditionalLindeberg η n ω}
    have hmono : (μ n).real E ≤ (μ n).real (F ∪ (G ∪ H)) := by
      rw [measureReal_def, measureReal_def]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2
      apply measure_mono_ae
      filter_upwards [stoppedArray_predictableQuadraticVariation_ae_eq_of_bounds
        A η 2 δ n] with ω heq
      intro hω
      by_cases hF : ω ∈ F
      · exact Or.inl hF
      by_cases hG : ω ∈ G
      · exact Or.inr (Or.inl hG)
      by_cases hH : ω ∈ H
      · exact Or.inr (Or.inr hH)
      exfalso
      apply hF
      change ε ≤ |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1| at hω
      change ε ≤ |A.predictableQuadraticVariation n ω - 1|
      change ¬2 < A.predictableQuadraticVariation n ω at hG
      change ¬δ < A.conditionalLindeberg η n ω at hH
      rw [heq (le_of_not_gt hG) (le_of_not_gt hH)] at hω
      exact hω
    calc
      (μ n).real {ω |
          ε ≤ |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1|} =
          (μ n).real E := rfl
      _ ≤ (μ n).real (F ∪ (G ∪ H)) := hmono
      _ ≤ (μ n).real F + ((μ n).real G + (μ n).real H) := by
        exact (measureReal_union_le F (G ∪ H)).trans
          (add_le_add le_rfl (measureReal_union_le G H))
      _ = _ := rfl
  have hStoppedVarianceL1 (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      Tendsto (fun n => ∫ ω,
        |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1| ∂(μ n))
        atTop (𝓝 0) := by
    apply tendsto_integral_abs_sub_of_tendstoInProbability_of_ae_bound
      (fun n => (A.stoppedArray η 2 δ).predictableQuadraticVariation n) 1 3
      (fun n => hPQVMeas (A.stoppedArray η 2 δ) n) (by norm_num) _
      (hStoppedVariance η δ hη hδ)
    intro n
    filter_upwards [hPQVNonneg (A.stoppedArray η 2 δ) n,
      A.stoppedArray_predictableQuadraticVariation_le η 2 δ (by norm_num)
        hδ.le n] with ω h0 h2
    simp only [Pi.zero_apply] at h0
    rw [abs_le]
    constructor <;> linarith
  have hCharIntegral (B : MartingaleDifferenceArray Ω μ) (n : ℕ) :
      charFun ((μ n).map (B.rowSum n)) t =
        ∫ ω, Complex.exp (Complex.I * ((t * B.rowSum n ω : ℝ) : ℂ)) ∂(μ n) := by
    rw [charFun_apply_real, integral_map (B.rowSum_aemeasurable n) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
    push_cast
    ring
  have hStopIntegral (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      Tendsto (fun n => ‖
        (∫ ω, Complex.exp (Complex.I *
          ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
        ∫ ω, Complex.exp (Complex.I *
          ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)‖)
        atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by
        have hc : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
        simpa using hc.mul (hStopProb η δ hη hδ))
    let g : Ω n → ℂ := fun ω => Complex.exp (Complex.I *
      ((t * A.rowSum n ω : ℝ) : ℂ))
    let gs : Ω n → ℂ := fun ω => Complex.exp (Complex.I *
      ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ))
    let E : Set (Ω n) :=
      {ω | (A.stoppedArray η 2 δ).rowSum n ω ≠ A.rowSum n ω}
    have hgMeas : AEStronglyMeasurable g (μ n) := by
      have hrow := A.rowSum_aemeasurable n
      dsimp [g]
      fun_prop
    have hgsMeas : AEStronglyMeasurable gs (μ n) := by
      have hrow := (A.stoppedArray η 2 δ).rowSum_aemeasurable n
      dsimp [gs]
      fun_prop
    have hgInt : Integrable g (μ n) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hgMeas ?_
      filter_upwards with ω
      dsimp [g]
      rw [Complex.norm_exp]
      simp
    have hgsInt : Integrable gs (μ n) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hgsMeas ?_
      filter_upwards with ω
      dsimp [gs]
      rw [Complex.norm_exp]
      simp
    have hE : NullMeasurableSet E (μ n) := by
      have hd := (A.stoppedArray η 2 δ).rowSum_aemeasurable n |>.sub
        (A.rowSum_aemeasurable n)
      have hp := hd.nullMeasurableSet_preimage
        (measurableSet_singleton (0 : ℝ)).compl
      convert hp using 1
      ext ω
      change ((A.stoppedArray η 2 δ).rowSum n ω ≠ A.rowSum n ω) ↔
        (A.stoppedArray η 2 δ).rowSum n ω - A.rowSum n ω ≠ 0
      exact (sub_ne_zero : ∀ {a b : ℝ}, a - b ≠ 0 ↔ a ≠ b).symm
    change ‖(∫ ω, g ω ∂(μ n)) - ∫ ω, gs ω ∂(μ n)‖ ≤ _
    rw [← integral_sub hgInt hgsInt]
    calc
      ‖∫ ω, g ω - gs ω ∂(μ n)‖ ≤ ∫ ω, ‖g ω - gs ω‖ ∂(μ n) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, E.indicator (fun _ => (2 : ℝ)) ω ∂(μ n) := by
        apply integral_mono_ae (hgInt.sub hgsInt).norm
          ((integrable_const (2 : ℝ)).indicator₀ hE)
        filter_upwards with ω
        by_cases he : ω ∈ E
        · rw [Set.indicator_of_mem he]
          exact (norm_sub_le _ _).trans_eq (by
            dsimp [g, gs]
            rw [Complex.norm_exp, Complex.norm_exp]
            norm_num)
        · rw [Set.indicator_of_notMem he]
          have heq : (A.stoppedArray η 2 δ).rowSum n ω = A.rowSum n ω :=
            not_ne_iff.mp he
          simp [g, gs, heq]
      _ = 2 * (μ n).real E := by
        rw [integral_indicator₀ hE, setIntegral_const]
        simp [mul_comm]
      _ = 2 * (μ n).real
          {ω | (A.stoppedArray η 2 δ).rowSum n ω ≠ A.rowSum n ω} := rfl
  have hGaussian : charFun (gaussianReal 0 1) t =
      ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
    rw [charFun_gaussianReal]
    rw [show ((1 : NNReal) : ℝ) = 1 by rfl]
    push_cast
    congr 1
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R₀ : ℝ → ℝ := fun η =>
    Real.exp ((t ^ 2 / 2) * 2) *
      (|t| ^ 3 * η * 2 +
        ((t ^ 2 / 2) ^ 2 / 2) * ((η ^ 2 + 0) * 2))
  have hR₀ : Tendsto R₀ (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt R₀ 0 := by
      dsimp [R₀]
      fun_prop
    simpa [R₀] using hc.tendsto
  have hR₀small : ∀ᶠ η in 𝓝 (0 : ℝ), dist (R₀ η) 0 < ε / 4 :=
    Metric.tendsto_nhds.mp hR₀ (ε / 4) (by linarith)
  rcases Metric.mem_nhds_iff.mp hR₀small with ⟨r, hr, hrsub⟩
  let η : ℝ := min (r / 2) (1 / (|t| + 1))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (div_pos hr (by norm_num))
      (one_div_pos.mpr (by linarith [abs_nonneg t]))
  have hηr : η < r :=
    lt_of_le_of_lt (min_le_left _ _) (div_lt_self hr (by norm_num))
  have hηsmallDist : dist (R₀ η) 0 < ε / 4 := by
    apply hrsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hη.le]
    exact hηr
  have hηsmall : R₀ η < ε / 4 := by
    exact (le_abs_self (R₀ η)).trans_lt (by
      simpa [Real.dist_eq] using hηsmallDist)
  have htη : |t| * η ≤ 1 := by
    calc
      |t| * η ≤ |t| * (1 / (|t| + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg t)
      _ = |t| / (|t| + 1) := by ring
      _ ≤ 1 := (div_lt_one (by linarith [abs_nonneg t])).2
        (by linarith [abs_nonneg t]) |>.le
  let D : ℝ → ℝ := fun δ =>
    Real.exp ((t ^ 2 / 2) * 2) *
      (|t| ^ 3 * η * 2 +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ +
        ((t ^ 2 / 2) ^ 2 / 2) * ((η ^ 2 + δ) * 2))
  have hD : Tendsto D (𝓝 0) (𝓝 (R₀ η)) := by
    have hc : ContinuousAt D 0 := by
      dsimp [D]
      fun_prop
    convert hc.tendsto using 1
    simp [D, R₀]
  have hDsmall : ∀ᶠ δ in 𝓝 (0 : ℝ), D δ < ε / 2 :=
    (tendsto_order.1 hD).2 (ε / 2) (by linarith)
  rcases Metric.mem_nhds_iff.mp hDsmall with ⟨s, hs, hssub⟩
  let δ : ℝ := min (s / 2) 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hs (by norm_num)) zero_lt_one
  have hδs : δ < s :=
    lt_of_le_of_lt (min_le_left _ _) (div_lt_self hs (by norm_num))
  have hDδ : D δ < ε / 2 := by
    apply hssub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hδ.le]
    exact hδs
  let C : ℝ := Real.exp ((t ^ 2 / 2) * max (2 : ℝ) 1) * (t ^ 2 / 2)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hL1scaled : Tendsto (fun n => C *
      ∫ ω, |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1| ∂(μ n))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa using hc.mul (hStoppedVarianceL1 η δ hη hδ)
  have hStopEventually : ∀ᶠ n in atTop, ‖
      (∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
      ∫ ω, Complex.exp (Complex.I *
        ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)‖ < ε / 4 :=
    (tendsto_order.1 (hStopIntegral η δ hη hδ)).2 (ε / 4) (by linarith)
  have hL1Eventually : ∀ᶠ n in atTop, C *
      ∫ ω, |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1| ∂(μ n) <
        ε / 4 :=
    (tendsto_order.1 hL1scaled).2 (ε / 4) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hStopEventually.and hL1Eventually)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hStopN, hL1N⟩
  have hBudget :=
    (A.stoppedArray η 2 δ).norm_integral_cexp_rowSum_sub_gaussian_le_of_budgets
      n t η 2 δ hη htη (by norm_num) hδ.le
      (A.stoppedArray_predictableQuadraticVariation_le η 2 δ (by norm_num)
        hδ.le n)
      (A.stoppedArray_conditionalLindeberg_le η 2 δ hη (by norm_num)
        hδ.le n)
  have hBudget' : ‖
      (∫ ω, Complex.exp (Complex.I *
        ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
      ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ D δ + C *
        ∫ ω, |(A.stoppedArray η 2 δ).predictableQuadraticVariation n ω - 1| ∂(μ n) := by
    simpa only [D, C] using hBudget
  rw [hCharIntegral A n, hGaussian, dist_eq_norm]
  calc
    ‖(∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
        ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
        ‖(∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
          ∫ ω, Complex.exp (Complex.I *
            ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)‖ +
        ‖(∫ ω, Complex.exp (Complex.I *
            ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
          ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)‖ := by
            calc
              _ = ‖((∫ ω, Complex.exp (Complex.I *
                    ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
                  ∫ ω, Complex.exp (Complex.I *
                    ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)) +
                ((∫ ω, Complex.exp (Complex.I *
                    ((t * (A.stoppedArray η 2 δ).rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
                  ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ))‖ := by congr 1 <;> ring
              _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hBudget'
    _ < ε := by linarith

end Causalean.Stat
