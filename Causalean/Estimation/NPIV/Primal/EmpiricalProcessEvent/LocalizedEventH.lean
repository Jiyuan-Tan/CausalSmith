/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventsBase

/-! # Localized Deviation for the Primal Class `H`

This file constructs high-probability events controlling empirical fluctuations
over pairs of candidate primal functions in the NPIV primal rate argument. Here
`H` is the primal hypothesis class `TC.H`.  The event is one component of the
localized empirical-process control needed for the Tikhonov-regularized
adversarial estimator. -/

public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Fixed-diameter localized deviation event for the candidate class `star(H)`.** Given [a
positive sample size `n`](hyp:hn) and [a confidence level `δ` in `(0, 1]`](hyp:hδ_pos,hδ_le),
[there is a single event of probability at least `1 − δ`, valid simultaneously for every pair
`h₁, h₂` in the primal hypothesis class `TC.H`, on which the gap between the fold's empirical
second-moment difference `(1/n) Σ_k h₁(X_k)² − (1/n) Σ_k h₂(X_k)²` and its population
counterpart `E[h₁(X)²] − E[h₂(X)²]` is bounded by `4 · (H_diameter + δ_n) · criticalRadius(ψ n)`
plus a `√(2·log(1/δ)/n)` deviation term](goal), where `H_diameter` and the critical-radius
regime come from the supplied localized-regime witness.

Produces a *single* μ-event simultaneously valid for **every pair** `(h₁, h₂) ∈ TC.H × TC.H`.
The radius is fixed at `H_diameter + δ_n`, using `regime.H_diameter_bound` and
`interp_H_norm`.  This avoids the dyadic peeling infrastructure needed for a pair-gap rate, at
the cost of a diameter-rate leading term. -/
lemma localized_omega_event_for_H
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    [IsProbabilityMeasure μ]
    {β lambda : ℝ}
    {sc : SourceCondition S β}
    {tb : TikhonovBiasBoundAt S β lambda sc}
    {n : ℕ} {δ_n : ℝ}
    (regime : LocalizedRegimes S TC sample sc tb n δ_n)
    (hn : 0 < n)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    ∃ E : Set Ω,
      MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ h₁, ∀ _hh₁ : h₁ ∈ TC.H, ∀ h₂, ∀ _hh₂ : h₂ ∈ TC.H,
        |((n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
            - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2)
          - (∫ ω', (h₁ (S.xOf (S.W ω'))) ^ 2 ∂μ
              - ∫ ω', (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ)|
          ≤ 4 * (regime.H_diameter + δ_n) *
                criticalRadius (regime.bundle_H.regime.ψ n)
            + 2 * Real.sqrt
                (((regime.H_diameter + δ_n) ^ 2 +
                    8 * regime.bundle_H.regime.b * (regime.H_diameter + δ_n) *
                      criticalRadius (regime.bundle_H.regime.ψ n)) *
                  Real.log (1 / δ) / n)
            + 8 * regime.bundle_H.regime.b * Real.log (1 / δ) / n := by
  classical
  let B := regime.bundle_H
  let r : ℝ := regime.H_diameter + δ_n
  haveI : IsProbabilityMeasure P_W := by
    rw [← regime.law_W]
    exact Measure.isProbabilityMeasure_map S.meas_W.aemeasurable
  have hδn_pos : 0 < δ_n := lt_of_lt_of_le B.crit_pos B.crit_le
  have hδn_nonneg : 0 ≤ δ_n := le_of_lt hδn_pos
  have hdiam_nonneg : 0 ≤ regime.H_diameter :=
    hδn_nonneg.trans regime.H_diameter_lb
  have hr_lb : criticalRadius (B.regime.ψ n) ≤ r := by
    dsimp [r]
    linarith [B.crit_le, hdiam_nonneg]
  have hr_delta : δ_n ≤ r := by
    dsimp [r]
    linarith [hdiam_nonneg]
  obtain ⟨E₀, hE₀_meas, hE₀_prob, hE₀_bound⟩ :=
    localized_uniform_deviation B.F B.norm P_W B.X B.X_meas B.F_meas B.norm_nonneg B.regime
      hδ_pos hδ_le n hn hr_lb B.crit_pos
      (B.rad_bdd r hr_delta) (B.rad_int r hr_delta)
  let Ψ : Ω → (Fin n → S.𝒲) := fun ω k => sample.Z k ω
  let E : Set Ω := Ψ ⁻¹' E₀
  have hpull :=
    Causalean.Stat.event_pullback_along_iidSample sample n hE₀_meas hE₀_prob
  refine ⟨E, ?_, ?_, ?_⟩
  · simpa [E, Ψ] using hpull.1
  · simpa [E, Ψ] using hpull.2
  · intro ω hω h₁ hh₁ h₂ hh₂
    let i : B.ι := regime.interp_H_idx h₁ h₂ hh₁ hh₂
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hgap_le :
        S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
          ≤ regime.H_diameter :=
      regime.H_diameter_bound h₁ h₂ hh₁ hh₂
    have hi_norm : B.norm (B.F i) ≤ r := by
      have hi_gap := regime.interp_H_norm h₁ h₂ hh₁ hh₂
      dsimp [r]
      linarith
    have hdev := hE₀_bound (Ψ ω) hω₀ i hi_norm
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W regime.law_W ((B.F_meas i).comp B.X_meas)
    have heval_sample :
        (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
          ∑ k : Fin n,
            ((h₁ (S.xOf (sample.Z k ω))) ^ 2
              - (h₂ (S.xOf (sample.Z k ω))) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [B, i] using regime.interp_H_eval h₁ h₂ hh₁ hh₂ (sample.Z k ω)
    have heval_pop :
        (fun ω' => B.F i (B.X (S.W ω'))) =
          fun ω' =>
            (h₁ (S.xOf (S.W ω'))) ^ 2 - (h₂ (S.xOf (S.W ω'))) ^ 2 := by
      funext ω'
      simpa [B, i] using regime.interp_H_eval h₁ h₂ hh₁ hh₂ (S.W ω')
    have hsample_split :
        (n : ℝ)⁻¹ *
            (∑ k : Fin n,
              ((h₁ (S.xOf (sample.Z k ω))) ^ 2
                - (h₂ (S.xOf (sample.Z k ω))) ^ 2))
          =
        (n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
          - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2 := by
      rw [Finset.sum_sub_distrib, mul_sub]
    have hsample_split' :
        (n : ℝ)⁻¹ *
            ((∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2)
              - ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2)
          =
        (n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
          - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2 := by
      ring
    have hsq₁_int :
        Integrable (fun ω' => (h₁ (S.xOf (S.W ω'))) ^ 2) μ := by
      exact (S.toHbarL2 h₁ (TC.H_subset hh₁)).integrable_sq
    have hsq₂_int :
        Integrable (fun ω' => (h₂ (S.xOf (S.W ω'))) ^ 2) μ := by
      exact (S.toHbarL2 h₂ (TC.H_subset hh₂)).integrable_sq
    have hpop_split :
        (∫ ω',
            (h₁ (S.xOf (S.W ω'))) ^ 2 - (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ)
          =
        (∫ ω', (h₁ (S.xOf (S.W ω'))) ^ 2 ∂μ)
          - ∫ ω', (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ := by
      exact integral_sub hsq₁_int hsq₂_int
    simpa [Ψ, r, hpop, heval_sample, heval_pop, hsample_split,
      hsample_split', hpop_split]
      using hdev

/-- Given [a positive sample size](hyp:hn), [a confidence level in `(0,1]`](hyp:hdelta_pos,hdelta_le),
[a localized NPIV regime](hyp:regime), and [its fixed-level peeling floor](hyp:floor),
[there is one event of probability at least
`1 - delta` on which every squared-candidate empirical-process difference is bounded by
`10 * delta_n * strongNorm(h₁-h₂) + 5 * delta_n²`](goal).

This is the dyadically peeled candidate-class event used for the centered
Tikhonov regularizer. Its radius follows the actual candidate gap. -/
lemma localized_omega_event_for_H_pair_peeled
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    [IsProbabilityMeasure μ]
    {β lambda : ℝ}
    {sc : SourceCondition S β}
    {tb : TikhonovBiasBoundAt S β lambda sc}
    {n : ℕ} {δ_n : ℝ}
    (regime : LocalizedRegimes S TC sample sc tb n δ_n)
    (hn : 0 < n)
    {δ : ℝ} (hdelta_pos : 0 < δ) (hdelta_le : δ ≤ 1)
    (floor : PeelingFloor regime δ) :
    ∃ E : Set Ω,
      MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ h₁, ∀ hh₁ : h₁ ∈ TC.H, ∀ h₂, ∀ hh₂ : h₂ ∈ TC.H,
        |((n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
            - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2)
          - (∫ ω', (h₁ (S.xOf (S.W ω'))) ^ 2 ∂μ
              - ∫ ω', (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ)|
          ≤ 10 * δ_n *
              S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
            + 5 * δ_n ^ 2 := by
  classical
  let B := regime.bundle_H
  let Rmax : ℝ := max δ_n regime.H_diameter
  have hdelta_n_pos : 0 < δ_n := lt_of_lt_of_le B.crit_pos B.crit_le
  have hslack : ∃ K : ℕ,
      Rmax ≤ δ_n * (2 : ℝ) ^ K ∧
      2 * Real.sqrt
          ((1 + 8 * B.regime.b) * Real.log (2 * ((K : ℝ) + 1) / δ) / n)
        + 8 * B.regime.b * Real.log (2 * ((K : ℝ) + 1) / δ) / (n * δ_n)
        ≤ δ_n := by
    simpa [B, Rmax] using floor.H
  obtain ⟨E, hE_meas, hE_mass, hE⟩ :=
    localized_omega_event_sharp_for_bundle
      (S := S) (P_W := P_W) (sample := sample) (B := B)
      regime.law_W hn hdelta_pos hdelta_le hdelta_n_pos hslack
  refine ⟨E, hE_meas, hE_mass, ?_⟩
  intro ω hω h₁ hh₁ h₂ hh₂
  let i : B.ι := regime.interp_H_idx h₁ h₂ hh₁ hh₂
  let gap : ℝ :=
    S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
  have hi_gap : B.norm (B.F i) ≤ gap := by
    simpa [B, i, gap] using regime.interp_H_norm h₁ h₂ hh₁ hh₂
  have hi_Rmax : B.norm (B.F i) ≤ Rmax := by
    exact hi_gap.trans <| (regime.H_diameter_bound h₁ h₂ hh₁ hh₂).trans
      (le_max_right _ _)
  have hdev := hE ω hω i hi_Rmax
  have hdev' :
      |(n : ℝ)⁻¹ * ∑ k : Fin n, B.F i (B.X (sample.Z k ω))
          - ∫ ω', B.F i (B.X (S.W ω')) ∂μ|
        ≤ 10 * δ_n * gap + 5 * δ_n ^ 2 := by
    have hcoeff : 0 ≤ 10 * δ_n := mul_nonneg (by norm_num) hdelta_n_pos.le
    have hmul := mul_le_mul_of_nonneg_left hi_gap hcoeff
    nlinarith
  have heval_sample :
      (∑ k : Fin n, B.F i (B.X (sample.Z k ω))) =
        ∑ k : Fin n,
          ((h₁ (S.xOf (sample.Z k ω))) ^ 2
            - (h₂ (S.xOf (sample.Z k ω))) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k _
    simpa [B, i] using regime.interp_H_eval h₁ h₂ hh₁ hh₂ (sample.Z k ω)
  have heval_pop :
      (fun ω' => B.F i (B.X (S.W ω'))) =
        fun ω' =>
          (h₁ (S.xOf (S.W ω'))) ^ 2 - (h₂ (S.xOf (S.W ω'))) ^ 2 := by
    funext ω'
    simpa [B, i] using regime.interp_H_eval h₁ h₂ hh₁ hh₂ (S.W ω')
  have hsq₁_int : Integrable (fun ω' => (h₁ (S.xOf (S.W ω'))) ^ 2) μ :=
    (S.toHbarL2 h₁ (TC.H_subset hh₁)).integrable_sq
  have hsq₂_int : Integrable (fun ω' => (h₂ (S.xOf (S.W ω'))) ^ 2) μ :=
    (S.toHbarL2 h₂ (TC.H_subset hh₂)).integrable_sq
  rw [heval_sample, heval_pop, integral_sub hsq₁_int hsq₂_int,
    Finset.sum_sub_distrib, mul_sub] at hdev'
  simpa [gap] using hdev'

end Primal
end NPIV
end Estimation
end Causalean
