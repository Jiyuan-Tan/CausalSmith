/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic

/-! # Varying-space probability convergence bounds

This module supplies elementary expectation bridges for row-indexed random
variables whose rows may live on different probability spaces.  They are used
after stopping the martingale array, when convergence in probability combines
with a deterministic uniform bound.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Topology

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

/-- If [measurable real row variables](hyp:hMeas) [converge in probability to a
constant](hyp:hTendsto), [the bound is nonnegative](hyp:hB), and [their absolute deviations are uniformly bounded
almost everywhere](hyp:hBound), then [their expected absolute deviations tend
to zero](goal).  The probability spaces may vary with the row. -/
theorem tendsto_integral_abs_sub_of_tendstoInProbability_of_ae_bound
    [∀ n, IsProbabilityMeasure (μ n)]
    (Y : (n : ℕ) → Ω n → ℝ) (c B : ℝ)
    (hMeas : ∀ n, AEMeasurable (Y n) (μ n))
    (hB : 0 ≤ B)
    (hBound : ∀ n, ∀ᵐ ω ∂(μ n), |Y n ω - c| ≤ B)
    (hTendsto : TendstoInProbability μ Y c) :
    Tendsto (fun n => ∫ ω, |Y n ω - c| ∂(μ n)) atTop (𝓝 0) := by
  /-
  For a positive tolerance `ε`, split the integral over
  `{|Y-c| < ε}` and its complement.  The first part is at most `ε`; the second
  is at most `B` times the exceptional probability, which tends to zero by
  `hTendsto`.  `hMeas` and the a.e. bound supply all integrability and measurable
  set side conditions.  Treat `B = 0` directly.
  -/
  let f : (n : ℕ) → Ω n → ℝ := fun n ω => |Y n ω - c|
  have hfMeas : ∀ n, AEMeasurable (f n) (μ n) := fun n => by
    simpa only [f, Real.norm_eq_abs] using ((hMeas n).sub_const c).norm
  have hfInt : ∀ n, Integrable (f n) (μ n) := by
    intro n
    apply Integrable.of_bound (hfMeas n).aestronglyMeasurable B
    filter_upwards [hBound n] with ω hω
    simpa [f, Real.norm_eq_abs, abs_abs] using hω
  have hfNonneg : ∀ n, 0 ≤ ∫ ω, f n ω ∂(μ n) := fun n =>
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => abs_nonneg _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := div_pos hε (by norm_num)
  let s : (n : ℕ) → Set (Ω n) := fun n => {ω | δ ≤ f n ω}
  have hs : ∀ n, NullMeasurableSet (s n) (μ n) := by
    intro n
    exact (hfMeas n).nullMeasurableSet_preimage measurableSet_Ici
  have hprob : Tendsto (fun n => (μ n (s n)).toReal) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_toReal_zero_iff]
    simpa [s, f] using hTendsto δ hδ
  have hupperTendsto :
      Tendsto (fun n => δ + B * (μ n (s n)).toReal) atTop (𝓝 δ) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hprob)
  have hevUpper : ∀ᶠ n in atTop, δ + B * (μ n (s n)).toReal < ε := by
    exact (tendsto_order.1 hupperTendsto).2 ε (by dsimp [δ]; linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevUpper
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hIntUpper : (∫ ω, f n ω ∂(μ n)) ≤ δ + B * (μ n (s n)).toReal := by
    let g : Ω n → ℝ := fun ω => δ + B * (s n).indicator (fun _ => (1 : ℝ)) ω
    have hind : Integrable ((s n).indicator (fun _ => (1 : ℝ))) (μ n) :=
      (integrable_const (1 : ℝ)).indicator₀ (hs n)
    have hg : Integrable g (μ n) := by
      exact (integrable_const δ).add (hind.const_mul B)
    calc
      (∫ ω, f n ω ∂(μ n)) ≤ ∫ ω, g ω ∂(μ n) := by
        apply integral_mono_ae (hfInt n) hg
        filter_upwards [hBound n] with ω hω
        by_cases htail : ω ∈ s n
        · simp only [g, Set.indicator_of_mem htail]
          dsimp [δ]
          linarith [hB]
        · have hlt : f n ω < δ := lt_of_not_ge htail
          simp only [g, Set.indicator_of_notMem htail, mul_zero, add_zero]
          exact hlt.le
      _ = δ + B * (μ n (s n)).toReal := by
        rw [integral_add (integrable_const δ) (hind.const_mul B), integral_const_mul]
        rw [integral_indicator₀ (hs n), setIntegral_one_eq_measureReal]
        simp [measureReal_def]
  change |(∫ ω, f n ω ∂(μ n)) - 0| < ε
  rw [sub_zero, abs_of_nonneg (hfNonneg n)]
  exact hIntUpper.trans_lt (hN n hn)

end Causalean.Stat
