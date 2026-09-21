/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.StochasticOrderEnvelope

/-!
# High-Probability Transfer Rules

This module transfers stochastic asymptotic bounds between random sequences
that agree on events whose probabilities tend to one.
-/

public section

namespace Causalean.Stat

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Given [events](hyp:G), [failure-probability bounds](hyp:Δ) that
[vanish](hyp:hΔ), [complement measures controlled by those bounds](hyp:hfail),
[two random sequences that agree on those events](hyp:h_eq), and [a
stochastic little-o bound for the second sequence](hyp:hY), [the first
sequence obeys the same stochastic little-o bound](goal). -/
theorem isLittleOp_of_isLittleOp_on_highProbEvent
    {Xn Yn : ℕ → Ω → ℝ} {rn : ℕ → ℝ}
    (G : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, μ (G n)ᶜ ≤ Δ n)
    (h_eq : ∀ n ω, ω ∈ G n → Xn n ω = Yn n ω)
    (hY : IsLittleOp Yn rn μ) :
    IsLittleOp Xn rn μ := by
  apply IsLittleOp.of_eq_on_asymptotic ?_ hY
  rw [ENNReal.tendsto_nhds_zero] at hΔ ⊢
  intro ε hε
  exact (hΔ ε hε).mono fun n hn => by
    have hsubset : {ω | Xn n ω ≠ Yn n ω} ⊆ (G n)ᶜ := by
      intro ω hne hmem
      exact hne (h_eq n ω hmem)
    exact (measure_mono hsubset).trans ((hfail n).trans hn)

end Causalean.Stat
