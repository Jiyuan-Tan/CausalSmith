module
public import Causalean.Mathlib.Analysis.Quantization.CompandingLimits
public import Causalean.Mathlib.Analysis.Quantization.Lower

/-! The exact high-resolution limit for finite paired weighted scalar L1
quantization on a compact nondegenerate real interval. -/

public section

open MeasureTheory Set Filter

namespace Causalean.Mathlib.Analysis.Quantization

/-- On [a nondegenerate interval](hyp:a,b,hab), [a nonempty finite
weight family](hyp:S,hS) with [jointly continuous](hyp:β,hcont) and
[strictly positive](hyp:hpos) losses satisfies the high-resolution limit: [the number of
cells k times the optimal paired L1 cost with k cells converges, as k grows, to one quarter
of the squared integral over the interval of the square root of the diagonal weight](goal). -/
theorem optimal_scaled_cost_tendsto (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    Tendsto (fun k : ℕ => (k : ℝ) * optimalCost a b S k β)
      atTop (nhds ((1 / 4 : ℝ) *
        (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2)) := by
  -- Squeeze optimalCost between optimal_lower_eventually and the feasible
  -- companding cost. The latter has the exact limit by companding_scaled_cost_tendsto.
  let A : ℝ := (1 / 4 : ℝ) *
    (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2
  have hcomp := companding_scaled_cost_tendsto a b hab S hS β hcont hpos
  apply tendsto_order.2
  constructor
  · intro c hc
    have hε : 0 < (A - c) / 2 := by
      exact div_pos (sub_pos.mpr hc) (by norm_num)
    obtain ⟨K, hK⟩ :=
      optimal_lower_eventually a b hab S hS β hcont hpos ((A - c) / 2) hε
    apply Filter.eventually_atTop.2
    refine ⟨max K 1, ?_⟩
    intro k hk
    have hkK : K ≤ k := (le_max_left K 1).trans hk
    have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right K 1).trans hk)
    have hlow := hK k hkK hkpos
    dsimp [A] at hε hlow
    linarith
  · intro c hc
    have hevent := (tendsto_order.1 hcomp).2 c hc
    have hkEventually : ∀ᶠ k : ℕ in atTop, 0 < k := by
      apply Filter.eventually_atTop.2
      exact ⟨1, fun k hk => lt_of_lt_of_le Nat.zero_lt_one hk⟩
    filter_upwards [hevent, hkEventually] with k hlt hk
    obtain ⟨hpart, hmid⟩ :=
      companding_feasible a b hab S k hS hk β hcont hpos
    have hβ : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
        0 ≤ β s x y := by
      intro s x y hx hy
      exact (hpos s x y hx hy).le
    have hle := optimalCost_le_feasible a b S k β
      (compandingCell a b S k β) (compandingMidpoint a b S k β)
      hpart hmid hβ
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg k)) hlt

end Causalean.Mathlib.Analysis.Quantization
