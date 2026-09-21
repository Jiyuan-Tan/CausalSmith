/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.AffineSignCellClosure.Basic

/-! # Segment approximation and closure of affine sign cells

Given one point satisfying every strict comparison, this module approximates every weakly
feasible point by strictly feasible segment points and identifies the weak relaxation as the
closure of the strict cell.
-/

open Set Filter
open scoped Topology

namespace Causalean.Mathlib.Optimization.AffineSignCellClosure

/-- Given [a weak endpoint](hyp:x), [a distinguished strict endpoint](hyp:x₀), and [a real
weight](hyp:ε), the [segment point](goal) is given by [placing weight `ε` on the strict endpoint](step:1).

The affine segment point with weight on the distinguished strict endpoint. -/
def segmentPoint {n : ℕ} (x x₀ : Fin n → ℝ) (ε : ℝ) : Fin n → ℝ :=
  (1 - ε) • x + ε • x₀

/-- Given [a weak endpoint](hyp:x) and [a distinguished strict endpoint](hyp:x₀), [their
segment points converge to the weak endpoint as the strict-endpoint weight tends to zero](goal). -/
theorem tendsto_segmentPoint_zero {n : ℕ} (x x₀ : Fin n → ℝ) :
    Tendsto (segmentPoint x x₀) (𝓝 0) (𝓝 x) := by
  have h : Continuous (segmentPoint x x₀) := by
    unfold segmentPoint
    fun_prop
  have h0 : Tendsto (segmentPoint x x₀) (𝓝 0) (𝓝 (segmentPoint x x₀ 0)) := h.continuousAt
  simpa [segmentPoint] using h0

/-- Given [a weakly feasible point](hyp:hx), [a strictly feasible point](hyp:hx₀), [a positive
segment weight](hyp:hεpos), and [a weight at most one](hyp:hεone), [the corresponding segment
point is strictly feasible](goal). -/
theorem segmentPoint_mem_strictCell {n : ℕ} {Γ : AffineSystem n}
    {x x₀ : Fin n → ℝ} (hx : x ∈ weakCell Γ) (hx₀ : x₀ ∈ strictCell Γ)
    {ε : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1) :
    segmentPoint x x₀ ε ∈ strictCell Γ := by
  intro c hc
  have hxc := hx c hc
  have hx₀c := hx₀ c hc
  unfold Constraint.weakHolds at hxc
  unfold segmentPoint
  cases hkind : c.kind with
  | weak =>
      simp only [Constraint.strictHolds, hkind] at hx₀c ⊢
      rw [AffineFn.eval_affineCombination]
      exact add_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hεone) hxc)
        (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hεpos) hx₀c)
  | strict =>
      simp only [Constraint.strictHolds, hkind] at hx₀c ⊢
      rw [AffineFn.eval_affineCombination]
      exact add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hεone) hxc)
        (mul_neg_of_pos_of_neg hεpos hx₀c)

/-- Given [a weakly feasible point](hyp:hx) and [a strictly feasible point](hyp:hx₀), [there
is a sequence of strictly feasible points converging to the weakly feasible point](goal). -/
theorem exists_strictCell_sequence_tendsto {n : ℕ} {Γ : AffineSystem n}
    {x x₀ : Fin n → ℝ} (hx : x ∈ weakCell Γ) (hx₀ : x₀ ∈ strictCell Γ) :
    ∃ u : ℕ → (Fin n → ℝ),
      (∀ k, u k ∈ strictCell Γ) ∧ Tendsto u atTop (𝓝 x) := by
  refine ⟨fun k => segmentPoint x x₀ (1 / ((k : ℝ) + 1)), ?_, ?_⟩
  · intro k
    apply segmentPoint_mem_strictCell hx hx₀
    · positivity
    · apply (div_le_one (by positivity)).2
      norm_num
  · exact (tendsto_segmentPoint_zero x x₀).comp tendsto_one_div_add_atTop_nhds_zero_nat

/-- Given [a nonempty strict cell](hyp:hΓ), [every point of the weak relaxation belongs to
the closure of the strict cell](goal). -/
theorem weakCell_subset_closure_strictCell {n : ℕ} {Γ : AffineSystem n}
    (hΓ : (strictCell Γ).Nonempty) : weakCell Γ ⊆ closure (strictCell Γ) := by
  intro x hx
  rcases hΓ with ⟨x₀, hx₀⟩
  rw [mem_closure_iff_seq_limit]
  exact exists_strictCell_sequence_tendsto hx hx₀

/-- Given [a nonempty strict cell](hyp:hΓ), [the closure of that strict cell equals its weak
relaxation](goal). -/
theorem closure_strictCell_eq_weakCell {n : ℕ} {Γ : AffineSystem n}
    (hΓ : (strictCell Γ).Nonempty) : closure (strictCell Γ) = weakCell Γ := by
  apply Set.Subset.antisymm
  · exact closure_minimal (strictCell_subset_weakCell Γ) (isClosed_weakCell Γ)
  · exact weakCell_subset_closure_strictCell hΓ

end Causalean.Mathlib.Optimization.AffineSignCellClosure
