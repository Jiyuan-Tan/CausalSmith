import CausalSmith.Substrate.AffineSignCellClosure.Basic

/-!
# Segment approximation and closure of affine sign cells

Given one point satisfying all strict constraints, this module moves every weakly feasible
point a positive distance toward it. The resulting segment points are strictly feasible and
converge back to the original weak point, identifying the closure of the strict cell.
-/

open Set Filter
open scoped Topology

namespace CausalSmith.Substrate.AffineSignCellClosure

/-- The affine segment point with weight `ε` on the distinguished strict point. -/
def segmentPoint {n : ℕ} (x x₀ : Fin n → ℝ) (ε : ℝ) : Fin n → ℝ :=
  (1 - ε) • x + ε • x₀

/-- Segment points converge to the first endpoint as their weight tends to zero. -/
theorem tendsto_segmentPoint_zero {n : ℕ} (x x₀ : Fin n → ℝ) :
    Tendsto (segmentPoint x x₀) (𝓝 0) (𝓝 x) := by
  have h : Continuous (segmentPoint x x₀) := by
    unfold segmentPoint
    fun_prop
  have h0 : Tendsto (segmentPoint x x₀) (𝓝 0)
      (𝓝 (segmentPoint x x₀ 0)) := h.continuousAt
  simpa [segmentPoint] using h0

/-- Moving a weakly feasible point a positive weight toward a strictly feasible point
produces a strictly feasible point. -/
/- Proof strategy: unfold membership constraint-by-constraint, rewrite with
`AffineFn.eval_affineCombination`, and split on the mark. Weak constraints use convexity of
`≤ 0`; strict constraints use the positive coefficient of the strict endpoint. -/
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

/-- Every weakly feasible point is the limit of a sequence of strictly feasible segment
points formed with a fixed strictly feasible point. -/
/- Proof strategy: take weights `(k + 1 : ℝ)⁻¹`; they lie in `(0,1]`, and their segment
points converge by `tendsto_natCast_atTop_atTop`, `tendsto_inv_atTop_zero`, and
`tendsto_segmentPoint_zero`. -/
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
  · exact (tendsto_segmentPoint_zero x x₀).comp
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- If the strict cell is nonempty, every point of the weak relaxation lies in the closure
of the strict cell. -/
theorem weakCell_subset_closure_strictCell {n : ℕ} {Γ : AffineSystem n}
    (hΓ : (strictCell Γ).Nonempty) :
    weakCell Γ ⊆ closure (strictCell Γ) := by
  intro x hx
  rcases hΓ with ⟨x₀, hx₀⟩
  rw [mem_closure_iff_seq_limit]
  exact exists_strictCell_sequence_tendsto hx hx₀

/-- The closure of a nonempty strict affine sign cell is exactly its weak relaxation. -/
theorem closure_strictCell_eq_weakCell {n : ℕ} {Γ : AffineSystem n}
    (hΓ : (strictCell Γ).Nonempty) :
    closure (strictCell Γ) = weakCell Γ := by
  apply Set.Subset.antisymm
  · exact closure_minimal (strictCell_subset_weakCell Γ) (isClosed_weakCell Γ)
  · exact weakCell_subset_closure_strictCell hΓ

end CausalSmith.Substrate.AffineSignCellClosure
