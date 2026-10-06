module
public import Causalean.Mathlib.Analysis.Quantization.Core

/-! Pointwise geometry used to control arbitrary measurable cells in the
universal lower bound. No cell is assumed to be connected. -/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- If a source point lies at least `δ` from one reproduction point and all
weights there are at least `c`, its paired distortion is at least `c*δ`. -/
theorem far_point_cost_lower (S : ℕ) (β : Fin S → ℝ → ℝ → ℝ)
    (z : Fin S → ℝ) (x c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hβ : ∀ s, c ≤ β s x (z s))
    (hfar : ∃ s, δ ≤ |x - z s|) :
    c * δ ≤ ∑ s : Fin S, β s x (z s) * |x - z s| := by
  obtain ⟨s, hs⟩ := hfar
  have hsingle : c * δ ≤ β s x (z s) * |x - z s| :=
    mul_le_mul (hβ s) hs hδ (hc.trans (hβ s))
  have hnonneg : ∀ t : Fin S, 0 ≤ β t x (z t) * |x - z t| := by
    intro t
    exact mul_nonneg (hc.trans (hβ t)) (abs_nonneg _)
  exact hsingle.trans (Finset.single_le_sum
    (fun t _ => hnonneg t) (Finset.mem_univ s))

/-- A [nonempty index family](hyp:S,hS) with [reproduction points](hyp:z)
and [two source points each close to every reproduction](hyp:x,y,δ,hx,hy)
has [source-point distance at most twice the common radius](goal). -/
theorem good_cell_diameter (S : ℕ) (hS : 0 < S) (z : Fin S → ℝ)
    (x y δ : ℝ) (hx : ∀ s, |x - z s| ≤ δ)
    (hy : ∀ s, |y - z s| ≤ δ) :
    |x - y| ≤ 2 * δ := by
  let s : Fin S := ⟨0, hS⟩
  calc
    |x - y| = |(x - z s) + (z s - y)| := by ring
    _ ≤ |x - z s| + |z s - y| := abs_add_le _ _
    _ ≤ δ + δ := add_le_add (hx s) (by simpa [abs_sub_comm] using hy s)
    _ = 2 * δ := by ring

end Causalean.Mathlib.Analysis.Quantization
