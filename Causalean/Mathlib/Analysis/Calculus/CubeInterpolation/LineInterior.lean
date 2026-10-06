module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Directional
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Segment

/-!
# Line calculus before a cube segment reaches its boundary

On every compact initial subsegment, the restriction of a `C^m` function is
`C^m` and its top line derivative inherits the coordinate Hölder modulus.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- A line from an interior cube point toward a closed-cube point is `C^m` on
each closed initial subsegment ending strictly before the final endpoint. -/
theorem segment_line_contDiffOn_before_endpoint {d m : ℕ}
    {u : (Fin d → ℝ) → ℝ} (hu : ContDiffOn ℝ m u (cube d))
    {x y : Fin d → ℝ} (hx : x ∈ openCube d) (hy : y ∈ cube d)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContDiffOn ℝ m (fun r : ℝ => u (x + r • (y - x))) (Set.Icc 0 t) := by
  -- Compose `hu` with the affine line and use `segment_mem_openCube` on
  -- `Icc 0 t`; the line is smooth in an open neighborhood of every point.
  have hline : ContDiff ℝ m (fun r : ℝ => x + r • (y - x)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hmaps : Set.MapsTo (fun r : ℝ => x + r • (y - x))
      (Set.Icc 0 t) (cube d) := by
    intro r hr
    have hro : r ∈ Set.Ico (0 : ℝ) 1 := ⟨hr.1, lt_of_le_of_lt hr.2 ht1⟩
    have hri := segment_mem_openCube hx hy hro
    intro i
    exact ⟨le_of_lt (hri i (Set.mem_univ i)).1,
      le_of_lt (hri i (Set.mem_univ i)).2⟩
  exact hu.comp hline.contDiffOn hmaps

/-- For [a function that is m times continuously differentiable on the closed normalized
cube](hyp:hu) and satisfies [the top-order Hölder condition with exponent s and constant
L](hyp:hholder), where [s is positive](hyp:hs) and [L is nonnegative](hyp:hL), take [a starting
point x in the open cube](hyp:hx), [an end point y in the closed cube](hyp:hy), and [a time t that
is nonnegative and strictly less than one](hyp:ht0,ht1). Then for [any two times r and w between 0
and t](hyp:hr,hw), [the m-th derivative of the function restricted to the segment from x to y
changes between those times by at most (d + 1)^m times L times the segment length to the power m +
s times the time difference to the power s](goal). -/
theorem segment_line_topHolder_before_endpoint {d m : ℕ} {s L : ℝ}
    {u : (Fin d → ℝ) → ℝ} (hu : ContDiffOn ℝ m u (cube d))
    (hs : 0 < s) (hL : 0 ≤ L) (hholder : TopHolder d m s L u)
    {x y : Fin d → ℝ} (hx : x ∈ openCube d) (hy : y ∈ cube d)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {r w : ℝ} (hr : r ∈ Set.Icc 0 t) (hw : w ∈ Set.Icc 0 t) :
    |iteratedDeriv m (fun q : ℝ => u (x + q • (y - x))) r -
      iteratedDeriv m (fun q : ℝ => u (x + q • (y - x))) w| ≤
      ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) * |r - w| ^ s := by
  -- Apply `segment_iteratedDeriv_eq_diagonal` at `r,w`, then
  -- `topHolder_diagonal_derivative`; use
  -- `‖r • (y-x) - w • (y-x)‖ = |r-w| * ‖y-x‖`.
  have hrr : r ∈ Set.Ico (0 : ℝ) 1 := ⟨hr.1, lt_of_le_of_lt hr.2 ht1⟩
  have hww : w ∈ Set.Ico (0 : ℝ) 1 := ⟨hw.1, lt_of_le_of_lt hw.2 ht1⟩
  rw [segment_iteratedDeriv_eq_diagonal hu hx hy hrr m le_rfl,
    segment_iteratedDeriv_eq_diagonal hu hx hy hww m le_rfl]
  have hrc : x + r • (y - x) ∈ cube d := by
    have h := segment_mem_openCube hx hy hrr
    intro i
    exact ⟨le_of_lt (h i (Set.mem_univ i)).1, le_of_lt (h i (Set.mem_univ i)).2⟩
  have hwc : x + w • (y - x) ∈ cube d := by
    have h := segment_mem_openCube hx hy hww
    intro i
    exact ⟨le_of_lt (h i (Set.mem_univ i)).1, le_of_lt (h i (Set.mem_univ i)).2⟩
  have hbound := topHolder_diagonal_derivative u hs hL hholder
    (x + r • (y - x)) (x + w • (y - x)) (y - x) hrc hwc
  have hdiff : (x + r • (y - x)) - (x + w • (y - x)) =
      (r - w) • (y - x) := by
    rw [sub_smul]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs] at hbound
  calc
    _ ≤ ((d : ℝ) + 1) ^ m * L *
        (|r - w| * ‖y - x‖) ^ s * ‖y - x‖ ^ m := hbound
    _ = ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) *
        |r - w| ^ s := by
      rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _),
        Real.rpow_add_of_nonneg (norm_nonneg _) (Nat.cast_nonneg _) (le_of_lt hs),
        Real.rpow_natCast]
      ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
