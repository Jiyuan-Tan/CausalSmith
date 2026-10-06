module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.CenteredNumeratorMean

/-! Exact reciprocal-polynomial certificates in the first two degree regimes. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

/-- The degree-two reciprocal polynomial is the constant polynomial one. -/
lemma GK_two (x : ℝ) : GK 2 x = 1 := by
  norm_num [GK, gCoeff, Finset.sum_range_succ]

/-- The degree-three reciprocal polynomial has the displayed affine form. -/
lemma GK_three (x : ℝ) : GK 3 x = 8 / 3 - 16 / 9 * x := by
  norm_num [GK, gCoeff, Finset.sum_range_succ]
  ring

/-- Exact degree-two residual certificate, the first case of equation (21). -/
lemma GK_two_residual (x : ℝ) : 1 - x * GK 2 x = 1 - x := by
  rw [GK_two]
  ring

/-- Exact degree-three residual certificate, the second case of equation (21). -/
lemma GK_three_residual (x : ℝ) :
    1 - x * GK 3 x = (1 - 4 * x / 3) ^ 2 := by
  rw [GK_three]
  ring

/-- Equation (22) for degree two.  Positivity of `x` is explicit because Lean
uses `x⁻¹ = 0` at `x = 0`, whereas the paper uses the extended-real value. -/
-- keep: degree-two endpoint required to audit the small-degree case of equation (22)
lemma GK_two_residual_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x * GK 2 x ∧
      1 - x * GK 2 x ≤ min 1 (1 / ((2 : ℝ) ^ 2 * x)) := by
  rw [GK_two_residual]
  constructor
  · linarith
  · rw [le_min_iff]
    constructor
    · linarith
    · apply (le_div_iff₀ (show 0 < (2 : ℝ) ^ 2 * x by positivity)).2
      nlinarith [sq_nonneg (2 * x - 1)]

/-- Equation (22) for degree three. -/
-- keep: degree-three endpoint required to audit the small-degree case of equation (22)
lemma GK_three_residual_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x * GK 3 x ∧
      1 - x * GK 3 x ≤ min 1 (1 / ((3 : ℝ) ^ 2 * x)) := by
  rw [GK_three_residual]
  constructor
  · positivity
  · rw [le_min_iff]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg (4 * x - 1))]
    · apply (le_div_iff₀ (show 0 < (3 : ℝ) ^ 2 * x by positivity)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg (4 * x - 1))]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
