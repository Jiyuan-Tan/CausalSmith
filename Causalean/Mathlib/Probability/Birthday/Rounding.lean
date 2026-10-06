module
public import Causalean.Mathlib.Probability.Birthday.Basic

/-!
# Positive integer rounding of real scales

Ceiling and floor choices with a positive minimum allow an arbitrary diverging
real scale to be instantiated as positive alphabet sizes.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- For a [real scale](hyp:x), the [positive ceiling](goal) is [given by the
larger of one and its natural-number ceiling](step:1). -/
noncomputable def positiveCeil (x : ℝ) : ℕ := max 1 (Nat.ceil x)

/-- For a [real scale](hyp:x), the [positive floor](goal) is [given by the
larger of one and its natural-number floor](step:1). -/
noncomputable def positiveFloor (x : ℝ) : ℕ := max 1 (Nat.floor x)

/-- For every [real scale](hyp:x), its [positive ceiling](goal) is positive. -/
theorem positiveCeil_pos (x : ℝ) : 0 < positiveCeil x := by
  simp [positiveCeil]

/-- For every [real scale](hyp:x), its [positive floor](goal) is positive. -/
theorem positiveFloor_pos (x : ℝ) : 0 < positiveFloor x := by
  simp [positiveFloor]

/-- For a [diverging positive scale](hyp:ha) and [positive multiplier](hyp:hc),
the [positive ceiling divided by the original scale](goal) converges to the
multiplier. -/
theorem positiveCeil_mul_div_tendsto
    (a : ℕ → ℝ) {c : ℝ} (ha : Tendsto a atTop atTop) (hc : 0 < c) :
    Tendsto (fun j => (positiveCeil (c * a j) : ℝ) / a j) atTop (nhds c) := by
  have hlarge : ∀ᶠ j in atTop, (1 : ℝ) ≤ c * a j :=
    (ha.const_mul_atTop hc).eventually_ge_atTop 1
  apply (tendsto_nat_ceil_mul_div_atTop hc.le).comp ha |>.congr'
  filter_upwards [hlarge] with j hj
  simp [positiveCeil, (Nat.one_le_ceil_iff).mpr (lt_of_lt_of_le zero_lt_one hj)]

/-- For a [diverging positive scale](hyp:ha) and [positive multiplier](hyp:hc),
the [positive floor divided by the original scale](goal) converges to the
multiplier. -/
theorem positiveFloor_mul_div_tendsto
    (a : ℕ → ℝ) {c : ℝ} (ha : Tendsto a atTop atTop) (hc : 0 < c) :
    Tendsto (fun j => (positiveFloor (c * a j) : ℝ) / a j) atTop (nhds c) := by
  have hlarge : ∀ᶠ j in atTop, (1 : ℝ) ≤ c * a j :=
    (ha.const_mul_atTop hc).eventually_ge_atTop 1
  apply (tendsto_nat_floor_mul_div_atTop hc.le).comp ha |>.congr'
  filter_upwards [hlarge] with j hj
  simp [positiveFloor, (Nat.one_le_floor_iff _).mpr hj]

end Causalean.Mathlib.Probability.Birthday
