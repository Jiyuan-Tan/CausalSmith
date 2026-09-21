/-! ## Coordinatewise retraction onto a finite unit cube -/

open Set Function MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable (V : Type*) [DecidableEq V] [Fintype V]

/-- A [finite coordinate type](hyp:V) and [a real assignment](hyp:v) determine [the
coordinatewise clamp to the closed unit cube](goal), [by clamping each coordinate between zero
and one](step:1). -/
def clampCube (v : V → ℝ) : V → ℝ :=
  fun i ↦ max 0 (min 1 (v i))

/-- The [coordinatewise clamp for a finite coordinate type](hyp:V) [is measurable](goal). -/
@[fun_prop]
theorem measurable_clampCube : Measurable (clampCube V) := by
  -- Prove each coordinate measurable from `measurable_pi_iff`, using measurability of `min` and
  -- `max` on the real line.
  refine measurable_pi_iff.mpr fun i ↦ ?_
  exact measurable_const.max (measurable_const.min (measurable_pi_apply i))

/-- Every [real assignment](hyp:v) over [a finite coordinate type](hyp:V) is [sent by the
coordinatewise clamp into the finite unit cube](goal). -/
theorem clampCube_mem (v : V → ℝ) :
    clampCube V v ∈ Causalean.Graph.FiniteDensity.unitCube V := by
  -- Unfold membership in `Set.pi`; the scalar expression is between zero and one by the linear
  -- order laws for `min` and `max`.
  rw [Causalean.Graph.FiniteDensity.unitCube]
  intro i _
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

/-- A [finite coordinate type](hyp:V) and [a point in its unit cube](hyp:hv) are such that [the
coordinatewise clamp fixes that point](goal). -/
@[simp]
theorem clampCube_eq_self {v : V → ℝ}
    (hv : v ∈ Causalean.Graph.FiniteDensity.unitCube V) :
    clampCube V v = v := by
  -- Extensionality reduces this to `max_eq_right` and `min_eq_right`, using the two coordinate
  -- inequalities extracted from `hv`.
  ext i
  have hi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  simp [clampCube, min_eq_right hi.2, max_eq_right hi.1]

/-- [An assignment](hyp:v), [a coordinate](hyp:i), and [a replacement value](hyp:x) satisfy
[the update-and-clamp identity](goal). -/
theorem clampCube_update (v : V → ℝ) (i : V) (x : ℝ) :
    clampCube V (Function.update v i x) =
      Function.update (clampCube V v) i (max 0 (min 1 x)) := by
  -- Use function extensionality and split on whether the inspected coordinate is `i`.
  ext j
  by_cases h : j = i
  · simp [clampCube, h]
  · simp [clampCube, h]

/-- [An assignment](hyp:v), [a coordinate](hyp:i), and [a replacement value in the unit
interval](hyp:hx) satisfy [the update identity in which only the unchanged context is
clamped](goal). -/
theorem clampCube_update_of_mem (v : V → ℝ) (i : V) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clampCube V (Function.update v i x) =
      Function.update (clampCube V v) i x := by
  -- Rewrite with `clampCube_update` and simplify the scalar clamp from `hx`.
  rw [clampCube_update]
  simp [min_eq_right hx.2, max_eq_right hx.1]

end Causalean.Graph.FiniteDensity

/-! ## Unit-cube reference measure -/

