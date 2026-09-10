import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Weighted neighborhoods of the Euclidean unit circle

This file fixes a neutral model of the Euclidean plane, its unit circle, the signed radial
coordinate, the two radial sides, and the power weight used by the side-mass estimates.  The plane
is represented by `ℂ`, with its standard Euclidean norm and two-dimensional Lebesgue measure; this
is the measure-preserving identification of `ℝ²` used by Mathlib's polar-coordinate theorem.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal NNReal Real Topology

namespace CausalSmith.Substrate.WeightedCircularTubeSideMassPacking

/-- The Euclidean plane, represented by the complex numbers with their standard Euclidean metric. -/
abbrev Plane := ℂ

/-- The unit circle is the set of planar points whose Euclidean norm is one. -/
def unitCircle : Set Plane := {z | ‖z‖ = 1}

/-- The signed radial coordinate is negative inside the unit circle and positive outside it. -/
def radialOffset (z : Plane) : ℝ := ‖z‖ - 1

/-- The two one-sided regions adjacent to the unit circle. -/
inductive CircleSide where
  | inside
  | outside
  deriving DecidableEq

/-- The inside side contains the circle, while the outside side is the strict exterior. -/
def CircleSide.region : CircleSide → Set Plane
  | .inside => {z | radialOffset z ≤ 0}
  | .outside => {z | 0 < radialOffset z}

/-- The power weight with exponent parameter `κ` is `|‖z‖ - 1|^(κ-2)`. -/
def powerWeight (κ : ℝ) (z : Plane) : ℝ := |radialOffset z| ^ (κ - 2)

/-- A one-sided ball is the intersection of an open Euclidean ball with a chosen radial side. -/
def sideBall (side : CircleSide) (x : Plane) (h : ℝ) : Set Plane :=
  ball x h ∩ side.region

/-- The unit circle is a compact subset of the Euclidean plane. -/
theorem isCompact_unitCircle : IsCompact unitCircle := by
  simpa only [unitCircle, Metric.sphere, Set.mem_ofPred_eq, dist_zero_right] using
    (isCompact_sphere (0 : Plane) 1)

/-- The unit circle is nonempty. -/
theorem unitCircle_nonempty : unitCircle.Nonempty := by
  exact ⟨1, by simp [unitCircle]⟩

/-- Each radial side is Lebesgue measurable. -/
theorem CircleSide.measurableSet_region (side : CircleSide) : MeasurableSet side.region := by
  cases side with
  | inside =>
      exact measurableSet_le (continuous_norm.sub continuous_const).measurable measurable_const
  | outside =>
      exact measurableSet_lt measurable_const (continuous_norm.sub continuous_const).measurable

/-- Every one-sided ball is Lebesgue measurable. -/
theorem measurableSet_sideBall (side : CircleSide) (x : Plane) (h : ℝ) :
    MeasurableSet (sideBall side x h) := by
  exact measurableSet_ball.inter (CircleSide.measurableSet_region side)

/-- For `κ > 2`, the power weight is continuous on the whole plane, including the unit circle. -/
theorem continuous_powerWeight {κ : ℝ} (hκ : 2 < κ) : Continuous (powerWeight κ) := by
  exact (Real.continuous_rpow_const (by linarith)).comp
    ((continuous_norm.sub continuous_const).abs)

/-- For `κ > 2`, the power weight is Lebesgue measurable. -/
theorem measurable_powerWeight {κ : ℝ} (hκ : 2 < κ) : Measurable (powerWeight κ) := by
  exact (continuous_powerWeight hκ).measurable

/-- The power weight is nonnegative for every exponent parameter. -/
theorem powerWeight_nonneg (κ : ℝ) (z : Plane) : 0 ≤ powerWeight κ z := by
  exact Real.rpow_nonneg (abs_nonneg _) _

/-- For `κ > 2`, the power weight vanishes exactly on the unit circle. -/
theorem powerWeight_eq_zero_iff {κ : ℝ} (hκ : 2 < κ) (z : Plane) :
    powerWeight κ z = 0 ↔ z ∈ unitCircle := by
  rw [powerWeight, Real.rpow_eq_zero (abs_nonneg _) (by linarith)]
  simp only [abs_eq_zero, radialOffset, unitCircle, Set.mem_ofPred_eq, sub_eq_zero]

/-- For `κ > 2`, the power weight is integrable on every bounded one-sided ball. -/
theorem integrableOn_powerWeight_sideBall {κ : ℝ} (hκ : 2 < κ)
    (side : CircleSide) (x : Plane) (h : ℝ) :
    IntegrableOn (powerWeight κ) (sideBall side x h) := by
  have hclosed : IntegrableOn (powerWeight κ) (closedBall x h) :=
    (continuous_powerWeight hκ).locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall x h)
  exact Integrable.mono_measure hclosed
    (Measure.restrict_mono
      (inter_subset_left.trans ball_subset_closedBall) le_rfl)

/-- Multiplication by a unit-circle point preserves the radial offset. -/
theorem radialOffset_mul_of_mem_unitCircle {u : Plane} (hu : u ∈ unitCircle) (z : Plane) :
    radialOffset (u * z) = radialOffset z := by
  have hnorm : ‖u‖ = 1 := hu
  simp [radialOffset, hnorm]

/-- Multiplication by a unit-circle point sends the reference point `1` to that point and is a
Euclidean isometry. -/
theorem dist_mul_one_of_mem_unitCircle {u : Plane} (hu : u ∈ unitCircle) (z : Plane) :
    dist (u * z) u = dist z 1 := by
  have hnorm : ‖u‖ = 1 := hu
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖u * z - u‖ = ‖u * (z - 1)‖ := by ring_nf
    _ = ‖z - 1‖ := by rw [Complex.norm_mul, hnorm, one_mul]

end CausalSmith.Substrate.WeightedCircularTubeSideMassPacking
