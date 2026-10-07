module
public import Causalean.Stat.Nonparametric.HistogramRegression.Mesh
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Euclidean unit-cube partition geometry

The covariate domain is the closed unit cube in Euclidean space, with the
Euclidean (L², not sup) metric. Floors at interior grid points choose the cell
to their right, and the coordinate value one is assigned to the final cell by
clamping the index. This keeps exactly `meshCount b ^ d` labels, covers the
boundary, and gives diameter at most `sqrt(d)*b` for positive bandwidths at
most one. Arbitrary probability distributions on the cube are permitted.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

/-- The [closed unit cube](goal) in [dimension](hyp:d) consists of Euclidean
vectors with every coordinate in the unit interval. -/
abbrev Cube (d : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin d) // ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The [cubical cell label](goal) for [a bandwidth and cube point](hyp:b,x)
floors each scaled coordinate and clamps the endpoint to the final bin. -/
def cubeLabel {d : ℕ} (b : ℝ) (x : Cube d) : Fin d → Fin (meshCount b) :=
  fun i => ⟨min ⌊(meshCount b : ℝ) * x.val i⌋₊ (meshCount b - 1), by
    have hn := meshCount_pos b
    have hle := Nat.min_le_right ⌊(meshCount b : ℝ) * x.val i⌋₊ (meshCount b - 1)
    omega⟩

/-- [Cubical labels are measurable](goal) for [every bandwidth](hyp:b). -/
@[fun_prop] theorem measurable_cubeLabel (d : ℕ) (b : ℝ) :
    Measurable (cubeLabel (d := d) b) := by
  apply measurable_pi_iff.mpr
  intro i
  let clamp : ℕ → Fin (meshCount b) := fun k =>
    ⟨min k (meshCount b - 1), by
      have hn := meshCount_pos b
      have hle := Nat.min_le_right k (meshCount b - 1)
      omega⟩
  have hf : Measurable (fun x : Cube d => ⌊(meshCount b : ℝ) * x.val i⌋₊) :=
    (measurable_const.mul
      ((measurable_pi_apply i).comp
        ((WithLp.measurable_ofLp 2 _).comp measurable_subtype_coe))).nat_floor
  exact (measurable_of_countable clamp).comp hf

/-- [Equal cubical labels](hyp:hlabel) imply [coordinate distance at most
the reciprocal number of bins](goal), including the upper cube boundary. -/
theorem same_cell_coordinate_le {d : ℕ} (b : ℝ) (x y : Cube d)
    (hlabel : cubeLabel b x = cubeLabel b y) (i : Fin d) :
    |x.val i - y.val i| ≤ (meshCount b : ℝ)⁻¹ := by
  -- Prove separately for a final-bin index and an interior index. The final
  -- bin uses x_i≤1, whereas interior bins use the floor interval bounds.
  have hn := meshCount_pos b
  have hnR : 0 < (meshCount b : ℝ) := by exact_mod_cast hn
  have hinterval (z : Cube d) :
      ((min ⌊(meshCount b : ℝ) * z.val i⌋₊ (meshCount b - 1) : ℕ) : ℝ) ≤
          (meshCount b : ℝ) * z.val i ∧
      (meshCount b : ℝ) * z.val i ≤
          ((min ⌊(meshCount b : ℝ) * z.val i⌋₊ (meshCount b - 1) : ℕ) : ℝ) + 1 := by
    constructor
    · exact (Nat.cast_le.mpr (Nat.min_le_left _ _)).trans
        (Nat.floor_le (mul_nonneg hnR.le (z.property i).1))
    · by_cases hf : ⌊(meshCount b : ℝ) * z.val i⌋₊ ≤ meshCount b - 1
      · rw [min_eq_left hf]
        exact (Nat.lt_floor_add_one _).le
      · rw [min_eq_right (by omega)]
        have hcast : ((meshCount b - 1 : ℕ) : ℝ) + 1 = (meshCount b : ℝ) := by
          exact_mod_cast (show meshCount b - 1 + 1 = meshCount b by omega)
        rw [hcast]
        exact mul_le_of_le_one_right hnR.le (z.property i).2
  have heq : min ⌊(meshCount b : ℝ) * x.val i⌋₊ (meshCount b - 1) =
      min ⌊(meshCount b : ℝ) * y.val i⌋₊ (meshCount b - 1) :=
    congrArg (fun f => (f i).val) hlabel
  obtain ⟨hxl, hxu⟩ := hinterval x
  obtain ⟨hyl, hyu⟩ := hinterval y
  rw [← heq] at hyl hyu
  apply (abs_le).mpr
  have hinv : (meshCount b : ℝ) * (meshCount b : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hnR.ne'
  constructor <;> nlinarith

/-- [A bandwidth in `(0,1]`](hyp:hb,hb1) and [equal cubical labels](hyp:hlabel)
imply [Euclidean point distance at most square-root dimension times bandwidth](goal). -/
theorem same_cell_diameter_le {d : ℕ} (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (x y : Cube d) (hlabel : cubeLabel b x = cubeLabel b y) :
    dist x y ≤ Real.sqrt (d : ℝ) * b := by
  -- Sum squared coordinate differences in EuclideanSpace.norm_eq, use
  -- same_cell_coordinate_le and mesh_bounds, then compare square roots.
  have hcoord (i : Fin d) : dist (x.val i) (y.val i) ≤ b := by
    rw [Real.dist_eq]
    exact (same_cell_coordinate_le b x y hlabel i).trans (mesh_bounds b hb hb1).2.1
  have hsum : ∑ i : Fin d, dist (x.val i) (y.val i) ^ 2 ≤ (d : ℝ) * b ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, b ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ dist_nonneg (hcoord i) 2
      _ = _ := by simp
  change dist x.val y.val ≤ _
  rw [EuclideanSpace.dist_eq]
  calc
    _ ≤ Real.sqrt ((d : ℝ) * b ^ 2) := Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hb.le]

/-- [Cubical labels have exactly the ceiling mesh count to the dimension](goal). -/
theorem cube_label_card (d : ℕ) (b : ℝ) :
    Fintype.card (Fin d → Fin (meshCount b)) = meshCount b ^ d := by
  simp

/-- [A positive Hölder exponent and nonnegative constant](hyp:hβ,hC),
[a Hölder regression function](hyp:hholder), [a bandwidth in `(0,1]`](hyp:hb,hb1),
and [equal cell labels](hyp:hlabel) give [the oscillation bound `|g x − g y| ≤ C (√d)^β b^β`
for two cube points in the same cell](goal). -/
theorem cube_holder_oscillation {d : ℕ} (g : Cube d → ℝ) (β C b : ℝ)
    (hβ : 0 < β) (hC : 0 ≤ C) (hb : 0 < b) (hb1 : b ≤ 1)
    (hholder : ∀ x y, |g x - g y| ≤ C * (dist x y) ^ β)
    (x y : Cube d) (hlabel : cubeLabel b x = cubeLabel b y) :
    |g x - g y| ≤ C * (Real.sqrt (d : ℝ)) ^ β * b ^ β := by
  calc
    |g x - g y| ≤ C * (dist x y) ^ β := hholder x y
    _ ≤ C * (Real.sqrt (d : ℝ) * b) ^ β :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (same_cell_diameter_le b hb hb1 x y hlabel) hβ.le) hC
    _ = _ := by rw [Real.mul_rpow (Real.sqrt_nonneg _) hb.le]; ring

end

end Causalean.Stat.Nonparametric.HistogramRegression
