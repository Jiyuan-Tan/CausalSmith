module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic

/-!
# Geometry of the affine map between fixed cubes

The coordinatewise map `x ↦ 2x-1` identifies the unit cube with the normalized
cube and doubles distances in the finite-product norm.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The coordinatewise affine map sends `[0,1]^d` to `[-1,1]^d`. -/
def cubeAffine {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => 2 * x i - 1

/-- The unit cube consists of points whose coordinates lie in `[0,1]`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

/-- The affine image of each point of the unit cube lies in the normalized cube. -/
theorem cubeAffine_mem_cube {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ unitCube d) : cubeAffine x ∈ cube d := by
  intro i
  have hi : x i ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_univ_pi.mp hx) i
  change -1 ≤ 2 * x i - 1 ∧ 2 * x i - 1 ≤ 1
  constructor <;> linarith [hi.1, hi.2]

/-- In [any dimension](hyp:d), [the set of points that the affine map x ↦ 2x − 1 (applied to each
coordinate) sends into the normalized cube is exactly the unit cube](goal). -/
theorem cubeAffine_preimage_cube (d : ℕ) :
    cubeAffine ⁻¹' cube d = unitCube d := by
  ext x
  constructor
  · intro hx
    apply Set.mem_univ_pi.mpr
    intro i
    have hi : cubeAffine x i ∈ Set.Icc (-1 : ℝ) 1 := hx i
    change -1 ≤ 2 * x i - 1 ∧ 2 * x i - 1 ≤ 1 at hi
    constructor <;> linarith
  · exact cubeAffine_mem_cube

/-- Affine transport doubles distances in the ambient finite-product norm. -/
theorem cubeAffine_norm_sub {d : ℕ} (x y : Fin d → ℝ) :
    ‖cubeAffine x - cubeAffine y‖ = 2 * ‖x - y‖ := by
  have h : cubeAffine x - cubeAffine y = (2 : ℝ) • (x - y) := by
    ext i
    simp [cubeAffine, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, norm_smul]
  norm_num

/-- The coordinatewise affine map is smooth to every finite order. -/
theorem cubeAffine_contDiff {d m : ℕ} :
    ContDiff ℝ m (cubeAffine : (Fin d → ℝ) → (Fin d → ℝ)) := by
  unfold cubeAffine
  fun_prop

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
