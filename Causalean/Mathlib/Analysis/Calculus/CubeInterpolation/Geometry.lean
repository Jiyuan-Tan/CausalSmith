module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Multiindex
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Convex.Topology

/-!
# Geometry of centered Euclidean cubes

Arbitrary centers and side lengths are supported. Positive-side cubes have
unique within derivatives and are closures of their interiors. The local
Euclidean radius is bounded by sqrt(d) times half the side length. These
geometric facts are independent of the Taylor and Legendre proof chains.
-/

@[expose] public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [closed coordinate cube](goal) with [centre a](hyp:a) and [side length h](hyp:h) is [the
set of points each of whose coordinates is within h / 2 of the matching coordinate of a](step:1).
-/
def centeredCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (h : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, |x i - a i| ≤ h / 2}

/-- For [any centre](hyp:a) and [any side length](hyp:h), [the centred coordinate cube is
convex](goal). -/
theorem centeredCube_convex {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (h : ℝ) :
    Convex ℝ (centeredCube a h) := by
  intro x hx y hy u v hu hv huv i
  have hxi : x i ∈ Set.Icc (a i - h / 2) (a i + h / 2) := by
    have hi := (abs_le.mp (hx i))
    constructor <;> linarith
  have hyi : y i ∈ Set.Icc (a i - h / 2) (a i + h / 2) := by
    have hi := (abs_le.mp (hy i))
    constructor <;> linarith
  have hi := (convex_Icc (a i - h / 2) (a i + h / 2)) hxi hyi hu hv huv
  simp only [Set.mem_Icc, smul_eq_mul] at hi
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
  apply abs_le.mpr
  constructor <;> linarith

/-- For [a centre](hyp:a) and [a side length](hyp:h) that is [positive](hyp:hh), [the centre lies
in the interior of its cube](goal). -/
theorem center_mem_interior_cube {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (h : ℝ) (hh : 0 < h) : a ∈ interior (centeredCube a h) := by
  -- Use the finite intersection of open coordinate intervals, including d=0.
  let U : Fin d → Set (EuclideanSpace ℝ (Fin d)) := fun i =>
    (fun x => x i) ⁻¹' Set.Ioo (a i - h / 2) (a i + h / 2)
  have hU : IsOpen (⋂ i, U i) :=
    isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)
  have hsub : (⋂ i, U i) ⊆ centeredCube a h := by
    intro x hx i
    have hi : a i - h / 2 < x i ∧ x i < a i + h / 2 := Set.mem_iInter.mp hx i
    apply abs_le.mpr
    constructor <;> linarith
  apply interior_maximal hsub hU
  apply Set.mem_iInter.mpr
  intro i
  change a i - h / 2 < a i ∧ a i < a i + h / 2
  constructor <;> linarith

/-- For [a centre](hyp:a) and [a side length](hyp:h) that is [positive](hyp:hh), [derivatives taken
within the cube are uniquely determined at every point of the cube](goal). -/
theorem uniqueDiffOn_centeredCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (h : ℝ) (hh : 0 < h) : UniqueDiffOn ℝ (centeredCube a h) := by
  -- Apply uniqueDiffOn_convex using the preceding two geometry lemmas.
  exact uniqueDiffOn_convex (centeredCube_convex a h)
    ⟨a, center_mem_interior_cube a h hh⟩

/-- For [a centre](hyp:a) and [a side length](hyp:h) that is [positive](hyp:hh), [every point of
the cube lies in the closure of the cube's interior](goal). -/
theorem centeredCube_subset_closure_interior {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d)) (h : ℝ) (hh : 0 < h) :
    centeredCube a h ⊆ closure (interior (centeredCube a h)) := by
  -- Contract a boundary point toward the center, or use convex topology.
  rw [(centeredCube_convex a h).closure_interior_eq_closure_of_nonempty_interior
    ⟨a, center_mem_interior_cube a h hh⟩]
  exact subset_closure

/-- For [a centre a](hyp:a) and [a side length h](hyp:h) that is [nonnegative](hyp:hh), [every
point of the cube](hyp:x,hx) [is at Euclidean distance at most the square root of the dimension
times h / 2 from the centre](goal). -/
theorem centeredCube_norm_sub_le {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (h : ℝ) (hh : 0 ≤ h) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ centeredCube a h) : ‖x - a‖ ≤ Real.sqrt d * (h / 2) := by
  -- EuclideanSpace.norm_eq bounds the square sum coordinate by coordinate.
  have hhalf : 0 ≤ h / 2 := by positivity
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖(x - a) i‖ ^ 2) ≤ Real.sqrt (∑ _ : Fin d, (h / 2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      rw [PiLp.sub_apply, Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hhalf).mpr (hx i)
    _ = Real.sqrt d * (h / 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hhalf]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

