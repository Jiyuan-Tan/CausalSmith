module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarGeometry
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# A crossing point on a reflected cube face

A segment from the exterior slab to the original cube crosses their shared
face. The crossing point gives a common comparison point for Hölder estimates.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [x lies in the closed exterior slab of the left collar in coordinate
i](hyp:hx) and [y lies in the normalized cube](hyp:hy), then [some point z of the
segment from x to y lies both in the slab and in the cube (hence on the left
face), and both ‖x − z‖ and ‖z − y‖ are at most ‖x − y‖](goal). -/
theorem exists_leftFaceReflection_crossing_point
    (d m : ℕ) (i : Fin d) (x y : Fin d → ℝ)
    (hx : x ∈ leftClosedExteriorCollar d m i) (hy : y ∈ cube d) :
    ∃ z : Fin d → ℝ,
      z ∈ segment ℝ x y ∧
      z ∈ leftClosedExteriorCollar d m i ∧ z ∈ cube d ∧
      ‖x - z‖ ≤ ‖x - y‖ ∧ ‖z - y‖ ≤ ‖x - y‖ := by
  have hxi : x i ≤ -1 := hx.2
  have hyi : -1 ≤ y i := (hy i).1
  have hcont : ContinuousOn
      (fun t : ℝ => (AffineMap.lineMap x y t) i) (Set.Icc 0 1) := by
    fun_prop
  have hface : (-1 : ℝ) ∈ Set.Icc
      ((AffineMap.lineMap x y (0 : ℝ)) i)
      ((AffineMap.lineMap x y (1 : ℝ)) i) := by
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      Set.mem_Icc] using And.intro hxi hyi
  obtain ⟨t, ht, hit⟩ :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont hface)
  let z : Fin d → ℝ := AffineMap.lineMap x y t
  have hzseg : z ∈ segment ℝ x y := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hcoord (j : Fin d) : z j ∈ segment ℝ (x j) (y j) := by
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    simp only [z, AffineMap.lineMap_apply_module, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  have hzi : z i = -1 := hit
  have hcube : z ∈ cube d := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [hzi]
    · have hxj : x j ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [leftClosedExteriorCollar, leftCubeCollar, hji] using hx.1 j
      exact ((convex_Icc (-1 : ℝ) 1).segment_subset hxj (hy j)) (hcoord j)
  have hcollar : z ∈ leftClosedExteriorCollar d m i := by
    refine ⟨?_, hzi.le⟩
    intro j
    by_cases hji : j = i
    · subst j
      simp only [↓reduceIte, Set.mem_Icc]
      have hnonneg : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
      constructor <;> linarith [hzi, (hcube i).2]
    · simpa [leftCubeCollar, hji] using hcube j
  refine ⟨z, hzseg, hcollar, hcube, ?_, ?_⟩
  · simpa only [norm_sub_rev] using
      (norm_sub_le_of_mem_segment hzseg)
  · have hrev : z ∈ segment ℝ y x := by
      simpa only [segment_symm] using hzseg
    simpa only [norm_sub_rev] using
      (norm_sub_le_of_mem_segment hrev)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
