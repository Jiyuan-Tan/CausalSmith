module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Segment derivatives of Euclidean within-cube jets

The segment from an interior point to a closed cube point remains interior
before its endpoint. Its ordinary iterated derivatives agree with diagonal
within-cube jets. This analytic transport imports no Taylor or Hölder layer.
-/

public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a cube with centre b and side length H](hyp:b,H), [a point a](hyp:a) [in the cube's
interior](hyp:ha), [a point y](hyp:y) [in the cube](hyp:hy), and [a time r](hyp:r) [in the
half-open unit interval](hyp:hr), [the point a + r (y − a) of the segment from a to y lies in the
cube's interior](goal). -/
theorem segment_mem_interior_centeredCube {d : ℕ}
    (b a y : EuclideanSpace ℝ (Fin d)) (H : ℝ)
    (ha : a ∈ interior (centeredCube b H)) (hy : y ∈ centeredCube b H)
    (r : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    a + r • (y - a) ∈ interior (centeredCube b H) := by
  have h := (centeredCube_convex b H).combo_interior_self_mem_interior
    ha hy (show 0 < 1 - r by linarith [hr.2]) hr.1 (by ring : (1 - r) + r = 1)
  convert h using 1
  module

/-- For [a cube with centre b and side length H](hyp:b,H) that is [positive](hyp:hH), [a function
u](hyp:u) that is [m times continuously differentiable on the cube](hyp:hu), [a point a](hyp:a) [in
the cube's interior](hyp:ha), [a point y](hyp:y) [in the cube](hyp:hy), [a time r](hyp:r) [in the
half-open unit interval](hyp:hr), and [an order k](hyp:k) [at most m](hyp:hk), [the k-th derivative
at time r of the function restricted to the segment from a to y equals the order-k derivative
within the cube at the point a + r (y − a), taken k times in the direction y − a](goal). -/
theorem segment_iteratedDeriv_eq_within_diagonal {d m : ℕ}
    (b a y : EuclideanSpace ℝ (Fin d)) (H : ℝ) (hH : 0 < H)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ContDiffOn ℝ m u (centeredCube b H))
    (ha : a ∈ interior (centeredCube b H)) (hy : y ∈ centeredCube b H)
    (r : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) (hk : k ≤ m) :
    iteratedDeriv k (fun t : ℝ => u (a + t • (y - a))) r =
      iteratedFDerivWithin ℝ k u (centeredCube b H)
        (a + r • (y - a)) (fun _ => y - a) := by
  -- Reuse CubeInterpolation/Segment.lean's generic chain-rule argument:
  -- V=(ContinuousLinearMap.id ℝ ℝ).smulRight (y-a),
  -- U={z | a+z ∈ interior (centeredCube b H)}. U and V⁻¹'U are open.
  -- Apply V.iteratedFDerivWithin_comp_right to u ∘ (a+·) on U,
  -- then iteratedFDerivWithin_of_isOpen, iteratedFDeriv_comp_add_left,
  -- and iteratedDeriv_eq_iteratedFDeriv. Finally convert the ambient jet
  -- to the cube jet by iteratedFDerivWithin_eq_iteratedFDeriv using
  -- uniqueDiffOn_centeredCube and hu.contDiffAt at the interior point.
  -- segment_mem_interior_centeredCube supplies all interior memberships.
  -- Keep arbitrary k≤m, boundary y, r=0, and d=0; no extension assumption.
  let v : ℝ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (y - a)
  let S : Set (EuclideanSpace ℝ (Fin d)) :=
    {z | a + z ∈ interior (centeredCube b H)}
  have hS : IsOpen S :=
    isOpen_interior.preimage (continuous_const.add continuous_id)
  have hf : ContDiffOn ℝ m (fun z : EuclideanSpace ℝ (Fin d) => u (a + z)) S := by
    apply hS.contDiffOn_iff.mpr
    intro z hz
    exact ((hu.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hz)).comp z
      ((contDiff_const.add contDiff_id).contDiffAt)
  have hinterior := segment_mem_interior_centeredCube b a y H ha hy r hr
  have hvr : v r ∈ S := by
    simpa [S, v, ContinuousLinearMap.smulRight_apply] using hinterior
  have hpre : IsOpen (v ⁻¹' S) := hS.preimage v.continuous
  have hcomp := v.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn
    hpre.uniqueDiffOn hvr (show (k : WithTop ℕ∞) ≤ m from mod_cast hk)
  have hfun : (fun t : ℝ => u (a + t • (y - a))) =
      (fun z : EuclideanSpace ℝ (Fin d) => u (a + z)) ∘ v := by
    funext t
    simp [v, ContinuousLinearMap.smulRight_apply]
  have huAt : ContDiffAt ℝ k u (a + r • (y - a)) :=
    ((hu.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hinterior)).of_le (by exact_mod_cast hk)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_centeredCube b H hH) huAt (interior_subset hinterior)]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv]
  rw [← iteratedFDerivWithin_of_isOpen k hpre hvr,
    hcomp, iteratedFDerivWithin_of_isOpen k hS hvr]
  rw [iteratedFDeriv_comp_add_left]
  simp [v, ContinuousMultilinearMap.compContinuousLinearMap_apply]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

