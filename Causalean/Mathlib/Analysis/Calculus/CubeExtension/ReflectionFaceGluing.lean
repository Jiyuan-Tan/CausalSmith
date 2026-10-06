module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ClosedPieceGluing
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionClosedExterior
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarGeometry
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceFirstDeriv
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceJets
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceLimit
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionInterior

/-!
# Gluing a one-face reflection to the cube

The reflected exterior branch and the original response have matching jets
at their common face. This module packages that match as regularity on the
closed one-face collar, including its edges and corners.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha) and [a response u is m times
continuously differentiable within the closed cube](hyp:hu), then [the one-face
reflection of u across the left face in coordinate i is m times continuously
differentiable within the closed left collar](goal). -/
theorem leftFaceReflection_contDiffOn_collar (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d)) :
    ContDiffOn ℝ m (leftFaceReflection d m i a u)
      (leftCubeCollar d m i) := by
  have hzero : (∑ q : Fin (m + 1), a q) = 1 := by
    simpa using ha (0 : Fin (m + 1))
  have hpi : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
      Pi.le_def, forall_and]
  have hclosed : IsClosed (cube d) := by
    rw [hpi]
    apply isClosed_set_pi
    intro j hj
    exact isClosed_Icc
  have hunique : UniqueDiffOn ℝ (cube d) := by
    rw [hpi]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  have hcube : ContDiffOn ℝ m (leftFaceReflection d m i a u) (cube d) :=
    hu.congr (leftFaceReflection_eqOn_cube d m i a u)
  have hglue := contDiffOn_closed_union_of_matching_jets d m
    (leftClosedExteriorCollar d m i) (cube d)
    (isClosed_leftClosedExteriorCollar d m i) hclosed
    (uniqueDiffOn_leftClosedExteriorCollar d m i) hunique
    (by rw [leftClosedExteriorCollar_union_cube]
        exact uniqueDiffOn_leftCubeCollar d m i)
    (leftFaceReflection d m i a u)
    (leftFaceReflection_contDiffOn_closedExterior d m i a hzero u hu) hcube
    (by
      intro j hj x hx
      have hface : x ∈ {x ∈ cube d | x i = -1} := by
        simpa [leftClosedExteriorCollar_inter_cube] using hx
      rw [leftFaceReflection_closedExterior_jet_eq_face d m i a ha u hu j hj x
        hface.1 hface.2]
      exact (iteratedFDerivWithin_congr
        (leftFaceReflection_eqOn_cube d m i a u) hface.1 j).symm)
  simpa [leftClosedExteriorCollar_union_cube] using hglue

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
