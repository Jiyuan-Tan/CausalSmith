module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.CoordinateLimit
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceAlgebra
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionSampleJets
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionSampleLimit

/-!
# Boundary trace of reflected jets

The ambient jets of a one-face reflection on its open exterior collar tend to
the intrinsic cube jets at the face. This statement is about a limit from the
collar, so it does not use ambient boundary jets of the original response.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), [a response u is m times
continuously differentiable within the closed cube](hyp:hu), [j ≤ m](hyp:hj),
and [x is a cube point](hyp:hx) [on the left face in coordinate i](hyp:hxi),
then [as z approaches x from within the open exterior collar, the order-j
ambient derivative of the one-face reflection of u at z, evaluated on the
standard basis vectors in directions f, converges to the order-j within-cube
derivative of u at x evaluated on the same vectors](goal). The moment equations
cancel the inward sample factors. -/
theorem leftFaceReflection_coordinate_jet_tendsto_face (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (j : ℕ) (hj : j ≤ m) (f : Fin j → Fin d) (x : Fin d → ℝ)
    (hx : x ∈ cube d) (hxi : x i = -1) :
    Filter.Tendsto
      (fun z => iteratedFDeriv ℝ j (leftFaceReflection d m i a u) z
        (fun k => Pi.single (f k) (1 : ℝ)))
      (nhdsWithin x (leftOpenCubeCollar d m i))
      (nhds (iteratedFDerivWithin ℝ j u (cube d) x
        (fun k => Pi.single (f k) (1 : ℝ)))) := by
  classical
  have hsum : Filter.Tendsto
      (fun z => ∑ q : Fin (m + 1), a q *
        iteratedFDeriv ℝ j (fun y => u (leftFaceSample d i q y)) z
          (fun k => Pi.single (f k) (1 : ℝ)))
      (nhdsWithin x (leftOpenCubeCollar d m i))
      (nhds (∑ q : Fin (m + 1), a q *
        iteratedFDerivWithin ℝ j u (cube d) x
          (fun k =>
            (if f k = i then -((q.val : ℝ) + 1) else 1) •
              Pi.single (f k) (1 : ℝ)))) := by
    apply tendsto_finsetSum
    intro q hq
    exact tendsto_const_nhds.mul
      (leftFaceSample_coordinate_jet_tendsto_face d m i q u hu j hj f x hx hxi)
  rw [reflection_weighted_coordinate_jet d m i a ha j hj
    (iteratedFDerivWithin ℝ j u (cube d) x) f] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [leftFaceReflection_iteratedFDeriv_eq_sum d m i a u hu j hj z hz]
  simp [smul_eq_mul]

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), [a response u is m times
continuously differentiable within the closed cube](hyp:hu), [j ≤ m](hyp:hj),
and [x is a cube point](hyp:hx) [on the left face in coordinate i](hyp:hxi),
then [as z approaches x from within the open exterior collar, the order-j
ambient derivative of the one-face reflection of u at z converges to the order-j
within-cube derivative of u at x](goal). -/
theorem leftFaceReflection_jet_tendsto_face (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (j : ℕ) (hj : j ≤ m) (x : Fin d → ℝ)
    (hx : x ∈ cube d) (hxi : x i = -1) :
    Filter.Tendsto
      (fun z => iteratedFDeriv ℝ j (leftFaceReflection d m i a u) z)
      (nhdsWithin x (leftOpenCubeCollar d m i))
      (nhds (iteratedFDerivWithin ℝ j u (cube d) x)) := by
  apply tendsto_multilinearMap_of_coordinate_tendsto d j
  intro f
  exact leftFaceReflection_coordinate_jet_tendsto_face
    d m i a ha u hu j hj f x hx hxi

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
