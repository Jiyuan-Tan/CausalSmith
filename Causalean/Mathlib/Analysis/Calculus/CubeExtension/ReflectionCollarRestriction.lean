module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceGluing

/-!
# Restricting reflected collar jets to the original cube

After face gluing, the within-collar jets of a reflected response coincide on
the original cube with its intrinsic cube jets, including face edges.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), [a response u is m times
continuously differentiable within the closed cube](hyp:hu), and [j ≤
m](hyp:hj), then at [every point x of the cube](hyp:hx) [the order-j
within-collar Fréchet derivative of the one-face reflection of u equals the
order-j within-cube derivative of u](goal). -/
theorem leftFaceReflection_withinJet_eq_cube
    (d m j : ℕ) (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (hj : j ≤ m) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
      (leftCubeCollar d m i) x =
    iteratedFDerivWithin ℝ j u (cube d) x := by
  have hsub : openCube d ⊆ cube d := by
    intro y hy k
    exact ⟨(hy k trivial).1.le, (hy k trivial).2.le⟩
  have hcube : cube d ⊆ leftCubeCollar d m i := by
    intro y hy
    rw [← leftClosedExteriorCollar_union_cube d m i]
    exact Or.inr hy
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hunique : UniqueDiffOn ℝ (cube d) := by
    have hpi : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
      ext y
      simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
        Pi.le_def, forall_and]
    rw [hpi]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  have hcollar := leftFaceReflection_contDiffOn_collar d m i a ha u hu
  have hreflCont : ContinuousOn
      (fun y => iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
        (leftCubeCollar d m i) y) (cube d) :=
    (hcollar.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast hj) (uniqueDiffOn_leftCubeCollar d m i)).mono hcube
  have huCont : ContinuousOn
      (fun y => iteratedFDerivWithin ℝ j u (cube d) y) (cube d) :=
    hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hunique
  have heq : Set.EqOn
      (fun y => iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
        (leftCubeCollar d m i) y)
      (fun y => iteratedFDerivWithin ℝ j u (cube d) y)
      (openCube d) := by
    intro y hy
    have hycube := hsub hy
    have hreg : ContDiffAt ℝ j (leftFaceReflection d m i a u) y :=
      ((hcollar.mono (hsub.trans hcube)).contDiffAt (hopen.mem_nhds hy)).of_le
        (by exact_mod_cast hj)
    calc
      iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
          (leftCubeCollar d m i) y =
          iteratedFDeriv ℝ j (leftFaceReflection d m i a u) y :=
        iteratedFDerivWithin_eq_iteratedFDeriv
          (uniqueDiffOn_leftCubeCollar d m i) hreg (hcube hycube)
      _ = iteratedFDerivWithin ℝ j
          (leftFaceReflection d m i a u) (cube d) y :=
        (iteratedFDerivWithin_eq_iteratedFDeriv hunique hreg hycube).symm
      _ = iteratedFDerivWithin ℝ j u (cube d) y :=
        iteratedFDerivWithin_congr
          (leftFaceReflection_eqOn_cube d m i a u) hycube j
  exact (heq.of_subset_closure hreflCont huCont hsub
    (cube_subset_closure_openCube d)) hx

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
