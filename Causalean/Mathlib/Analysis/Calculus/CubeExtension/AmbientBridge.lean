module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Extension
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.BoundaryFacts

/-!
# Ambient and within-cube Hölder balls are interchangeable

The library carries two Hölder balls on the closed normalized cube `[-1,1]^d`. The within-cube
ball `CubeHolderBall` is the standard one: all derivatives are taken within the cube, so
membership depends only on the values of the function on the cube. The ambient ball
`CubeInterpolation.HolderBall` takes the derivatives in the whole space, so at boundary points
membership also depends on the function outside the cube.

This file proves that the two describe the same functions on the cube, up to a constant in the
radius; the extension direction, from the within-cube ball to the ambient ball, is proved for
Hölder exponents in `(0,1]`.

## Main results

* `cubeHolderBall_of_holderBall` — a function in the ambient ball of radius `R` lies in the
  within-cube ball of the same radius.
* `exists_holderBall_extension` — for a Hölder exponent in `(0,1]` there is a constant `A`,
  depending only on the dimension, the order and the exponent, such that every function in the
  within-cube ball of radius `L` agrees on the cube with a function in the ambient ball of radius
  `A·L`.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

private theorem openCube_subset_cube' (d : ℕ) : openCube d ⊆ cube d := by
  intro x hx i
  exact ⟨(hx i trivial).1.le, (hx i trivial).2.le⟩

private theorem cube_eq_pi' (d : ℕ) :
    cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
    Pi.le_def, forall_and]

/-- [A function in the ambient Hölder ball](hyp:h) of order m, [nonnegative exponent
s](hyp:hs) and radius R on the closed normalized cube [lies in the within-cube Hölder ball with
the same order, exponent and radius](goal): replacing the whole-space derivatives by derivatives
taken within the cube keeps every derivative bound and the top-order Hölder modulus. -/
theorem cubeHolderBall_of_holderBall {d m : ℕ} {s R : ℝ} {u : (Fin d → ℝ) → ℝ}
    (hs : 0 ≤ s) (h : HolderBall d m s R u) : CubeHolderBall d m s R u := by
  have hu := h.regularity
  have hcl : ∀ x ∈ cube d, x ∈ closure (openCube d) := fun x hx =>
    cube_subset_closure_openCube d hx
  refine ⟨hu, ?_, ?_⟩
  · intro j hj f x hx
    have hR : 0 ≤ R := (abs_nonneg _).trans (h.derivBound 0 (Nat.zero_le m) Fin.elim0 x hx)
    exact within_coordPartial_bound_extends hu hj f
      (fun y hy => h.derivBound j hj f y (openCube_subset_cube' d hy)) x hx
  · intro f x hx y hy
    -- The inequality holds on the open cube, where both jets are ambient partials, and both
    -- sides are continuous on the closed cube, whose product is the closure of the open product.
    let F : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun p =>
      |coordJetOn (cube d) m u f p.1 - coordJetOn (cube d) m u f p.2|
    let G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun p => R * ‖p.1 - p.2‖ ^ s
    have hFcont : ContinuousOn F (cube d ×ˢ cube d) := by
      have h1 : ContinuousOn (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
          coordJetOn (cube d) m u f p.1) (cube d ×ˢ cube d) :=
        (continuousOn_coordJetOn_cube hu le_rfl f).comp continuousOn_fst (fun p hp => hp.1)
      have h2 : ContinuousOn (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
          coordJetOn (cube d) m u f p.2) (cube d ×ˢ cube d) :=
        (continuousOn_coordJetOn_cube hu le_rfl f).comp continuousOn_snd (fun p hp => hp.2)
      exact (h1.sub h2).abs
    have hGcont : Continuous G := by
      have : Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖p.1 - p.2‖ ^ s) :=
        (Real.continuous_rpow_const hs).comp (by fun_prop)
      exact continuous_const.mul this
    have hopen : ∀ p ∈ openCube d ×ˢ openCube d, F p ≤ G p := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      change |coordJetOn (cube d) m u f a - coordJetOn (cube d) m u f b| ≤ R * ‖a - b‖ ^ s
      rw [coordJetOn_cube_eq_ambient hu le_rfl ha, coordJetOn_cube_eq_ambient hu le_rfl hb]
      exact h.modulus f a (openCube_subset_cube' d ha) b (openCube_subset_cube' d hb)
    have hmem : (x, y) ∈ closure (openCube d ×ˢ openCube d) := by
      rw [closure_prod_eq]
      exact ⟨hcl x hx, hcl y hy⟩
    have hsub : closure (openCube d ×ˢ openCube d) ⊆ cube d ×ˢ cube d := by
      rw [closure_prod_eq]
      have hclosed : IsClosed (cube d) := by
        rw [cube_eq_pi']
        exact isClosed_set_pi (fun _ _ => isClosed_Icc)
      have := closure_minimal (openCube_subset_cube' d) hclosed
      exact Set.prod_mono this this
    exact le_on_closure hopen (hFcont.mono hsub) hGcont.continuousOn hmem

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and [a Hölder exponent s](hyp:s)
with [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1), [there is a positive constant A such that every
function in the within-cube Hölder ball of order m, exponent s and radius L ≥ 0 on the closed
normalized cube agrees on the cube with a function in the ambient Hölder ball of order m,
exponent s and radius A·L](goal). The constant depends only on d, m and s, so on the cube the
ambient ball and the standard within-cube ball contain the same functions up to this factor in
the radius. -/
theorem exists_holderBall_extension (d m : ℕ) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∃ U : (Fin d → ℝ) → ℝ,
          Set.EqOn U u (cube d) ∧ HolderBall d m s (A * L) U := by
  obtain ⟨A, hA, hext⟩ := exists_global_holder_extension d m s hs hs1
  refine ⟨A, hA, ?_⟩
  intro u L hL hu
  obtain ⟨U, hEq, hSmooth, hBounds, hMod⟩ := hext u L hL hu
  have hdir : ∀ {j : ℕ} (f : Fin j → Fin d),
      ∏ k, ‖(Pi.single (f k) (1 : ℝ) : Fin d → ℝ)‖ = 1 := by
    intro j f
    simp [Pi.norm_single]
  refine ⟨U, hEq, hSmooth.contDiffOn, ?_, ?_⟩
  · intro j hj f x _
    unfold coordPartial
    calc |iteratedFDeriv ℝ j U x (fun k => Pi.single (f k) (1 : ℝ))|
        = ‖iteratedFDeriv ℝ j U x (fun k => Pi.single (f k) (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ j U x‖ * ∏ k, ‖(Pi.single (f k) (1 : ℝ) : Fin d → ℝ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ j U x‖ := by rw [hdir f, mul_one]
      _ ≤ A * L := hBounds j hj x
  · intro f x _ y _
    unfold coordPartial
    calc |iteratedFDeriv ℝ m U x (fun k => Pi.single (f k) (1 : ℝ)) -
          iteratedFDeriv ℝ m U y (fun k => Pi.single (f k) (1 : ℝ))|
        = ‖(iteratedFDeriv ℝ m U x - iteratedFDeriv ℝ m U y)
            (fun k => Pi.single (f k) (1 : ℝ))‖ := by
          rw [sub_apply, Real.norm_eq_abs]
      _ ≤ ‖iteratedFDeriv ℝ m U x - iteratedFDeriv ℝ m U y‖ *
            ∏ k, ‖(Pi.single (f k) (1 : ℝ) : Fin d → ℝ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ m U x - iteratedFDeriv ℝ m U y‖ := by rw [hdir f, mul_one]
      _ ≤ A * L * ‖x - y‖ ^ s := hMod x y

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
