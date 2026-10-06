module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Second derivatives of finite jets

Finite `C^(n+2)` regularity makes the order-`n` derivative a `C²` map.
The library's second-derivative symmetry then applies to that lower jet.
An evaluation bridge identifies its second derivative with the first two
slots of the order-`n+2` derivative of the original map.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The order-`n` iterated derivative of a `C^(n+2)` real function is `C²`
at the same point. -/
theorem finite_order_lower_jet_contDiffAt_two {d n : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ (n + 2) u x) :
    ContDiffAt ℝ 2 (iteratedFDeriv ℝ n u) x := by
  exact hu.iteratedFDeriv_right (m := 2) (i := n)
    (by exact le_of_eq (add_comm (2 : WithTop ℕ∞) (n : WithTop ℕ∞)))

/-- At a `C^(n+2)` point, the second derivative of the order-`n` jet is
symmetric in its two input directions. -/
theorem finite_order_lower_jet_second_symmetric {d n : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ (n + 2) u x) (a b : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n u)) x a b =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n u)) x b a := by
  exact (finite_order_lower_jet_contDiffAt_two hu).isSymmSndFDerivAt
    (by norm_num) a b

/-- Evaluating the second derivative of the order-`n` jet on two directions
and then on `n` more directions equals the order-`n+2` derivative evaluated
on that concatenated list. -/
theorem iteratedFDeriv_two_front_as_second_jet {d n : ℕ}
    (u : (Fin d → ℝ) → ℝ) (x a b : Fin d → ℝ)
    (r : Fin n → (Fin d → ℝ)) :
    (iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n u) x ![a, b]) r =
      iteratedFDeriv ℝ (n + 2) u x (Fin.cons a (Fin.cons b r)) := by
  -- Both sides are obtained by twice applying
  -- `iteratedFDeriv_succ_apply_left`; unfold the curry equivalences and
  -- commute evaluation at the fixed trailing directions with `fderiv`.
  let L : ((Fin d → ℝ) [×(n + 1)]→L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      ((Fin d → ℝ) [×1]→L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Fin d → ℝ) ℝ).trans
      (continuousMultilinearCurryFin1 ℝ (Fin d → ℝ)
        ((Fin d → ℝ) [×n]→L[ℝ] ℝ)).symm
  have h : iteratedFDeriv ℝ 1 (iteratedFDeriv ℝ n u) =
      L ∘ iteratedFDeriv ℝ (n + 1) u := by
    funext y
    ext v r
    rw [iteratedFDeriv_one_apply]
    simp [L, iteratedFDeriv_succ_apply_left]
  change ((fderiv ℝ (iteratedFDeriv ℝ 1 (iteratedFDeriv ℝ n u)) x) a) ![b] r =
    ((fderiv ℝ (iteratedFDeriv ℝ (n + 1) u) x) a) (Fin.cons b r)
  rw [h, L.comp_fderiv]
  rfl

/-- If [a function is n + 2 times continuously differentiable at a point](hyp:hu), then for [any
two leading directions](hyp:a,b) and [any n further directions](hyp:r), [exchanging the two leading
directions leaves the order-(n + 2) derivative at that point unchanged](goal). -/
theorem finite_order_iteratedFDeriv_front_swap {d n : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ (n + 2) u x)
    (a b : Fin d → ℝ) (r : Fin n → (Fin d → ℝ)) :
    iteratedFDeriv ℝ (n + 2) u x (Fin.cons a (Fin.cons b r)) =
      iteratedFDeriv ℝ (n + 2) u x (Fin.cons b (Fin.cons a r)) := by
  calc
    _ = (iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n u) x ![a, b]) r :=
      (iteratedFDeriv_two_front_as_second_jet u x a b r).symm
    _ = (iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n u) x ![b, a]) r := by
      simpa [iteratedFDeriv_two_apply] using
        congrArg (fun L => L r) (finite_order_lower_jet_second_symmetric hu a b)
    _ = _ := iteratedFDeriv_two_front_as_second_jet u x b a r

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
