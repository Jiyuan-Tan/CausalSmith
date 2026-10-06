module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetSymmetryTwo

/-!
# Adjacent swaps in finite-order jets

The leading-pair swap extends to any pair of consecutive derivative slots.
This is the analytic step needed before using finite permutation generators.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [a function is n + 1 times continuously differentiable at a point](hyp:hu), then for [any n
+ 1 directions](hyp:v) and [any position i among the first n](hyp:i), [exchanging the directions at
positions i and i + 1 leaves the order-(n + 1) derivative at that point unchanged](goal). -/
theorem finite_order_iteratedFDeriv_adjacent_swap {d n : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ (n + 1) u x)
    (v : Fin (n + 1) → (Fin d → ℝ)) (i : Fin n) :
    iteratedFDeriv ℝ (n + 1) u x
        (v ∘ Equiv.swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n + 1) u x v := by
  -- The first two positions are `finite_order_iteratedFDeriv_front_swap`.
  -- For later positions, peel off the first direction with
  -- `iteratedFDeriv_succ_apply_left'`. The induction hypothesis identifies
  -- the two scalar evaluations of the lower jet near `x`, so their derivatives
  -- at `x` agree.
  induction n generalizing x with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rcases Fin.exists_cons v with ⟨a, w, rfl⟩
      rcases Fin.exists_cons w with ⟨b, r, rfl⟩
      change (iteratedFDeriv ℝ (n + 2) u x)
          (Matrix.vecCons a (Matrix.vecCons b r) ∘ Equiv.swap 0 1) = _
      rw [Matrix.cons_cons_comp_swap_zero_one]
      simpa [Fin.cons, Matrix.vecCons] using
        finite_order_iteratedFDeriv_front_swap hu b a r
    | succ j =>
      rcases Fin.exists_cons v with ⟨a, w, rfl⟩
      have hlow : ContDiffAt ℝ (n + 1) u x := hu.of_le (by norm_cast; omega)
      have hnear :
          (fun y => (iteratedFDeriv ℝ (n + 1) u y)
            (w ∘ Equiv.swap j.castSucc j.succ)) =ᶠ[nhds x]
          (fun y => (iteratedFDeriv ℝ (n + 1) u y) w) := by
        filter_upwards [hlow.eventually (by simp)] with y hy
        exact ih hy w j
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) u) x :=
        hu.differentiableAt_iteratedFDeriv (by norm_cast; omega)
      have hidx : (Fin.succ j).castSucc = Fin.succ j.castSucc := Fin.ext rfl
      rw [hidx]
      change (iteratedFDeriv ℝ (n + 2) u x)
          (Matrix.vecCons a w ∘ Equiv.swap (Fin.succ j.castSucc) (Fin.succ j.succ)) = _
      rw [← Matrix.cons_swap]
      rw [hd.iteratedFDeriv_succ_apply_left', hd.iteratedFDeriv_succ_apply_left']
      exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L a) (hnear.fderiv_eq)

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
