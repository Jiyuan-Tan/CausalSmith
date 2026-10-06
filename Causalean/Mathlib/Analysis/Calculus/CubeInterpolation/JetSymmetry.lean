module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetSymmetryAdjacent
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Finite-order symmetry of coordinate jets

At a point of finite `C^k` regularity over the reals, the order-`k` iterated
Fréchet derivative is invariant under permutations of its directions. This is
the symmetry needed to recover ordered coordinate partials from homogeneous
Taylor terms without assuming analyticity.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [a function is k times continuously differentiable at a point](hyp:hu), then for [any k
directions](hyp:v) and [any permutation of them](hyp:σ), [the order-k derivative at that point
takes the same value on the reordered directions as on the original ones](goal). -/
theorem finite_order_iteratedFDeriv_perm {d k : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ k u x) (v : Fin k → (Fin d → ℝ))
    (σ : Equiv.Perm (Fin k)) :
    iteratedFDeriv ℝ k u x (v ∘ σ) = iteratedFDeriv ℝ k u x v := by
  cases k with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim σ 1
    simp [hσ]
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {τ | ∀ w : Fin (n + 1) → (Fin d → ℝ),
            iteratedFDeriv ℝ (n + 1) u x (w ∘ τ) =
              iteratedFDeriv ℝ (n + 1) u x w}
        one_mem' := by simp
        mul_mem' := by
          intro τ ρ hτ hρ w
          calc
            iteratedFDeriv ℝ (n + 1) u x
                (w ∘ (τ * ρ : Equiv.Perm (Fin (n + 1)))) =
                iteratedFDeriv ℝ (n + 1) u x ((w ∘ τ) ∘ ρ) := by
                  congr 1
            _ = iteratedFDeriv ℝ (n + 1) u x (w ∘ τ) := hρ (w ∘ τ)
            _ = iteratedFDeriv ℝ (n + 1) u x w := hτ w }
    have hgen : (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ⊆ S := by
      rintro τ ⟨i, rfl⟩
      exact fun w => finite_order_iteratedFDeriv_adjacent_swap hu w i
    have htop : S = ⊤ := by
      apply top_unique
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ n]
      exact Submonoid.closure_le.mpr hgen
    have hσ : σ ∈ S := by rw [htop]; trivial
    exact hσ v

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
