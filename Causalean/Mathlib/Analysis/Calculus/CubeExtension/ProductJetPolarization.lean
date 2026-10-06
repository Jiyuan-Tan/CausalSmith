module
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Symmetric multilinear maps are determined by their diagonal

This algebraic fact is the polarization step in the exact product-jet formula.
It is stated for scalar continuous multilinear maps on a finite-dimensional
real space, but does not use differentiability.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [two continuous real-valued m-linear maps A and B on d-dimensional
coordinate space](hyp:A,B) are [symmetric under permutations of their
arguments](hyp:hA,hB) and [agree whenever every argument is the same
vector](hyp:hdiag), then [A = B](goal).

One route is to apply the real polarization identity to their difference.
The case `m = 0` follows directly from the diagonal assumption. For positive
order, expand the diagonal polynomial at sums of distinct vectors and isolate
the coefficient of their product; symmetry makes it `m!` times the desired
mixed value. -/
theorem continuousMultilinearMap_eq_of_symmetric_diagonal
    {d m : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)
    (hA : ∀ (σ : Equiv.Perm (Fin m)) (v : Fin m → Fin d → ℝ),
      A (v ∘ σ) = A v)
    (hB : ∀ (σ : Equiv.Perm (Fin m)) (v : Fin m → Fin d → ℝ),
      B (v ∘ σ) = B v)
    (hdiag : ∀ z : Fin d → ℝ, A (fun _ => z) = B (fun _ => z)) :
    A = B := by
  have heq : (fun z : Fin d → ℝ => A (fun _ => z)) =
      (fun z : Fin d → ℝ => B (fun _ => z)) := funext hdiag
  ext v
  have hderiv := congrArg
    (fun f : (Fin d → ℝ) → ℝ => iteratedFDeriv ℝ m f 0 v) heq
  rw [A.iteratedFDeriv_comp_diagonal 0 v,
    B.iteratedFDeriv_comp_diagonal 0 v] at hderiv
  have hsumA : (∑ σ : Equiv.Perm (Fin m), A (fun i => v (σ i))) =
      (Fintype.card (Equiv.Perm (Fin m))) • A v := by
    simp only [show ∀ σ : Equiv.Perm (Fin m),
      A (fun i => v (σ i)) = A v from fun σ => hA σ v, Finset.sum_const,
      Finset.card_univ]
  have hsumB : (∑ σ : Equiv.Perm (Fin m), B (fun i => v (σ i))) =
      (Fintype.card (Equiv.Perm (Fin m))) • B v := by
    simp only [show ∀ σ : Equiv.Perm (Fin m),
      B (fun i => v (σ i)) = B v from fun σ => hB σ v, Finset.sum_const,
      Finset.card_univ]
  rw [hsumA, hsumB] at hderiv
  have hcard : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin m)))
  exact (mul_left_cancel₀ hcard) (by simpa only [nsmul_eq_mul] using hderiv)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
