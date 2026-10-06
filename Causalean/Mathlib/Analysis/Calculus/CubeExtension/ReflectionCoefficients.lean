module
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite reflection coefficients for cube extension

The one-sided reflection construction combines finitely many inward samples.
Its coefficients reproduce boundary derivatives through a prescribed order.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- For [every derivative order m](hyp:m) [there are real weights a_0, …, a_m
such that, for every k ≤ m, the sum over i of a_i·(−(i + 1))^k equals one](goal);
that is, the negative integer dilation factors −1, …, −(m + 1) admit weights all
of whose moments through order m equal one. -/
theorem exists_reflection_coefficients (m : ℕ) :
    ∃ a : Fin (m + 1) → ℝ,
      ∀ k : Fin (m + 1),
        (∑ i : Fin (m + 1),
          a i * (-((i.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1 := by
  /- Let v i = -(i+1). The transpose of `Matrix.vandermonde v` is
  invertible because the nodes are pairwise distinct. Solve Vᵀ a = 1.
  This is precisely the jet-matching system for reflection at either face. -/
  let v : Fin (m + 1) → ℝ := fun i => -((i.val : ℝ) + 1)
  have hv : Function.Injective v := by
    intro i j hij
    have h : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 := neg_injective hij
    have h' : (i.val : ℝ) = (j.val : ℝ) := add_right_cancel h
    exact Fin.ext (by exact_mod_cast h')
  have hdet : (Matrix.vandermonde v).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hunit : IsUnit (Matrix.vandermonde v).transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa using (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨a, ha⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) (fun _ => (1 : ℝ))
  refine ⟨a, fun k => ?_⟩
  have hk := congrFun ha k
  simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, v, mul_comm] using hk

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
