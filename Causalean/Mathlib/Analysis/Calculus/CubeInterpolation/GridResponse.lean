module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Grid
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetPolynomial
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Taylor

/-!
# Taylor polynomial values on the fixed tensor grid

The top derivative seminorm controls the Taylor remainder at every fixed grid
node. Together with the response supremum this bounds the Taylor polynomial
on that grid, with a constant independent of the function and its bounds.
-/

public section

open scoped BigOperators
open Causalean.Mathlib.Analysis.Approximation.Chebyshev

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a dimension, a derivative order m, and an exponent s](hyp:d,m,s) with [s positive](hyp:hs)
and [s at most one](hyp:hs1), [there is a positive constant C such that the following holds for all
nonnegative M and L: if a function is m times continuously differentiable on the closed normalized
cube, bounded there by M in absolute value, and satisfies the top-order Hölder condition with
exponent s and constant L, then any polynomial that equals its order-m Taylor polynomial at a
centre in the open cube is at most C times (M + L) in absolute value at every node of the fixed
tensor grid](goal). -/
theorem taylor_polynomial_grid_bound (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L → ContDiffOn ℝ m u (cube d) →
        (∀ y ∈ cube d, |u y| ≤ M) → TopHolder d m s L u →
        ∀ x ∈ openCube d, ∀ p : MvPolynomial (Fin d) ℝ,
          (∀ y : Fin d → ℝ,
            MvPolynomial.eval y p =
              ∑ k ∈ Finset.range (m + 1),
                (Nat.factorial k : ℝ)⁻¹ *
                  iteratedFDeriv ℝ k u x (fun _ => y - x)) →
          ∀ b : Fin d → Fin (m + 1),
            |MvPolynomial.eval (tensorGridPoint b) p| ≤ C * (M + L) := by
  obtain ⟨A, hApos, hA⟩ := top_holder_taylor_remainder d m s hs hs1
  have hcompact : IsCompact (cube d) := by
    have h := isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    convert h using 1
    ext z
    simp only [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
      Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc]
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  let K : ℝ := max 1 D
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hKdist : ∀ x ∈ cube d, ∀ y ∈ cube d, ‖y - x‖ ≤ K := by
    intro x hx y hy
    rw [← dist_eq_norm]
    exact (hD hy hx).trans (le_max_right _ _)
  refine ⟨1 + A * K ^ ((m : ℝ) + s), by positivity, ?_⟩
  intro u M L hM hL hu hbound hholder x hx p hp b
  let y := tensorGridPoint b
  have hy : y ∈ cube d := tensorGridPoint_mem_cube b
  have hx' : x ∈ cube d := by
    intro i
    exact ⟨le_of_lt (hx i (Set.mem_univ i)).1,
      le_of_lt (hx i (Set.mem_univ i)).2⟩
  have hpow : ‖y - x‖ ^ ((m : ℝ) + s) ≤ K ^ ((m : ℝ) + s) :=
    Real.rpow_le_rpow (norm_nonneg _) (hKdist x hx' y hy) (by positivity)
  have hrem := hA u L hL hu hholder x hx y hy
  rw [← hp y] at hrem
  have hpoly : |MvPolynomial.eval y p| ≤ M + A * L * K ^ ((m : ℝ) + s) := by
    calc
      |MvPolynomial.eval y p| = |u y - (u y - MvPolynomial.eval y p)| := by ring
      _ ≤ |u y| + |u y - MvPolynomial.eval y p| := by
        simpa [abs_sub_comm] using abs_sub_le (u y) 0 (u y - MvPolynomial.eval y p)
      _ ≤ M + A * L * ‖y - x‖ ^ ((m : ℝ) + s) :=
        add_le_add (hbound y hy) hrem
      _ ≤ M + A * L * K ^ ((m : ℝ) + s) := by
        have h := mul_le_mul_of_nonneg_left hpow (mul_nonneg hApos.le hL)
        nlinarith [h]
  change |MvPolynomial.eval y p| ≤ (1 + A * K ^ ((m : ℝ) + s)) * (M + L)
  nlinarith [mul_nonneg (le_of_lt hApos) (Real.rpow_nonneg hKpos.le ((m : ℝ) + s))]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
