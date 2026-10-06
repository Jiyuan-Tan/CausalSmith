module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic

/-!
# Euclidean seminorm conversion on a finite cube

The paper convention uses the square root of the coordinate square sum, while the
neutral fixed-cube API uses the ambient norm on `Fin d → ℝ`.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The Euclidean distance between two `d`-dimensional coordinate vectors. -/
noncomputable def euclideanDistance {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- For [a dimension](hyp:d) that is [at least one](hyp:hd), [a derivative order](hyp:m), and [an
exponent s](hyp:s) that is [positive](hyp:hs), [there is a positive constant C, depending only on
the dimension, the order, and the exponent, such that for every function and every nonnegative L:
if every order-m coordinate partial changes between any two points of the normalized cube by at
most L times their Euclidean distance to the power s, then the function satisfies the top-order
Hölder condition with constant C times L in the coordinatewise-maximum norm](goal). -/
theorem euclidean_to_topHolder (d m : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ),
        0 ≤ L →
        (∀ f : Fin m → Fin d, ∀ x ∈ cube d, ∀ y ∈ cube d,
          |coordPartial m u f x - coordPartial m u f y| ≤
            L * euclideanDistance x y ^ s) →
        TopHolder d m s (C * L) u := by
  refine ⟨(Real.sqrt d) ^ s, Real.rpow_pos_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hd)) _, ?_⟩
  intro u L hL hmod f x hx y hy
  have hsq : (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) * ‖x - y‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, ‖x - y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := norm_le_pi_norm (x - y) i
        simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using
          ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi)
      _ = (d : ℝ) * ‖x - y‖ ^ 2 := by simp
  have hdist : euclideanDistance x y ≤ Real.sqrt d * ‖x - y‖ := by
    calc
      euclideanDistance x y ≤ Real.sqrt ((d : ℝ) * ‖x - y‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = Real.sqrt d * ‖x - y‖ := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d), Real.sqrt_sq_eq_abs]
        simp
  have hpow : euclideanDistance x y ^ s ≤
      (Real.sqrt d) ^ s * ‖x - y‖ ^ s := by
    calc
      _ ≤ (Real.sqrt d * ‖x - y‖) ^ s :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hdist (le_of_lt hs)
      _ = _ := Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)
  exact (hmod f x hx y hy).trans (by
    calc
      L * euclideanDistance x y ^ s ≤ L * ((Real.sqrt d) ^ s * ‖x - y‖ ^ s) :=
        mul_le_mul_of_nonneg_left hpow hL
      _ = ((Real.sqrt d) ^ s * L) * ‖x - y‖ ^ s := by ring)

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
