module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCoefficients

/-!
# Polynomial reproduction by one-sided reflection

The reflection weights reproduce every Taylor polynomial through the chosen
order. This algebraic identity is the jet-matching step at a cube face.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [the reflection weights a satisfy the moment conditions
Σ_i a_i·(−(i + 1))^k = 1 for every k ≤ m](hyp:ha), then [for every polynomial with coefficients
c_0, …, c_m and every real t, the weighted sum over i of a_i times the
polynomial evaluated at −(i + 1)·t equals the polynomial evaluated at t](goal);
that is, moment-matched weights reproduce every polynomial of degree at most m. -/
theorem reflection_taylor_polynomial (m : ℕ)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ i : Fin (m + 1),
        a i * (-((i.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (c : Fin (m + 1) → ℝ) (t : ℝ) :
    (∑ i : Fin (m + 1),
      a i * (∑ k : Fin (m + 1),
        c k * ((-((i.val : ℝ) + 1)) * t) ^ (k.val : ℕ))) =
      ∑ k : Fin (m + 1), c k * t ^ (k.val : ℕ) := by
  calc
    _ = ∑ i : Fin (m + 1), ∑ k : Fin (m + 1),
        a i * (c k * ((-((i.val : ℝ) + 1)) * t) ^ (k.val : ℕ)) := by
          simp only [Finset.mul_sum]
    _ = ∑ k : Fin (m + 1), ∑ i : Fin (m + 1),
        a i * (c k * ((-((i.val : ℝ) + 1)) * t) ^ (k.val : ℕ)) :=
          Finset.sum_comm
    _ = ∑ k : Fin (m + 1),
        (c k * t ^ (k.val : ℕ)) *
          (∑ i : Fin (m + 1), a i * (-((i.val : ℝ) + 1)) ^ (k.val : ℕ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_pow]
          ring
    _ = _ := by simp only [ha, mul_one]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
