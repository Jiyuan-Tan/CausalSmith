module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorGridWeights
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic

/-!
# Fixed tensor grid coefficient bounds

The existing Causalean tensor interpolation formula supplies a uniform coefficient norm
bound for polynomials of arbitrary finite coordinate degree.
-/

public section

open scoped BigOperators
open Causalean.Mathlib.Analysis.Approximation.Chebyshev

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a dimension and a degree m](hyp:d,m), [there is a positive constant C such that every
multivariate polynomial of degree at most m in each variable that is bounded in absolute value by a
nonnegative B at every point of the fixed tensor grid has every tensor monomial coefficient bounded
in absolute value by C times B](goal). -/
theorem tensor_coefficient_bound (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : MvPolynomial (Fin d) ℝ) (B : ℝ),
        0 ≤ B → (∀ i, p.degreeOf i ≤ m) →
        (∀ b : Fin d → Fin (m + 1),
          |MvPolynomial.eval (tensorGridPoint b) p| ≤ B) →
        ∀ a : Fin d → Fin (m + 1), |tensorCoeffs (D := m) p a| ≤ C * B := by
  classical
  refine ⟨((2 : ℝ) ^ (4 * m + 4)) ^ d, by positivity, ?_⟩
  intro p B hB hdeg hgrid a
  have hw : (∑ b : Fin d → Fin (m + 1), |tensorGridWeight a b|) ≤
      ((2 : ℝ) ^ (4 * m + 4)) ^ d := by
    calc
      _ ≤ ∑ a : Fin d → Fin (m + 1),
          ∑ b : Fin d → Fin (m + 1), |tensorGridWeight a b| :=
        Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          (Finset.mem_univ a)
      _ ≤ _ := tensorGrid_weight_oneNorm_le d m
  rw [tensorGrid_coeff_recovery p hdeg a]
  calc
    |∑ b : Fin d → Fin (m + 1),
        tensorGridWeight a b * MvPolynomial.eval (tensorGridPoint b) p| ≤
        ∑ b : Fin d → Fin (m + 1),
          |tensorGridWeight a b * MvPolynomial.eval (tensorGridPoint b) p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b : Fin d → Fin (m + 1),
          |tensorGridWeight a b| * |MvPolynomial.eval (tensorGridPoint b) p| := by
      simp only [abs_mul]
    _ ≤ ∑ b : Fin d → Fin (m + 1), |tensorGridWeight a b| * B := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hgrid b) (abs_nonneg _)
    _ = (∑ b : Fin d → Fin (m + 1), |tensorGridWeight a b|) * B := by
      rw [Finset.sum_mul]
    _ ≤ ((2 : ℝ) ^ (4 * m + 4)) ^ d * B :=
      mul_le_mul_of_nonneg_right hw hB

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
