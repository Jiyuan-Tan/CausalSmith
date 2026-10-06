module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Definitions

/-!
# Enlarging finite cosine spans

Zero padding of coefficient sequences embeds every finite normalized cosine span
in each larger rank. The rank still counts the constant mode, with no positivity
assumption needed for this algebraic inclusion.
-/

public section

open scoped BigOperators
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- A [cosine polynomial](hyp:a) of [smaller rank](hyp:hmn) [equals its
zero-padded polynomial at the larger rank](goal), at every [position](hyp:x). -/
theorem cosinePolynomial_zero_pad {m n : ℕ} (hmn : m ≤ n) (a : ℕ → ℝ) (x : ℝ) :
    cosinePolynomial n (fun j => if j < m then a j else 0) x =
      cosinePolynomial m a x := by
  classical
  unfold cosinePolynomial
  calc
    _ = ∑ j ∈ Finset.range m, (if j < m then a j else 0) * cosineBasis j x := by
      symm
      apply Finset.sum_subset (Finset.range_mono hmn)
      intro j hjn hjm
      simp only [Finset.mem_range] at hjm
      simp [hjm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]

/-- A [function in a smaller cosine span](hyp:hp) [belongs to every larger
cosine span](goal), whenever [the ranks are ordered](hyp:hmn). -/
theorem inCosineSpan_mono {m n : ℕ} {p : ℝ → ℝ}
    (hmn : m ≤ n) (hp : InCosineSpan m p) : InCosineSpan n p := by
  rcases hp with ⟨a, ha⟩
  refine ⟨fun j => if j < m then a j else 0, ?_⟩
  intro x hx
  rw [cosinePolynomial_zero_pad hmn, ha x hx]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

