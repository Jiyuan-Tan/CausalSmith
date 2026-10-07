module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Radial
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ScalingCore

/-!
# Uniform bandwidth bounds for exact coordinate and mixed profiles

The generic amplitude and dilation calculus specializes to the odd coordinate
product, its Euclidean version, and the tangent product with complementary
radial plateau. Each constant is independent of bandwidth, exponent, and center.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- In [dimension](hyp:d), [one fixed constant bounds all scaled coordinate odd-product jets](goal),
uniformly over exponents in `(0,2]`, bandwidths in `(0,1]`, and centers. -/
theorem oddProduct_uniform_scaled_bounds (d : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (β h : ℝ), 0 < β → β ≤ 2 → 0 < h → h ≤ 1 → ∀ z : Fin d → ℝ,
      ScaledJetBounds β h (scaledCopy β h z oddProduct) C := by
  obtain ⟨C, hC, hf⟩ := oddProduct_jetBounds d
  exact ⟨C, hC, fun β h _ _ hh _ z => scaledCopy_jetBounds β h z hf hh⟩

/-- In [dimension](hyp:d), [one fixed constant bounds all scaled Euclidean odd-product jets](goal),
uniformly over exponents in `(0,2]`, bandwidths in `(0,1]`, and centers. -/
theorem oddEuclidean_uniform_scaled_bounds (d : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (β h : ℝ), 0 < β → β ≤ 2 → 0 < h → h ≤ 1 → ∀ z : EuclideanSpace ℝ (Fin d),
      ScaledJetBounds β h (scaledCopy β h z oddEuclidean) C := by
  obtain ⟨C, hC, hf⟩ := oddEuclidean_jetBounds d
  exact ⟨C, hC, fun β h _ _ hh _ z => scaledCopy_jetBounds β h z hf hh⟩

/-- For [every tangent dimension t and complementary dimension c](hyp:t,c)
[there is a constant C ≥ 1 such that for every exponent β with 0 < β ≤ 2, every
bandwidth h with 0 < h ≤ 1 and every center z, the scaled copy
x ↦ h^β·(mixed profile at (x − z)/h) is twice continuously differentiable on the
whole space, with absolute value at most C·h^β, derivative of operator norm at
most C·h^(β−1) and second derivative of operator norm at most C·h^(β−2) at
every point](goal). The constant does not depend on the exponent, bandwidth or
center. -/
theorem mixedProfile_uniform_scaled_bounds (t c : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (β h : ℝ), 0 < β → β ≤ 2 → 0 < h → h ≤ 1 →
      ∀ z : EuclideanSpace ℝ (Fin t ⊕ Fin c),
        ScaledJetBounds β h (scaledCopy β h z mixedProfile) C := by
  obtain ⟨C, hC, hf⟩ := mixedProfile_jetBounds t c
  exact ⟨C, hC, fun β h _ _ hh _ z => scaledCopy_jetBounds β h z hf hh⟩

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
