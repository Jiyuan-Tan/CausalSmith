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

/-- In [fixed tangent and complementary dimensions](hyp:t,c), [one fixed constant bounds
all scaled mixed-profile jets](goal), uniformly over exponents in `(0,2]`, bandwidths
in `(0,1]`, and centers. -/
theorem mixedProfile_uniform_scaled_bounds (t c : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (β h : ℝ), 0 < β → β ≤ 2 → 0 < h → h ≤ 1 →
      ∀ z : EuclideanSpace ℝ (Fin t ⊕ Fin c),
        ScaledJetBounds β h (scaledCopy β h z mixedProfile) C := by
  obtain ⟨C, hC, hf⟩ := mixedProfile_jetBounds t c
  exact ⟨C, hC, fun β h _ _ hh _ z => scaledCopy_jetBounds β h z hf hh⟩

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
