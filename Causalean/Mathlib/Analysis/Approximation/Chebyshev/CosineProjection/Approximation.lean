module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Convolution
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.JacksonError
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Span

/-!
# The even Jackson approximant in the cosine span

Use convolution of the even periodic extension against the existing
Jackson kernel, defined in JacksonError. Finite-degree membership and uniform
Hölder error are separate obligations: no spectral approximation result is
assumed in the definition.
-/

public section

noncomputable section
open MeasureTheory
open Causalean.Mathlib.Analysis.JacksonApproximation
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- At a [positive order](hyp:hK), a [target continuous on the closed
interval](hyp:hf) has [Jackson approximant in the cosine span through
degree twice the predecessor of its order](goal).

Use `jackson_isTrigPolyLE`, `even_trigPoly_cosine`, and
`angularConvolution_cosine_expansion` for the folded extension. Its continuity,
evenness and periodicity follow from Fold; the generic convolution helpers
in Convolution isolate the integration-window and odd-integral obligations.
Rescale nonzero coefficients by √2, keeping the constant coefficient separate.
The change of window is a theorem in Convolution, not a definitional equality.
-/
theorem jacksonApproximant_mem_span {K : ℕ} {f : ℝ → ℝ}
    (hK : 0 < K) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    InCosineSpan (2 * (K - 1) + 1) (jacksonApproximant K f) := by
  classical
  obtain ⟨a, ha⟩ := even_trigPoly_cosine (jackson_isTrigPolyLE K hK) (jackson_even K)
  let b : ℕ → ℝ := fun j =>
    a j * ∫ t in Set.Icc (-Real.pi) Real.pi,
      evenExtension f t * Real.cos ((j : ℝ) * t)
  refine ⟨fun j => if j = 0 then b j else b j / Real.sqrt 2, ?_⟩
  intro x hx
  change angularConvolution (evenExtension f) (jackson K) (Real.pi * x) = _
  rw [angularConvolution_cosine_expansion (continuous_evenExtension hf)
    (evenExtension_even f) (evenExtension_periodic f) a ha]
  unfold cosinePolynomial
  apply Finset.sum_congr rfl
  intro j hj
  change b j * Real.cos ((j : ℝ) * (Real.pi * x)) = _
  by_cases hzero : j = 0
  · subst j
    simp [cosineBasis]
  · simp only [cosineBasis, hzero, if_false]
    rw [show (j : ℝ) * (Real.pi * x) = Real.pi * (j : ℝ) * x by ring]
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp

/-- For a [positive rank](hyp:hk), a [continuous target](hyp:hf), an
[exponent between zero and one](hyp:hγ,hγ1), and a [nonnegative Hölder
bound](hyp:hH,hholder), [there is a continuous rank-k cosine approximant
with uniform error at most five times the Hölder constant times k⁻γ](goal).

Choose K=(k+1)/2 in the previous results and zero-pad the coefficient sequence.
This covers odd and even ranks, including rank one.
-/
theorem exists_cosine_approximant {k : ℕ} {f : ℝ → ℝ} {γ H : ℝ}
    (hk : 1 ≤ k) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H) (hholder : HasHolderBound f γ H) :
    ∃ p : ℝ → ℝ, ContinuousOn p (Set.Icc (0 : ℝ) 1) ∧ InCosineSpan k p ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - p x| ≤ 5 * H * (k : ℝ) ^ (-γ) := by
  let K : ℕ := (k + 1) / 2
  have hK : 0 < K := (matchedOrder_bounds hk).1
  refine ⟨jacksonApproximant K f, (continuous_jacksonApproximant hf).continuousOn,
    inCosineSpan_mono (by have := (matchedOrder_bounds hk).2; omega)
      (jacksonApproximant_mem_span hK hf), ?_⟩
  intro x hx
  calc
    _ ≤ H * (2 / (K : ℝ)) ^ γ :=
      jacksonApproximant_error hK hf hγ hγ1 hH hholder hx
    _ ≤ H * (5 * (k : ℝ) ^ (-γ)) :=
      mul_le_mul_of_nonneg_left (matchedOrder_constant_five hk hγ hγ1) hH
    _ = _ := by ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

