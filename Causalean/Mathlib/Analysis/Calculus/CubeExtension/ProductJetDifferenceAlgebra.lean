module
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Bilinear sum differences

This finite-sum estimate is the algebraic step in comparing two evaluations of
a Leibniz expansion. It applies to any contractive continuous bilinear map,
including multiplication and the multilinear contractions in product jets.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [a continuous bilinear map B has operator norm at most one](hyp:hB) and
[the coefficients c_i are nonnegative on a finite index set t](hyp:hc), then
[the norm of the difference between Σ_{i ∈ t} c_i·B(a_i, b_i) and
Σ_{i ∈ t} c_i·B(a'_i, b'_i) is at most
Σ_{i ∈ t} c_i·(‖a_i − a'_i‖·‖b_i‖ + ‖a'_i‖·‖b_i − b'_i‖)](goal).

For each summand, write `B a b - B a' b'` as `B (a-a') b + B a' (b-b')`; then
apply the bilinear operator norm and the triangle inequality before summing. -/
theorem norm_bilinear_sum_sub_le
    {ι E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    (t : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ t, 0 ≤ c i)
    (a a' : ι → E) (b b' : ι → F) :
    ‖∑ i ∈ t, c i • B (a i) (b i) -
        ∑ i ∈ t, c i • B (a' i) (b' i)‖ ≤
      ∑ i ∈ t, c i *
        (‖a i - a' i‖ * ‖b i‖ + ‖a' i‖ * ‖b i - b' i‖) := by
  have hbil (x : E) (y : F) : ‖B x y‖ ≤ ‖x‖ * ‖y‖ := by
    simpa using B.le_of_opNorm₂_le_of_le hB (le_refl ‖x‖) (le_refl ‖y‖)
  have hterm (i : ι) :
      ‖B (a i) (b i) - B (a' i) (b' i)‖ ≤
        ‖a i - a' i‖ * ‖b i‖ + ‖a' i‖ * ‖b i - b' i‖ := by
    have hsplit : B (a i) (b i) - B (a' i) (b' i) =
        B (a i - a' i) (b i) + B (a' i) (b i - b' i) := by
      simp only [map_sub, sub_apply]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hbil _ _) (hbil _ _))
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ t, (c i • B (a i) (b i) - c i • B (a' i) (b' i))‖ ≤
        ∑ i ∈ t, ‖c i • B (a i) (b i) - c i • B (a' i) (b' i)‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ t, c i * ‖B (a i) (b i) - B (a' i) (b' i)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc i hi)]
    _ ≤ ∑ i ∈ t, c i *
          (‖a i - a' i‖ * ‖b i‖ + ‖a' i‖ * ‖b i - b' i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hterm i) (hc i hi)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
