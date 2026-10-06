module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Variation

/-!
# Mass of the normalized Jackson coefficients

The nonnegative finite convolution has coefficient mass proportional to its
order. This supplies the lower mass estimate needed at the center of a packet.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

/-- For [an order N](hyp:N) that is [at least two](hyp:hN), [the sum over all integers of the
absolute values of the normalized Jackson coefficients is at least N / 2](goal). -/
theorem normalizedCoeff_l1_lower (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) / 2 ≤ ∑' j : ℤ, |normalizedCoeff N j| := by
  have hNpos : 0 < N := by omega
  have htri (j : ℤ) : 0 ≤ triangle N j := Nat.cast_nonneg _
  have hconv (j : ℤ) : 0 ≤ convolution N j := by
    unfold convolution
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (htri k) (htri (j - k))
  have htriMass : (∑' j : ℤ, triangle N j) = (N : ℝ) ^ 2 := by
    simpa only [abs_of_nonneg (htri _)] using triangle_l1 N
  have hpair := triangle_pair_sum_eq_convolution N hNpos 0
  simp only [mul_zero, Real.cos_zero, mul_one] at hpair
  have hmass : (∑' j : ℤ, |convolution N j|) = (N : ℝ) ^ 4 := by
    rw [tsum_eq_sum (s := Finset.Icc (-((2 * N - 2 : ℕ) : ℤ))
      ((2 * N - 2 : ℕ) : ℤ))]
    · simp_rw [abs_of_nonneg (hconv _)]
      rw [← hpair]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      have hsum : (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), triangle N k) =
          (N : ℝ) ^ 2 := by
        rw [← htriMass]
        symm
        apply tsum_eq_sum
        intro k hk
        have : (N : ℤ) ≤ |k| := by
          simp only [Finset.mem_Icc] at hk
          rcases le_total k 0 with h | h
          · rw [abs_of_nonpos h]
            omega
          · rw [abs_of_nonneg h]
            omega
        exact triangle_support N k this
      rw [hsum]
      ring
    · intro j hj
      have hfar : ((2 * N - 2 : ℕ) : ℤ) < |j| := by
        simp only [Finset.mem_Icc] at hj
        rcases le_total j 0 with h | h
        · rw [abs_of_nonpos h]
          omega
        · rw [abs_of_nonneg h]
          omega
      simp [convolution_support N j hfar]
  have hpos := convolution_zero_pos N hNpos
  have hscale : (∑' j : ℤ, |normalizedCoeff N j|) =
      (∑' j : ℤ, |convolution N j|) / convolution N 0 := by
    simp_rw [normalizedCoeff, abs_div, abs_of_pos hpos, div_eq_mul_inv]
    rw [tsum_mul_right]
  rw [hscale, hmass, convolution_zero N hNpos]
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < (2 * (N : ℝ) ^ 3 + N) / 3 := by positivity
  apply (le_div_iff₀ hd).2
  have hs : 1 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hp : 0 ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 - 1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [hp]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

