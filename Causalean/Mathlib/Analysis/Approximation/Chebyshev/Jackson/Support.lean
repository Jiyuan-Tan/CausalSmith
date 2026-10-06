module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Fourier

/-!
# Shifted Fourier support of Jackson packets

The modulated Jackson kernel has Fourier support in two frequency bands away
from zero. This module provides the integral formulation for real modes.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

open MeasureTheory

/-- For [an order N](hyp:N) that is [at least two](hyp:hN) and [an integer frequency r](hyp:r)
[whose absolute value is either less than 2N + 2 or greater than 6N − 2](hyp:hr), [the integrals
over the period from −π to π of the oscillatory Jackson packet against both the cosine and the sine
of r u are zero](goal). -/
theorem packet_shifted_support (N : ℕ) (hN : 2 ≤ N) (r : ℤ)
    (hr : |r| < (2 * N + 2 : ℕ) ∨ (6 * N - 2 : ℕ) < |r|) :
    (∫ u in Set.Icc (-Real.pi) Real.pi,
      packetOscillation N u * Real.cos ((r : ℝ) * u)) = 0 ∧
    (∫ u in Set.Icc (-Real.pi) Real.pi,
      packetOscillation N u * Real.sin ((r : ℝ) * u)) = 0 := by
  let s : Finset ℤ := Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)
  have hfreq (j : ℤ) (hj : j ∈ s) :
      |4 * (N : ℤ) + j| ≠ |r| ∧ |4 * (N : ℤ) - j| ≠ |r| := by
    have hb : -(2 * (N : ℤ) - 2) ≤ j ∧ j ≤ 2 * (N : ℤ) - 2 := by
      change j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ) at hj
      simp only [Finset.mem_Icc] at hj
      omega
    have hp : 0 ≤ 4 * (N : ℤ) + j := by omega
    have hm : 0 ≤ 4 * (N : ℤ) - j := by omega
    rw [abs_of_nonneg hp, abs_of_nonneg hm]
    rcases hr with hr | hr <;> constructor <;> omega
  have hsin (m : ℤ) :
      (∫ u in Set.Icc (-Real.pi) Real.pi, Real.sin ((m : ℝ) * u)) = 0 := by
    by_cases hm : m = 0
    · subst m; simp
    · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
          (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      rw [intervalIntegral.integral_comp_mul_left Real.sin hm0, integral_sin]
      simp [mul_neg, Real.cos_neg]
  have hmix (k : ℤ) :
      (∫ u in Set.Icc (-Real.pi) Real.pi,
        Real.cos ((k : ℝ) * u) * Real.sin ((r : ℝ) * u)) = 0 := by
    have hp (u : ℝ) :
        Real.cos ((k : ℝ) * u) * Real.sin ((r : ℝ) * u) =
          (Real.sin (((r + k : ℤ) : ℝ) * u) +
            Real.sin (((r - k : ℤ) : ℝ) * u)) / 2 := by
      rw [show (((r + k : ℤ) : ℝ) * u) = (r : ℝ) * u + (k : ℝ) * u by
          push_cast; ring,
        show (((r - k : ℤ) : ℝ) * u) = (r : ℝ) * u - (k : ℝ) * u by
          push_cast; ring,
        Real.sin_add, Real.sin_sub]
      ring
    simp_rw [hp]
    rw [MeasureTheory.integral_div]
    rw [MeasureTheory.integral_add
      ((show Continuous (fun u : ℝ => Real.sin (((r + k : ℤ) : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc)
      ((show Continuous (fun u : ℝ => Real.sin (((r - k : ℤ) : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc)]
    rw [hsin, hsin]
    ring
  have hfourier (u : ℝ) : packetOscillation N u =
      ∑ j ∈ s, normalizedCoeff N j *
        ((Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
          Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u)) / 2) := by
    rw [packetOscillation, packet_kernel_reconstruction N (by omega : 0 < N) u]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (4 * N : ℝ) * u = ((4 * (N : ℤ) : ℤ) : ℝ) * u by
      push_cast; ring]
    rw [show (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) =
      ((4 * (N : ℤ) : ℤ) : ℝ) * u + (j : ℝ) * u by push_cast; ring,
      show (((4 * (N : ℤ) - j : ℤ) : ℝ) * u) =
      ((4 * (N : ℤ) : ℤ) : ℝ) * u - (j : ℝ) * u by push_cast; ring,
      Real.cos_add, Real.cos_sub]
    ring
  have hint (j : ℤ) (f : ℝ → ℝ) (hf : Continuous f) :
      IntegrableOn (fun u : ℝ => normalizedCoeff N j *
        ((Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
          Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u)) / 2) * f u)
        (Set.Icc (-Real.pi) Real.pi) := by
    exact (show Continuous (fun u : ℝ => normalizedCoeff N j *
      ((Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
        Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u)) / 2) * f u) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc
  constructor
  · simp_rw [hfourier, Finset.sum_mul]
    rw [MeasureTheory.integral_finsetSum s (fun j _ =>
      hint j (fun u => Real.cos ((r : ℝ) * u)) (by fun_prop))]
    apply Finset.sum_eq_zero
    intro j hj
    have hp := (hfreq j hj).1
    have hm := (hfreq j hj).2
    have hzero (k : ℤ) (hk : |k| ≠ |r|) :
        (∫ u in Set.Icc (-Real.pi) Real.pi,
          Real.cos ((k : ℝ) * u) * Real.cos ((r : ℝ) * u)) = 0 := by
      have h := cosine_mode_orthogonality k r
      have h00 : ¬ (k = 0 ∧ r = 0) := by
        rintro ⟨rfl, rfl⟩
        exact hk rfl
      simp only [h00, hk, if_false] at h
      exact (mul_eq_zero.mp h).resolve_left (by positivity)
    rw [show (fun u : ℝ => normalizedCoeff N j *
      ((Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
        Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u)) / 2) *
          Real.cos ((r : ℝ) * u)) =
      (fun u : ℝ => normalizedCoeff N j / 2 *
        (Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) * Real.cos ((r : ℝ) * u) +
         Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u) * Real.cos ((r : ℝ) * u))) by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
      ((show Continuous (fun u : ℝ =>
        Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) * Real.cos ((r : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc)
      ((show Continuous (fun u : ℝ =>
        Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u) * Real.cos ((r : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc)]
    rw [hzero _ hp, hzero _ hm]
    ring
  · simp_rw [hfourier, Finset.sum_mul]
    rw [MeasureTheory.integral_finsetSum s (fun j _ =>
      hint j (fun u => Real.sin ((r : ℝ) * u)) (by fun_prop))]
    apply Finset.sum_eq_zero
    intro j hj
    rw [show (fun u : ℝ => normalizedCoeff N j *
      ((Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
        Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u)) / 2) *
          Real.sin ((r : ℝ) * u)) =
      (fun u : ℝ => normalizedCoeff N j / 2 *
        (Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) * Real.sin ((r : ℝ) * u) +
         Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u) * Real.sin ((r : ℝ) * u))) by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
      ((show Continuous (fun u : ℝ =>
        Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) * Real.sin ((r : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc)
      ((show Continuous (fun u : ℝ =>
        Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u) * Real.sin ((r : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc)]
    rw [hmix, hmix]
    ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

