module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Fourier

/-!
# Bridge from Jackson cosine packets to finite complex Fourier sums

The shifted real cosine polynomial is the real part of two modulated finite
complex Fourier polynomials. This lets Abel summation act on its coefficients.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

/-- For [any order N](hyp:N) and [any angle u](hyp:u), [the packet antiderivative equals minus one
half times the sum of two real parts: that of the complex exponential of 4N i u times the Fourier
series of the plus-shifted coefficients at u, and that of the same exponential times the Fourier
series of the minus-shifted coefficients at −u](goal). -/
theorem packetAntideriv_eq_finiteFourier (N : ℕ) (u : ℝ) :
    packetAntideriv N u = -(1 / 2 : ℝ) *
      ((Complex.exp (Complex.I * (4 * (N : ℝ) * u : ℂ)) *
          finiteFourier (fun j => (packetCoeffPlus N j : ℂ)) u).re +
       (Complex.exp (Complex.I * (4 * (N : ℝ) * u : ℂ)) *
          finiteFourier (fun j => (packetCoeffMinus N j : ℂ)) (-u)).re) := by
  let s : Finset ℤ := Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)
  have hout (j : ℤ) (hj : j ∉ s) :
      packetCoeffPlus N j = 0 ∧ packetCoeffMinus N j = 0 := by
    have hj' : ((2 * N - 2 : ℕ) : ℤ) < |j| := by
      simp only [s, Finset.mem_Icc, not_and_or, not_le] at hj
      have ha := le_abs_self j
      have hb := neg_le_abs j
      rcases hj with hj | hj <;> omega
    exact ⟨weightedCoeff_support N 1 j hj', weightedCoeff_support N (-1) j hj'⟩
  have hplus : finiteFourier (fun j => (packetCoeffPlus N j : ℂ)) u =
      ∑ j ∈ s, (packetCoeffPlus N j : ℂ) *
        Complex.exp (Complex.I * (j : ℂ) * (u : ℂ)) := by
    unfold finiteFourier
    apply tsum_eq_sum
    intro j hj
    simp [(hout j hj).1]
  have hminus : finiteFourier (fun j => (packetCoeffMinus N j : ℂ)) (-u) =
      ∑ j ∈ s, (packetCoeffMinus N j : ℂ) *
        Complex.exp (Complex.I * (j : ℂ) * ((-u : ℝ) : ℂ)) := by
    unfold finiteFourier
    apply tsum_eq_sum
    intro j hj
    simp [(hout j hj).2]
  have hphase (c : ℝ) (j : ℤ) (v : ℝ) :
      (Complex.exp (Complex.I * (4 * (N : ℝ) * u : ℂ)) *
        ((c : ℂ) * Complex.exp (Complex.I * (j : ℂ) * (v : ℂ)))).re =
        c * Real.cos ((4 * (N : ℝ) * u) + (j : ℝ) * v) := by
    rw [show Complex.exp (Complex.I * (4 * (N : ℝ) * u : ℂ)) *
          ((c : ℂ) * Complex.exp (Complex.I * (j : ℂ) * (v : ℂ))) =
          (c : ℂ) * Complex.exp (((4 * (N : ℝ) * u) + (j : ℝ) * v : ℝ) *
            Complex.I) by
      calc
        _ = (c : ℂ) * (Complex.exp (Complex.I * (4 * (N : ℝ) * u : ℂ)) *
              Complex.exp (Complex.I * (j : ℂ) * (v : ℂ))) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 1
          apply congrArg Complex.exp
          push_cast
          ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  rw [hplus, hminus]
  simp only [Finset.mul_sum, Complex.re_sum]
  unfold packetAntideriv
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hphase (packetCoeffPlus N j) j u,
      hphase (packetCoeffMinus N j) j (-u)]
  congr 1 <;> congr 1 <;> push_cast <;> ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

