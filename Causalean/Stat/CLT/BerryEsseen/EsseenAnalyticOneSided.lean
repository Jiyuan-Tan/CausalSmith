module
public import Causalean.Stat.CLT.BerryEsseen.EsseenSpectralComparison
public import Mathlib.Analysis.Fourier.Inversion

/-! # Analytic one-sided Esseen inequality

This separates the band-limited comparison with constant 24/π for an integrable real
function from the measure-specific CDF and characteristic-function identities.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [an integrable real function H](hyp:hH) whose
[downward increments are bounded by a nonnegative constant L times the
distance](hyp:hL,hdown) and
[a positive bandwidth T](hyp:hT), [the value of H at every point is at most
1/π times the integral over [−T, T] of the magnitude of its Fourier
transform, plus the one-sided Esseen smoothing error 24L/(πT)](goal). -/
theorem integrable_one_sided_esseen_fourier_bound
    (H : ℝ → ℝ) (hH : Integrable H volume)
    (L : ℝ) (hL : 0 ≤ L)
    (hdown : ∀ a b : ℝ, a ≤ b → H a ≤ H b + L * (b - a))
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    H x ≤
      (1 / Real.pi) *
        (∫ t in (-T)..T,
          ‖∫ y : ℝ,
            Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (H y : ℂ)‖) +
      24 * L / (Real.pi * T) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨K, hKi, hKc, hKhat, hsupp, hnorm, _, hpoint⟩ :=
    exists_esseen_one_sided_spectral_comparator H hH L hL hdown T hT x ε hε
  have hbound := bandlimited_convolution_fourier_bound
    H K hH hKi hKc hKhat T hT hsupp hnorm x
  have hcoeff : 2 * (1 / (2 * Real.pi)) = 1 / Real.pi := by
    field_simp [Real.pi_ne_zero]
  calc
    H x ≤ 2 * |∫ y : ℝ, H (x - y) * K y| +
        24 * L / (Real.pi * T) + ε := hpoint
    _ ≤ 2 * ((1 / (2 * Real.pi)) *
        (∫ t in (-T)..T,
          ‖∫ y : ℝ,
            Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (H y : ℂ)‖)) +
        24 * L / (Real.pi * T) + ε := by gcongr
    _ = (1 / Real.pi) *
        (∫ t in (-T)..T,
          ‖∫ y : ℝ,
            Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (H y : ℂ)‖) +
        24 * L / (Real.pi * T) + ε := by rw [← mul_assoc, hcoeff]

end Causalean.Stat.CLT.BerryEsseen
