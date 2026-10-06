module
public import Causalean.Stat.CLT.BerryEsseen.EsseenUnitRawWitness

/-! # Unit-bandwidth one-sided spectral comparison

This module isolates the sharp analytic kernel construction at bandwidth one,
unit downward slope, and the origin. Translation and rescaling belong to the
general spectral comparison module.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [an integrable real function H](hyp:hH) whose
[downward increments are at most the distance between its arguments](hyp:hdown)
and [any positive tolerance ε](hyp:hε), [there is a continuous integrable
kernel K with integrable Fourier transform that vanishes outside (−1, 1) and
has magnitude at most one, such that y ↦ H(−y)·K(y) is integrable and H(0)
is at most twice the absolute value of its integral plus 24/π + ε](goal). -/
theorem exists_esseen_unit_spectral_comparator
    (H : ℝ → ℝ) (hH : Integrable H volume)
    (hdown : ∀ a b : ℝ, a ≤ b → H a ≤ H b + (b - a))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ → ℝ,
      Integrable K volume ∧ Continuous K ∧
      Integrable (fun t : ℝ =>
        ∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) volume ∧
      (∀ t : ℝ, 1 ≤ |t| →
        (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0) ∧
      (∀ t : ℝ,
        ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1) ∧
      Integrable (fun y : ℝ => H (-y) * K y) volume ∧
      H 0 ≤ 2 * |∫ y : ℝ, H (-y) * K y| + 24 / Real.pi + ε := by
  obtain ⟨K, hKi, hKc, hsupp, hnorm, hpoint⟩ :=
    exists_esseen_unit_raw_spectral_witness H hH hdown ε hε
  exact ⟨K, hKi, hKc,
    integrable_unit_supported_kernel_fourier K hKi hsupp hnorm,
    hsupp, hnorm,
    integrable_reflected_mul_unit_supported_kernel H K hH hKi hKc hsupp hnorm,
    hpoint⟩

end Causalean.Stat.CLT.BerryEsseen
