module
public import Causalean.Stat.CLT.BerryEsseen.EsseenSignedKernelComparison
public import Causalean.Stat.CLT.BerryEsseen.EsseenSignedKernelFourier
public import Causalean.Stat.CLT.BerryEsseen.EsseenSignedKernelFourierNorm
public import Causalean.Stat.CLT.BerryEsseen.EsseenSinc4FirstMoment
public import Causalean.Stat.CLT.BerryEsseen.EsseenSinc4SecondMoment
public import Causalean.Stat.CLT.BerryEsseen.EsseenUnitRegularity
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Sharp unit-bandwidth spectral witness

This isolates the genuine one-sided approximation step. Kernel regularity
consequences of spectral support are supplied by `EsseenUnitRegularity`.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [an integrable real function H](hyp:hH) whose
[downward increments are at most the distance between its arguments](hyp:hdown)
and [any positive tolerance ε](hyp:hε), [there is a continuous integrable
kernel K whose Fourier transform vanishes outside (−1, 1) and has magnitude
at most one, such that H(0) is at most twice the absolute value of the
integral of H(−y)·K(y) plus 24/π + ε](goal). -/
theorem exists_esseen_unit_raw_spectral_witness
    (H : ℝ → ℝ) (hH : Integrable H volume)
    (hdown : ∀ a b : ℝ, a ≤ b → H a ≤ H b + (b - a))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ → ℝ,
      Integrable K volume ∧ Continuous K ∧
      (∀ t : ℝ, 1 ≤ |t| →
        (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0) ∧
      (∀ t : ℝ,
        ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1) ∧
      H 0 ≤ 2 * |∫ y : ℝ, H (-y) * K y| + 24 / Real.pi + ε := by
  let K := esseenSignedSinc4Kernel
  obtain ⟨hKint, hKcont⟩ := esseenSignedSinc4Kernel_integrable_continuous
  have hsupp : ∀ t : ℝ, 1 ≤ |t| →
      (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0 :=
    fun t ht => esseenSignedSinc4Kernel_fourier_eq_zero t ht
  have hnorm : ∀ t : ℝ,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1 :=
    esseenSignedSinc4Kernel_fourier_norm_le_one
  have hprod : Integrable (fun y : ℝ => H (-y) * K y) volume :=
    integrable_reflected_mul_unit_supported_kernel H K hH hKint hKcont hsupp hnorm
  have hcomp := esseenSignedSinc4Kernel_comparison H hdown hprod
  have hpi : (7 : ℝ) ≤ 24 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d2]
  refine ⟨K, hKint, hKcont, hsupp, hnorm, ?_⟩
  linarith

end Causalean.Stat.CLT.BerryEsseen
