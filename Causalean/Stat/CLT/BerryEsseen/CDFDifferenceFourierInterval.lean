module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierKernel

/-! # Lebesgue integral of the oriented Fourier kernel

This module evaluates the oriented interval kernel in its Lebesgue variable.
It is the other input to the CDF Fourier Fubini interchange.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- [Integrating the oriented Fourier kernel over the real line gives the
oriented interval integral of the Fourier exponential exp(itx) from a to
b](goal). -/
theorem orientedFourierKernel_interval_integral
    (t a b : ℝ) :
    (∫ x : ℝ, orientedFourierKernel t a b x) =
      ∫ x in a..b, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
  let f : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  rcases le_total a b with hab | hba
  · have hkernel : orientedFourierKernel t a b = (Set.Ico a b).indicator f := by
      funext x
      by_cases hax : a ≤ x <;> by_cases hbx : b ≤ x
      all_goals simp [orientedFourierKernel, f, Set.indicator_apply, Set.mem_Ico,
        hax, hbx]
      exact hax (hab.trans hbx)
    rw [hkernel, integral_indicator measurableSet_Ico]
    rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioc]
  · have hkernel : orientedFourierKernel t a b = -(Set.Ico b a).indicator f := by
      funext x
      by_cases hax : a ≤ x <;> by_cases hbx : b ≤ x
      all_goals simp [orientedFourierKernel, f, Set.indicator_apply, Set.mem_Ico,
        hax, hbx]
      exact hbx (hba.trans hax)
    rw [hkernel]
    simp only [Pi.neg_apply, integral_neg, integral_indicator measurableSet_Ico]
    rw [intervalIntegral.integral_of_ge hba, integral_Ico_eq_integral_Ioc]

end Causalean.Stat.CLT.BerryEsseen
