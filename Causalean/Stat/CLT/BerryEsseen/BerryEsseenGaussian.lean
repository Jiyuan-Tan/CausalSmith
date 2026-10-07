module
public import Mathlib.Probability.CentralLimitTheorem

/-! # Quadratic approximation of the Gaussian characteristic function

The characteristic function exp(−t²/2) of the standard normal law differs from its second-order
Taylor polynomial 1 − t²/2 by at most t⁴/8, for every real t. This is the Gaussian half of the
local characteristic-function comparison in the Berry–Esseen proof: near the origin, both the
characteristic function of a standardized law and that of the normal law are compared with the
same quadratic.

## Main results

* `gaussian_charFun_quadratic_remainder` — the bound |exp(−t²/2) − (1 − t²/2)| ≤ t⁴/8, deduced
  from |exp(−u) − (1 − u)| ≤ u²/2 for u ≥ 0.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- [The standard Gaussian characteristic function differs from its quadratic
Taylor polynomial 1 − t²/2 by at most t⁴/8 at every real frequency t](goal). -/
theorem gaussian_charFun_quadratic_remainder (t : ℝ) :
    ‖charFun (gaussianReal 0 1) t -
      ((1 : ℂ) - (t : ℂ) ^ 2 / 2)‖ ≤ |t| ^ 4 / 8 := by
  have hrem (u : ℝ) (hu : 0 ≤ u) :
      |Real.exp (-u) - (1 - u)| ≤ u ^ 2 / 2 := by
    have hlow : 0 ≤ Real.exp (-u) - (1 - u) := by
      linarith [Real.one_sub_le_exp_neg u]
    have hpoly : 0 ≤ 1 - u + u ^ 2 / 2 := by
      nlinarith [sq_nonneg (u - 1)]
    have hmul : 1 ≤ (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) := by
      nlinarith [sq_nonneg (u ^ 2)]
    have hquad := Real.quadratic_le_exp_of_nonneg hu
    have hprod : 1 ≤ (1 - u + u ^ 2 / 2) * Real.exp u :=
      le_trans hmul (mul_le_mul_of_nonneg_left hquad hpoly)
    have hupr : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
      rw [Real.exp_neg]
      simpa only [one_div] using (div_le_iff₀ (Real.exp_pos u)).2 hprod
    rw [abs_of_nonneg hlow]
    linarith
  have heq : charFun (gaussianReal 0 1) t -
      ((1 : ℂ) - (t : ℂ) ^ 2 / 2) =
      ((Real.exp (-(t ^ 2 / 2)) - (1 - t ^ 2 / 2) : ℝ) : ℂ) := by
    simp [charFun_gaussianReal]
  rw [heq, Complex.norm_real]
  have h := hrem (t ^ 2 / 2) (by positivity)
  calc
    |Real.exp (-(t ^ 2 / 2)) - (1 - t ^ 2 / 2)| ≤ (t ^ 2 / 2) ^ 2 / 2 := h
    _ = |t| ^ 4 / 8 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t ^ 4)]
      ring

end Causalean.Stat.CLT.BerryEsseen
