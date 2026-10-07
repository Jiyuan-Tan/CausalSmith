module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Basic

/-!
# A real beta integral with an integer right parameter

This evaluates the beta integral needed after derivatives have been
transferred from a Rodrigues kernel onto a reciprocal weight.
-/

public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open MeasureTheory intervalIntegral

/-- A [nonnegative integer power](hyp:k) and [positive real shape parameter](hyp:α), with [parameter positivity](hyp:hα), give [the beta integral identity: the integral of x^(α−1)·(1−x)^k over the unit interval equals k! divided by α times the rising factorial (α+1)ₖ](goal).

For positive `α`, integrating `x^(α-1) (1-x)^k` over `[0,1]` gives
`k! / (α (α+1)ₖ)`.  This is the real, integer-parameter beta identity. -/
theorem integral_rpow_mul_one_sub_pow (k : ℕ) (α : ℝ) (hα : 0 < α) :
    (∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ k) =
      (Nat.factorial k : ℝ) / (α * rising (α + 1) k) := by
  have hprod (n : ℕ) :
      ∏ j ∈ Finset.range (n + 1), ((α : ℂ) + j) =
        ((α * rising (α + 1) n : ℝ) : ℂ) := by
    induction n with
    | zero => simp [rising]
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        simp only [rising, ascPochhammer_succ_eval]
        push_cast
        ring
  have hbeta :
      (∫ x in (0 : ℝ)..1, ((x ^ (α - 1) * (1 - x) ^ k : ℝ) : ℂ)) =
        Complex.betaIntegral (α : ℂ) (k + 1) := by
    rw [Complex.betaIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := by simpa using hx.1
    have hx1 : x ≤ 1 := by simpa using hx.2
    dsimp
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow hx0,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
      add_sub_cancel_right, Complex.cpow_natCast]
  have heval := Complex.betaIntegral_eval_nat_add_one_right
    (u := (α : ℂ)) (by simpa using hα) k
  rw [← hbeta, hprod] at heval
  rw [intervalIntegral.integral_ofReal] at heval
  exact Complex.ofReal_inj.mp
    (by simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using heval)

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
