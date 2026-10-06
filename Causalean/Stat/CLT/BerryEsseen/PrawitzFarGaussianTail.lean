module
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Far-frequency Gaussian allocation for small Prawitz ratios

This bounded real integral handles the far part of the high-frequency budget
using the coarse global damping bound. The reciprocal weight is nonsingular
throughout this interval. The full high-frequency budget remains a separate
theorem over all ratios strictly between zero and one.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a positive ratio ρ at most one hundredth](hyp:ρ,hρ,hsmall),
[the integral from the reciprocal-ratio cutoff 1/(2ρ) to the fixed outer
cutoff 12/(5ρ) of (1/(πt) + 5ρ/12)·exp(−t²/50) is at most one twentieth of
ρ](goal). -/
theorem prawitz_far_gaussian_tail_budget
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ ≤ 1 / 100) :
    (∫ t in (1 / (2 * ρ))..(12 / (5 * ρ)),
      (1 / (Real.pi * t) + 5 * ρ / 12) *
        Real.exp (-(t ^ 2 / 50))) ≤ ρ / 20 := by
  /- Prove interval integrability by continuity (t stays positive). Bound
  1/(πt)+5ρ/12 by (2/π+5/12)*ρ and the exponential by
  exp(-1/(200ρ²)). The interval length is 19/(10ρ). For q>0,
  exp(q)≥q³/6 gives exp(-q)≤6/q³. At q=1/(200ρ²), the resulting
  bound is (19/10)*(2/π+5/12)*48000000*ρ⁶. After dividing by ρ,
  ρ⁵≤(1/100)⁵ and π>3 certify the stated rational allocation.
  No floating-point quadrature is needed for this helper.

  Connection to PrawitzBudgetHigh: on t≤U=12/(5ρ), the cubic exponent
  -t²/2+ρt³/5 is at most -t²/50. Combine this leaf with
  GaussianWeightedTail for the middle subinterval when ρ≤1/100.
  The complementary ρ>1/100 case still needs its own compact-parameter
  certificate with the actual kernel/envelope. Do not replace the full
  high-budget statement by this helper case. -/
  have hab : 1 / (2 * ρ) ≤ 12 / (5 * ρ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have ha : 0 < 1 / (2 * ρ) := by positivity
  have hf : IntervalIntegrable (fun t : ℝ =>
      (1 / (Real.pi * t) + 5 * ρ / 12) * Real.exp (-(t ^ 2 / 50)))
      volume (1 / (2 * ρ)) (12 / (5 * ρ)) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul
    · apply ContinuousOn.add
      · exact continuousOn_const.div (continuous_const.mul continuous_id).continuousOn
          (fun t ht => ne_of_gt (mul_pos Real.pi_pos (lt_of_lt_of_le ha ht.1)))
      · exact continuousOn_const
    · fun_prop
  have hpoint : ∀ t ∈ Set.Icc (1 / (2 * ρ)) (12 / (5 * ρ)),
      (1 / (Real.pi * t) + 5 * ρ / 12) * Real.exp (-(t ^ 2 / 50)) ≤
        2 * ρ * (48000000 * ρ ^ 6) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hrt : 1 ≤ 2 * ρ * t := by
      have hh := (div_le_iff₀ (by positivity : 0 < 2 * ρ)).1 ht.1
      nlinarith
    have hw : 1 / (Real.pi * t) + 5 * ρ / 12 ≤ 2 * ρ := by
      have hrec' : 1 / (Real.pi * t) ≤ ρ := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [Real.pi_gt_three]
      linarith
    have he : Real.exp (-(t ^ 2 / 50)) ≤ 48000000 * ρ ^ 6 := by
      have hq : 0 < t ^ 2 / 50 := by positivity
      have hex := Real.pow_div_factorial_le_exp (t ^ 2 / 50) hq.le 3
      norm_num at hex
      have hprod : (t ^ 2 / 50) ^ 3 * Real.exp (-(t ^ 2 / 50)) ≤ 6 := by
        have hm := mul_le_mul_of_nonneg_right hex (Real.exp_nonneg (-(t ^ 2 / 50)))
        rw [← Real.exp_add] at hm
        simp only [add_neg_cancel, Real.exp_zero] at hm
        nlinarith
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hrt 6
      have hlower : 1 ≤ 8000000 * ρ ^ 6 * t ^ 6 := by
        nlinarith [hpow]
      have hm := mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ 8000000 * ρ ^ 6)
      have hepos := Real.exp_nonneg (-(t ^ 2 / 50))
      have hl := mul_le_mul_of_nonneg_right hlower hepos
      nlinarith
    exact mul_le_mul hw he (Real.exp_nonneg _) (by positivity)
  have hi := intervalIntegral.integral_mono_on hab hf
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => 2 * ρ * (48000000 * ρ ^ 6)) volume
      (1 / (2 * ρ)) (12 / (5 * ρ))) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hlen : (12 / (5 * ρ) - 1 / (2 * ρ)) *
      (2 * ρ * (48000000 * ρ ^ 6)) = 182400000 * ρ ^ 6 := by
    field_simp
    ring
  rw [hlen] at hi
  have hp := pow_le_pow_left₀ hρ.le hsmall 5
  norm_num at hp
  have hm := mul_le_mul_of_nonneg_right hp hρ.le
  nlinarith [hi]


end Causalean.Stat.CLT.BerryEsseen
