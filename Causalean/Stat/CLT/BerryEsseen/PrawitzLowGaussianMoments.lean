module
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-! # Gaussian moment allocation for small Prawitz ratios

This elementary real integral controls a polynomial Gaussian majorant of
the low-frequency Prawitz contribution when the moment ratio is at most
one hundredth. It is a helper case, not a replacement for the full budget.
No characteristic-function or smoothing theorem is a premise.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a positive ratio ρ at most one hundredth](hyp:ρ,hρ,hsmall),
[the integral over t > 0 of the polynomial Gaussian low-frequency majorant
(ρt²/(6π) + ρ²t³/(8π) + 5ρ²t³/72 + 5ρ³t⁴/96)·exp(−23t²/100) is at most one
quarter of ρ](goal). -/
theorem prawitz_low_gaussian_moment_budget
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ ≤ 1 / 100) :
    (∫ t in Set.Ioi (0 : ℝ),
      (ρ * t ^ 2 / (6 * Real.pi) +
        ρ ^ 2 * t ^ 3 / (8 * Real.pi) +
        5 * ρ ^ 2 * t ^ 3 / 72 + 5 * ρ ^ 3 * t ^ 4 / 96) *
        Real.exp (-(23 * t ^ 2 / 100))) ≤ ρ / 4 := by
  /- Evaluate the second, third, and fourth Gaussian moments with Mathlib's
  integral_rpow_mul_exp_neg_mul_rpow (p=2) and the Gamma half-integer
  identities. Prove integrability before splitting the integral. Bound the
  resulting constants using rational pi/sqrt bounds, and use ρ≤1/100.
  The coefficient after division by ρ is below .224 throughout this case;
  that numerical observation is guidance, never a certificate.

  Connection to the unchanged low budget: log(1/ρ)≤1/ρ-1 gives
  ρ*U0≤1/5 for ρ≤1/100. Thus on [0,U0] the Taylor envelope is at most its
  polynomial times exp(-23t²/100). The proven kernel bound gives
  (2/U)*‖K(t/U)‖≤1/(πt)+5ρ/12 for t>0. Expanding their product gives
  exactly this nonsingular polynomial. Endpoint integrability and that
  comparison, followed by nonnegative integral restriction, remain to be
  assembled in PrawitzBudgetLow. The complementary ρ>1/100 case still
  requires a separate compact-parameter certificate using the min envelope.
  Do not claim this lemma alone proves prawitz_budget_low. -/
  let b : ℝ := 23 / 100
  have hb : 0 < b := by norm_num [b]
  have hint (n : ℕ) : IntegrableOn
      (fun t : ℝ => t ^ n * Real.exp (-b * t ^ 2)) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_two] using
      (integrableOn_rpow_mul_exp_neg_mul_sq (s := (n : ℝ)) hb (by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith))
  have heval (n : ℕ) : (∫ t in Set.Ioi (0 : ℝ), t ^ n * Real.exp (-b * t ^ 2)) =
      b ^ (-((n : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((n : ℝ) + 1) / 2) := by
    simpa only [Real.rpow_natCast, Real.rpow_two] using
      (integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ))
        (by norm_num) (by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith) hb)
  have hg3 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  have hg5 : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0), hg3]
    ring
  have hr3 : b ^ (-(3 / 2 : ℝ)) = (b * Real.sqrt b)⁻¹ := by
    rw [Real.rpow_neg hb.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hb, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hr5 : b ^ (-(5 / 2 : ℝ)) = (b ^ 2 * Real.sqrt b)⁻¹ := by
    rw [Real.rpow_neg hb.le, show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num,
      Real.rpow_add hb, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : 47 / 100 ≤ Real.sqrt b := by
    have := Real.sq_sqrt hb.le
    have := Real.sqrt_nonneg b
    dsimp [b] at *
    nlinarith
  have hsp : Real.sqrt Real.pi ≤ 9 / 5 := by
    have := Real.sq_sqrt Real.pi_pos.le
    have := Real.sqrt_nonneg Real.pi
    nlinarith [Real.pi_lt_d2]
  have h2 : (∫ t in Set.Ioi (0 : ℝ), t ^ 2 * Real.exp (-b * t ^ 2)) ≤ 21 / 5 := by
    rw [heval]
    rw [show (-((2 : ℕ) + 1 : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num,
      show (((2 : ℕ) + 1 : ℝ) / 2) = (3 / 2 : ℝ) by norm_num]
    rw [hr3, hg3]
    have hden : 0 < b * Real.sqrt b := by positivity
    have heq : (b * Real.sqrt b)⁻¹ * (1 / 2) * (Real.sqrt Real.pi / 2) =
        Real.sqrt Real.pi / (4 * b * Real.sqrt b) := by
      field_simp
      norm_num
    rw [heq]
    apply (div_le_iff₀ (by positivity)).2
    dsimp [b] at *
    nlinarith
  have h3 : (∫ t in Set.Ioi (0 : ℝ), t ^ 3 * Real.exp (-b * t ^ 2)) ≤ 10 := by
    rw [heval]
    norm_num [b, Real.rpow_neg, Real.rpow_natCast, Real.Gamma_nat_eq_factorial]
  have h4 : (∫ t in Set.Ioi (0 : ℝ), t ^ 4 * Real.exp (-b * t ^ 2)) ≤ 30 := by
    rw [heval]
    rw [show (-((4 : ℕ) + 1 : ℝ) / 2) = -(5 / 2 : ℝ) by norm_num,
      show (((4 : ℕ) + 1 : ℝ) / 2) = (5 / 2 : ℝ) by norm_num]
    rw [hr5, hg5]
    have heq : (b ^ 2 * Real.sqrt b)⁻¹ * (1 / 2) * (3 * Real.sqrt Real.pi / 4) =
        3 * Real.sqrt Real.pi / (8 * b ^ 2 * Real.sqrt b) := by
      field_simp
      norm_num
    rw [heq]
    apply (div_le_iff₀ (by positivity)).2
    dsimp [b] at *
    nlinarith
  have hsplit : (∫ t in Set.Ioi (0 : ℝ),
      (ρ * t ^ 2 / (6 * Real.pi) + ρ ^ 2 * t ^ 3 / (8 * Real.pi) +
        5 * ρ ^ 2 * t ^ 3 / 72 + 5 * ρ ^ 3 * t ^ 4 / 96) * Real.exp (-(23 * t ^ 2 / 100))) =
      (ρ / (6 * Real.pi)) * (∫ t in Set.Ioi (0 : ℝ), t ^ 2 * Real.exp (-b * t ^ 2)) +
      (ρ ^ 2 / (8 * Real.pi)) * (∫ t in Set.Ioi (0 : ℝ), t ^ 3 * Real.exp (-b * t ^ 2)) +
      (5 * ρ ^ 2 / 72) * (∫ t in Set.Ioi (0 : ℝ), t ^ 3 * Real.exp (-b * t ^ 2)) +
      (5 * ρ ^ 3 / 96) * (∫ t in Set.Ioi (0 : ℝ), t ^ 4 * Real.exp (-b * t ^ 2)) := by
    have heq : (fun t : ℝ =>
        (ρ * t ^ 2 / (6 * Real.pi) + ρ ^ 2 * t ^ 3 / (8 * Real.pi) +
          5 * ρ ^ 2 * t ^ 3 / 72 + 5 * ρ ^ 3 * t ^ 4 / 96) * Real.exp (-(23 * t ^ 2 / 100))) =
        (fun t : ℝ =>
          (ρ / (6 * Real.pi)) * (t ^ 2 * Real.exp (-b * t ^ 2)) +
          (ρ ^ 2 / (8 * Real.pi)) * (t ^ 3 * Real.exp (-b * t ^ 2)) +
          (5 * ρ ^ 2 / 72) * (t ^ 3 * Real.exp (-b * t ^ 2)) +
          (5 * ρ ^ 3 / 96) * (t ^ 4 * Real.exp (-b * t ^ 2))) := by
      funext t
      dsimp [b]
      rw [show -(23 * t ^ 2 / 100) = -(23 / 100 : ℝ) * t ^ 2 by ring]
      ring
    have hi2 := (hint 2).const_mul (ρ / (6 * Real.pi))
    have hi3 := (hint 3).const_mul (ρ ^ 2 / (8 * Real.pi))
    have hi3' := (hint 3).const_mul (5 * ρ ^ 2 / 72)
    have hi4 := (hint 4).const_mul (5 * ρ ^ 3 / 96)
    rw [heq]
    have hadd4 := integral_add ((hi2.add hi3).add hi3') hi4
    have hadd3 := integral_add (hi2.add hi3) hi3'
    have hadd2 := integral_add hi2 hi3
    simp only [Pi.add_apply] at hadd4 hadd3 hadd2
    rw [hadd4, hadd3, hadd2]
    simp only [integral_const_mul]
  rw [hsplit]
  have hm2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ ρ / (6 * Real.pi))
  have hm3 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ ρ ^ 2 / (8 * Real.pi))
  have hm3' := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 5 * ρ ^ 2 / 72)
  have hm4 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 5 * ρ ^ 3 / 96)
  have hc2 : ρ / (6 * Real.pi) * (21 / 5) ≤ 7 * ρ / 30 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have hc3 : ρ ^ 2 / (8 * Real.pi) * 10 ≤ 5 * ρ ^ 2 / 12 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_three, sq_nonneg ρ]
  have hr2 : ρ ^ 2 ≤ ρ / 100 := by nlinarith
  have hr3 : ρ ^ 3 ≤ ρ / 10000 := by
    have hm := mul_le_mul_of_nonneg_right hr2 hρ.le
    nlinarith
  nlinarith


end Causalean.Stat.CLT.BerryEsseen
