module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Termwise integration of a damped cotangent sine series

Inside the open unit disk the geometric sine series is uniformly absolutely
convergent. This leaf handles that exchange separately from the boundary limit
and separately from evaluation of its elementary Fourier coefficients.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a damping ratio r strictly between zero and one](hyp:r,hr,hr1) and
[any real frequency x](hyp:x), [the damped triangularly weighted sine
coefficients r^(n+1)·∫₀¹ (1 − t)·sin(2π(n+1)t)·sin(2πxt) dt are summable,
and twice their sum equals the weighted integral of the rational Abel kernel
2r·sin(2πt)/(1 − 2r·cos(2πt) + r²) against sin(2πxt)](goal). -/
theorem prawitz_abel_weighted_integral_series
    (x r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => r ^ (n + 1) *
      (∫ t in (0 : ℝ)..1, (1 - t) *
        Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t) *
        Real.sin (2 * Real.pi * x * t))) ∧
    (∫ t in (0 : ℝ)..1, (1 - t) *
      (2 * r * Real.sin (2 * Real.pi * t) /
        (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
      Real.sin (2 * Real.pi * x * t)) =
      2 * (∑' n : ℕ, r ^ (n + 1) *
        (∫ t in (0 : ℝ)..1, (1 - t) *
          Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t) *
          Real.sin (2 * Real.pi * x * t))) := by
  /- Take the imaginary part of the complex geometric sum with ratio
  r*exp(2πit) to evaluate 2*Σ r^(n+1) sin(2π(n+1)t). Denominator positivity
  follows from (1-r)^2+2r(1-cos(2πt))>0. Integrate termwise on [0,1]:
  each weighted summand has norm at most r^(n+1), whose sum is finite.
  Use existing integral_tsum/DCT infrastructure. No boundary limit, reciprocal
  partial fraction identity, or Prawitz sign comparison may be assumed here. -/
  have hgeom (a : ℝ) : HasSum
      (fun n : ℕ => r ^ (n + 1) * Real.sin (((n : ℝ) + 1) * a))
      (r * Real.sin a / (1 - 2 * r * Real.cos a + r ^ 2)) := by
    let q : ℂ := (r : ℂ) * Complex.exp ((a : ℂ) * Complex.I)
    have hq : ‖q‖ < 1 := by
      simpa [q, norm_mul, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
        abs_of_pos hr] using hr1
    have hp (n : ℕ) : q ^ (n + 1) =
        (r ^ (n + 1) : ℝ) *
          Complex.exp ((((n : ℝ) + 1) * a : ℝ) * Complex.I) := by
      dsimp [q]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      congr 1
      simp only [mul_assoc]
    have h := Complex.hasSum_im ((hasSum_geometric_of_norm_lt_one hq).mul_left q)
    have hd : 0 < 1 - 2 * r * Real.cos a + r ^ 2 := by
      have hc := Real.cos_le_one a
      have hrr : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
      nlinarith
    have hnorm : Complex.normSq (1 - q) = 1 - 2 * r * Real.cos a + r ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, q, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        zero_mul, add_zero, sub_zero]
      nlinarith [Real.sin_sq_add_cos_sq a]
    have hv : (q * (1 - q)⁻¹).im =
        r * Real.sin a / (1 - 2 * r * Real.cos a + r ^ 2) := by
      rw [← div_eq_mul_inv, Complex.div_im, hnorm]
      simp only [q, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        zero_mul, add_zero, sub_zero]
      field_simp
      ring
    rw [hv] at h
    convert! h using 1
    funext n
    rw [← pow_succ', hp]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
  let F : ℕ → ℝ → ℝ := fun n t => r ^ (n + 1) *
    ((1 - t) * Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t) *
      Real.sin (2 * Real.pi * x * t))
  let g : ℝ → ℝ := fun t => (1 - t) *
    (r * Real.sin (2 * Real.pi * t) /
      (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
      Real.sin (2 * Real.pi * x * t)
  have hs : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr.le hr1).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hsum (t : ℝ) : HasSum (fun n => F n t) (g t) := by
    have h := (hgeom (2 * Real.pi * t)).mul_left
      ((1 - t) * Real.sin (2 * Real.pi * x * t))
    convert! h using 1
    · funext n
      dsimp [F]
      rw [show 2 * Real.pi * ((n : ℝ) + 1) * t =
        ((n : ℝ) + 1) * (2 * Real.pi * t) by ring]
      ring
    · dsimp [g]; ring
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      ‖F n t‖ ≤ r ^ (n + 1) := by
    change ‖r ^ (n + 1) *
      ((1 - t) * Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t) *
        Real.sin (2 * Real.pi * x * t))‖ ≤ r ^ (n + 1)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.le _)]
    have hw : |1 - t| ≤ 1 := by rw [abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
    have hw' : |1 - t| * |Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t)| *
        |Real.sin (2 * Real.pi * x * t)| ≤ 1 := by
      calc
        _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hw (Real.abs_sin_le_one _)
          (abs_nonneg _) (by norm_num)) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact mul_le_of_le_one_right (pow_nonneg hr.le _) hw'
  have hi : HasSum (fun n => ∫ t in Set.Ioc (0 : ℝ) 1, F n t)
      (∫ t in Set.Ioc (0 : ℝ) 1, g t) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => r ^ (n + 1))
    · intro n
      exact (show Continuous (F n) by dsimp [F]; fun_prop).aestronglyMeasurable
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbound n t ht
    · exact Filter.Eventually.of_forall fun _ => hs
    · exact integrableOn_const (by simp)
    · exact Filter.Eventually.of_forall hsum
  have hi' : HasSum (fun n : ℕ => r ^ (n + 1) *
      (∫ t in (0 : ℝ)..1, (1 - t) *
        Real.sin (2 * Real.pi * ((n : ℝ) + 1) * t) *
        Real.sin (2 * Real.pi * x * t))) (∫ t in (0 : ℝ)..1, g t) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      F, integral_const_mul] using hi
  refine ⟨hi'.summable, ?_⟩
  rw [hi'.tsum_eq, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp [g]
  ring

end Causalean.Stat.CLT.BerryEsseen
