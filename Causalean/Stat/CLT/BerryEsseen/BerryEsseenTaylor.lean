module
public import Mathlib.Probability.CentralLimitTheorem

/-! # The third-order characteristic-function estimate

This module isolates the local analytic estimate needed for a quantitative
scalar central limit theorem. The bound is for an arbitrary real frequency
and does not assume a limiting normal approximation.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For a real argument, the complex exponential on the imaginary axis differs
from its quadratic Taylor polynomial by at most one sixth of the cubed
absolute argument. -/
theorem exp_imag_quadratic_remainder (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) -
      (1 + (u : ℂ) * Complex.I + ((u : ℂ) * Complex.I) ^ 2 / 2)‖ ≤
      |u| ^ 3 / 6 := by
  let f : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * Complex.I)
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := by
    convert (Complex.ofRealCLM.contDiff : ContDiff ℝ ⊤ (Complex.ofRealCLM : ℝ → ℂ)) using 1
    funext t
    rfl
  have hf : ContDiff ℝ ⊤ f := by
    have hm : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ) * Complex.I) := hc.mul contDiff_const
    exact Complex.contDiff_exp.comp hm
  have hd (t : ℝ) : HasDerivAt f (Complex.I * f t) t := by
    dsimp [f]
    convert ((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp (t : ℂ)
      (hasDerivAt_mul_const Complex.I)).comp_ofReal using 1
    · funext s
      simp [mul_comm]
    · ring
  have hn (n : ℕ) (t : ℝ) : iteratedDeriv n f t = Complex.I ^ n * f t := by
    induction n with
    | zero => simp [iteratedDeriv_zero]
    | succ n ih =>
      rw [iteratedDeriv_succ']
      have hfun : deriv f = fun x => Complex.I * f x := funext fun x => (hd x).deriv
      rw [hfun]
      rw [iteratedDeriv_const_mul Complex.I (hf.contDiffAt.of_le (by simp))]
      rw [ih]
      ring
  by_cases hu : u = 0
  · subst u
    norm_num [f]
  have hs : UniqueDiffOn ℝ (Set.uIcc 0 u) := uniqueDiffOn_uIcc (Ne.symm hu)
  have hi (n : ℕ) (t : ℝ) (ht : t ∈ Set.uIcc 0 u) :
      iteratedDerivWithin n f (Set.uIcc 0 u) t = Complex.I ^ n * f t := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt.of_le (by simp)) ht, hn]
  have hz : (0 : ℝ) ∈ Set.uIcc 0 u := Set.left_mem_uIcc
  have htaylor : taylorWithinEval f 2 (Set.uIcc 0 u) 0 u =
      1 + (u : ℂ) * Complex.I + ((u : ℂ) * Complex.I) ^ 2 / 2 := by
    have hzero (n : ℕ) : iteratedDerivWithin n f (Set.uIcc 0 u) 0 = Complex.I ^ n := by
      rw [hi n 0 hz]
      simp [f]
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, hzero]
    rw [mul_pow, Complex.I_sq]
    ring
  have hrem := taylor_integral_remainder (f := f) (x := u) (x₀ := 0) (n := 2)
    (hf.contDiffOn.of_le (by simp))
  rw [htaylor] at hrem
  have hpoint (t : ℝ) (ht : t ∈ Set.uIcc 0 u) :
      ‖((u - t) ^ 2 / (2 : ℝ)) • iteratedDerivWithin 3 f (Set.uIcc 0 u) t‖ ≤
        (u - t) ^ 2 / 2 := by
    rw [hi 3 t ht, norm_smul, norm_mul, norm_pow, Complex.norm_I]
    simp [f, Complex.norm_exp_ofReal_mul_I]
  calc
    ‖Complex.exp ((u : ℂ) * Complex.I) -
        (1 + (u : ℂ) * Complex.I + ((u : ℂ) * Complex.I) ^ 2 / 2)‖
      = ‖∫ t : ℝ in 0..u, ((u - t) ^ 2 / (2 : ℝ)) •
          iteratedDerivWithin 3 f (Set.uIcc 0 u) t‖ := by
          simpa [f] using congrArg norm hrem
    _ ≤ |∫ t : ℝ in 0..u, (u - t) ^ 2 / 2| := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
        exact hpoint t (Set.uIoc_subset_uIcc ht)
      · exact (by fun_prop : Continuous (fun t : ℝ => (u - t) ^ 2 / 2)).intervalIntegrable 0 u
    _ = |u| ^ 3 / 6 := by
      have h := intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => x ^ 2 / 2) u (a := 0) (b := u)
      simp only [sub_self, sub_zero] at h
      rw [h, intervalIntegral.integral_div, integral_pow]
      norm_num [abs_div, abs_pow]
      ring

/-- For [a centered](hyp:hmean_int,hmean) real probability law with
[integrable second moment σ2](hyp:hvar_int,hvar) and
[integrable third absolute moment at most M3](hyp:hthird_int,hthird),
[the characteristic function at every real frequency t lies within
M3·|t|³/6 of the variance quadratic 1 − σ2·t²/2](goal). -/
theorem centered_charFun_quadratic_remainder
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ2 M3 : ℝ)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ2)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (t : ℝ) :
    ‖charFun μ t - ((1 : ℂ) - (σ2 : ℂ) * (t : ℂ) ^ 2 / 2)‖ ≤
      M3 * |t| ^ 3 / 6 := by
  let E : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  let A : ℝ → ℂ := fun x => ((t * x : ℝ) : ℂ) * Complex.I
  let B : ℝ → ℂ := fun x => (A x) ^ 2 / 2
  let G : ℝ → ℝ := fun x => |t * x| ^ 3 / 6
  have hE : Integrable E μ := by
    apply Integrable.of_bound (C := 1)
    · exact (by fun_prop : Continuous E).aestronglyMeasurable
    · filter_upwards [] with x
      simpa [E, Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (t * x)).le
  have hA : Integrable A μ := by
    have h := (hmean_int.ofReal : Integrable (fun x : ℝ => (x : ℂ)) μ)
    convert (h.const_mul ((t : ℂ) * Complex.I)) using 1 <;> funext x <;> simp [A] <;> ring
  have hB : Integrable B μ := by
    have h := (hvar_int.ofReal : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) μ)
    convert (h.const_mul (-(t : ℂ) ^ 2 / 2)) using 1 <;> funext x <;>
      simp only [B, A, Complex.ofReal_mul, mul_pow, Complex.I_sq] <;>
      push_cast <;> ring_nf <;> rfl
  have hG : Integrable G μ := by
    convert hthird_int.const_mul (|t| ^ 3 / 6) using 1 <;> funext x <;>
      simp [G, abs_mul, mul_pow] <;> ring
  have hP : Integrable (fun x => (1 : ℂ) + A x + B x) μ :=
    ((integrable_const (1 : ℂ)).add hA).add hB
  have hAform : A = fun x : ℝ => ((t : ℂ) * Complex.I) * (x : ℂ) := by
    funext x
    simp [A, Complex.ofReal_mul]
    ring
  have hBform : B = fun x : ℝ => (-(t : ℂ) ^ 2 / 2) * ((x ^ 2 : ℝ) : ℂ) := by
    funext x
    simp only [B, A, Complex.ofReal_mul, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hAint : (∫ x : ℝ, A x ∂μ) = 0 := by
    rw [hAform, integral_const_mul, integral_complex_ofReal, hmean]
    simp
  have hBint : (∫ x : ℝ, B x ∂μ) = -(t : ℂ) ^ 2 / 2 * (σ2 : ℂ) := by
    rw [hBform, integral_const_mul, integral_complex_ofReal, hvar]
  have hPval : (∫ x : ℝ, (1 : ℂ) + A x + B x ∂μ) =
      1 - (σ2 : ℂ) * (t : ℂ) ^ 2 / 2 := by
    calc
      (∫ x : ℝ, (1 : ℂ) + A x + B x ∂μ) =
          (∫ x : ℝ, (1 : ℂ) + A x ∂μ) + ∫ x : ℝ, B x ∂μ :=
        integral_add ((integrable_const (1 : ℂ)).add hA) hB
      _ = (∫ _x : ℝ, (1 : ℂ) ∂μ) + (∫ x : ℝ, A x ∂μ) + ∫ x : ℝ, B x ∂μ := by
        rw [integral_add (integrable_const (1 : ℂ)) hA]
      _ = 1 - (σ2 : ℂ) * (t : ℂ) ^ 2 / 2 := by
        rw [integral_const, hAint, hBint]
        simp
        ring
  have hEq : charFun μ t = ∫ x : ℝ, E x ∂μ := by
    rw [charFun_apply_real]
    congr 1
    funext x
    simp [E, Complex.ofReal_mul]
  calc
    ‖charFun μ t - ((1 : ℂ) - (σ2 : ℂ) * (t : ℂ) ^ 2 / 2)‖
        = ‖∫ x : ℝ, (E x - ((1 : ℂ) + A x + B x)) ∂μ‖ := by
            rw [hEq, ← hPval, integral_sub hE hP]
    _ ≤ ∫ x : ℝ, G x ∂μ := by
      apply norm_integral_le_of_norm_le hG
      filter_upwards [] with x
      simpa [E, A, B, G, Complex.ofReal_mul] using
        exp_imag_quadratic_remainder (t * x)
    _ ≤ M3 * |t| ^ 3 / 6 := by
      have hGform : G = fun x : ℝ => (|t| ^ 3 / 6) * |x| ^ 3 := by
        funext x
        simp [G, abs_mul, mul_pow]
        ring
      rw [hGform, integral_const_mul]
      calc
        |t| ^ 3 / 6 * ∫ x : ℝ, |x| ^ 3 ∂μ ≤ |t| ^ 3 / 6 * M3 :=
          mul_le_mul_of_nonneg_left hthird (by positivity)
        _ = M3 * |t| ^ 3 / 6 := by ring

end Causalean.Stat.CLT.BerryEsseen
