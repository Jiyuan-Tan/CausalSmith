module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenGaussian
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenTaylor

/-! # Local product estimate for a standardized iid characteristic function

The Taylor estimates for one centered draw and for a Gaussian become a
frequency-dependent estimate for their powers. The frequency cutoff is the
natural third-moment scale used by a scalar Berry–Esseen proof.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

private theorem norm_pow_sub_pow_le_of_bound (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1 : ℕ) * ‖a - b‖ * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        (a ^ (n + 1) - b ^ (n + 1)) * a + b ^ (n + 1) * (a - b) := by ring
    rw [hid]
    have h₁ : ‖(a ^ (n + 1) - b ^ (n + 1)) * a‖ ≤
        ((n + 1 : ℕ) * ‖a - b‖ * r ^ n) * r := by
      rw [norm_mul]
      exact mul_le_mul ih ha (norm_nonneg _) (by positivity)
    have h₂ : ‖b ^ (n + 1) * (a - b)‖ ≤ r ^ (n + 1) * ‖a - b‖ := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb _) (norm_nonneg _)
    calc
      ‖(a ^ (n + 1) - b ^ (n + 1)) * a + b ^ (n + 1) * (a - b)‖
          ≤ ‖(a ^ (n + 1) - b ^ (n + 1)) * a‖ + ‖b ^ (n + 1) * (a - b)‖ := norm_add_le _ _
      _ ≤ ((n + 1 : ℕ) * ‖a - b‖ * r ^ n) * r + r ^ (n + 1) * ‖a - b‖ := add_le_add h₁ h₂
      _ = (↑(n + 1 + 1) : ℝ) * ‖a - b‖ * r ^ (n + 1) := by
        rw [pow_succ]
        push_cast
        ring

/-- For [a centered](hyp:hmean_int,hmean) [unit-variance](hyp:hvar_int,hvar)
real law with [integrable third absolute moment at most M3](hyp:hthird_int,hthird),
where [M3 is at least one](hyp:hM3), [a sample size n of at least two](hyp:hn),
and [a frequency with |t| ≤ √n/M3](hyp:ht),
[the characteristic function of the standardized iid sum differs from the
standard Gaussian characteristic function by at most
(7·M3/(24√n))·|t|³·exp(−t²/6)](goal), an explicit cubic error with Gaussian
decay. -/
theorem iid_unit_variance_charFun_local_product_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ) (hM3 : 1 ≤ M3)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / M3) :
    ‖(charFun μ (t / Real.sqrt (n : ℝ))) ^ n -
      charFun (gaussianReal 0 1) t‖ ≤
      (7 * M3 / (24 * Real.sqrt (n : ℝ))) * |t| ^ 3 *
        Real.exp (-(t ^ 2 / 6)) := by
  let s : ℝ := Real.sqrt (n : ℝ)
  let u : ℝ := t / s
  let a : ℂ := charFun μ u
  let b : ℂ := charFun (gaussianReal 0 1) u
  let q : ℂ := 1 - (u : ℂ) ^ 2 / 2
  let r : ℝ := Real.exp (-(u ^ 2 / 3))
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hspos : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hMpos : 0 < M3 := by linarith
  have huabs : |u| ≤ 1 / M3 := by
    dsimp [u]
    rw [abs_div, abs_of_pos hspos]
    exact (div_le_div_iff₀ hspos hMpos).2
      ((le_div_iff₀ hMpos).1 (by simpa [s] using ht))
  have hu1 : |u| ≤ 1 := (huabs.trans (div_le_one hMpos |>.2 hM3))
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u, abs_nonneg u, sq_abs u]
  have hMabs : M3 * |u| ≤ 1 := by
    calc
      M3 * |u| ≤ M3 * (1 / M3) := mul_le_mul_of_nonneg_left huabs (le_of_lt hMpos)
      _ = 1 := by field_simp
  have hnonneg : 0 ≤ (1 : ℝ) - u ^ 2 / 2 := by linarith
  have hq : ‖q‖ = 1 - u ^ 2 / 2 := by
    have hqeq : q = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    simp only [hqeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have haerr : ‖a - q‖ ≤ M3 * |u| ^ 3 / 6 := by
    simpa [a, q] using centered_charFun_quadratic_remainder μ 1 M3
      hmean_int hmean hvar_int hvar hthird_int hthird u
  have hberr : ‖b - q‖ ≤ |u| ^ 4 / 8 := by
    simpa [b, q] using gaussian_charFun_quadratic_remainder u
  have hberr' : ‖b - q‖ ≤ M3 * |u| ^ 3 / 8 := by
    calc
      ‖b - q‖ ≤ |u| ^ 4 / 8 := hberr
      _ ≤ M3 * |u| ^ 3 / 8 := by
        have h : |u| ^ 4 ≤ M3 * |u| ^ 3 := by
          calc
            |u| ^ 4 = |u| ^ 3 * |u| := by ring
            _ ≤ |u| ^ 3 * 1 := mul_le_mul_of_nonneg_left hu1 (by positivity)
            _ ≤ |u| ^ 3 * M3 := mul_le_mul_of_nonneg_left hM3 (by positivity)
            _ = M3 * |u| ^ 3 := by ring
        nlinarith
  have hgap : ‖a - b‖ ≤ 7 * M3 * |u| ^ 3 / 24 := by
    have htri : ‖a - b‖ ≤ ‖a - q‖ + ‖b - q‖ := by
      calc
        ‖a - b‖ = ‖(a - q) + (q - b)‖ := by congr 1; ring
        _ ≤ ‖a - q‖ + ‖q - b‖ := norm_add_le _ _
        _ = ‖a - q‖ + ‖b - q‖ := congrArg _ (norm_sub_rev q b)
    linarith
  have har : ‖a‖ ≤ r := by
    have htri : ‖a‖ ≤ ‖a - q‖ + ‖q‖ := by
      simpa only [sub_add_cancel] using (norm_add_le (a - q) q)
    have hlocal : ‖a‖ ≤ 1 - u ^ 2 / 3 := by
      rw [hq] at htri
      have hm : M3 * |u| ^ 3 ≤ u ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hMabs (sq_nonneg u)
        nlinarith [h, sq_abs u, abs_nonneg u]
      linarith
    have hexp : 1 - u ^ 2 / 3 ≤ r := by
      dsimp [r]
      have := Real.add_one_le_exp (-(u ^ 2 / 3))
      linarith
    exact hlocal.trans hexp
  have hbform : b = Complex.exp ((-(u ^ 2 / 2) : ℝ) : ℂ) := by
    dsimp [b]
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have hbr : ‖b‖ ≤ r := by
    have hbval : ‖b‖ = Real.exp (-(u ^ 2 / 2)) := by
      rw [hbform, Complex.norm_exp]
      simp
      norm_cast
    rw [hbval]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have hrpos : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hpow := norm_pow_sub_pow_le_of_bound a b r hrpos har hbr (n - 1)
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  rw [hnsub] at hpow
  have hbscale : b ^ n = charFun (gaussianReal 0 1) t := by
    have htform : charFun (gaussianReal 0 1) t =
        Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ) := by
      rw [charFun_gaussianReal]
      congr 1
      push_cast
      ring
    have hscale : (n : ℝ) * (u ^ 2 / 2) = t ^ 2 / 2 := by
      dsimp [u]
      rw [div_pow, hs2]
      field_simp
    rw [hbform, htform, ← Complex.exp_nat_mul]
    congr 1
    norm_cast
    linarith [hscale]
  have hrpow : r ^ (n - 1) ≤ Real.exp (-(t ^ 2 / 6)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hnsubreal : (n - 1 : ℕ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hnsubreal]
    have hscale : (n : ℝ) * u ^ 2 = t ^ 2 := by
      dsimp [u]
      rw [div_pow, hs2]
      field_simp
    have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    nlinarith [sq_nonneg u, hscale]
  rw [← hbscale]
  change ‖a ^ n - b ^ n‖ ≤ _
  calc
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ * r ^ (n - 1) := by simpa using hpow
    _ ≤ (n : ℝ) * (7 * M3 * |u| ^ 3 / 24) * r ^ (n - 1) := by
      gcongr
    _ ≤ (n : ℝ) * (7 * M3 * |u| ^ 3 / 24) * Real.exp (-(t ^ 2 / 6)) := by
      gcongr
    _ = (7 * M3 / (24 * s)) * |t| ^ 3 * Real.exp (-(t ^ 2 / 6)) := by
      have hsne : s ≠ 0 := ne_of_gt hspos
      simp only [u, abs_div, abs_of_pos hspos]
      rw [div_pow]
      rw [← hs2]
      field_simp

end Causalean.Stat.CLT.BerryEsseen
