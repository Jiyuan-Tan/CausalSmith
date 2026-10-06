module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenLocalProduct

/-! # Refined local characteristic-function product estimate

On a smaller frequency window the third-moment Taylor error allows a
stronger Gaussian damping factor. This analytic estimate is separate from
the CDF inversion and finite-sample normal approximation steps.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a centered](hyp:hmean_int,hmean) [unit-variance](hyp:hvar_int,hvar)
real law with [integrable third absolute moment at most M3](hyp:hthird_int,hthird),
where [M3 is at least one](hyp:hM3), [a sample size n of at least four](hyp:hn),
and [a frequency in the half-size window |t| ≤ √n/(2·M3)](hyp:ht),
[the characteristic function of the standardized iid sum differs from the
standard Gaussian characteristic function by at most
(M3/(4√n))·|t|³·exp(−t²/4)](goal). -/
theorem iid_unit_variance_charFun_refined_local_product_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ) (hM3 : 1 ≤ M3)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 4 ≤ n) (t : ℝ)
    (ht : |t| ≤ Real.sqrt (n : ℝ) / (2 * M3)) :
    ‖(charFun μ (t / Real.sqrt (n : ℝ))) ^ n -
      charFun (gaussianReal 0 1) t‖ ≤
      (M3 / (4 * Real.sqrt (n : ℝ))) * |t| ^ 3 *
        Real.exp (-(t ^ 2 / 4)) := by
  /- Put u=t/√n and q=1-u²/2. Taylor gives ‖φμ(u)-q‖ ≤
  M3|u|³/6 and ‖φG(u)-q‖ ≤ |u|⁴/8. Since M3|u|≤1/2,
  their sum is at most (11/48) M3|u|³ ≤ M3|u|³/4.
  Also ‖φμ(u)‖ ≤ 1-(5/12)u² ≤ exp(-(5/12)u²), and the
  Gaussian factor obeys the same bound. Apply the difference-of-powers
  estimate from BerryEsseenLocalProduct and use (n-1)/n ≥ 3/4 to
  obtain exp(-t²/4). No CDF approximation is assumed here. -/
  let s : ℝ := Real.sqrt (n : ℝ)
  let u : ℝ := t / s
  let a : ℂ := charFun μ u
  let b : ℂ := charFun (gaussianReal 0 1) u
  let q : ℂ := 1 - (u : ℂ) ^ 2 / 2
  let r : ℝ := Real.exp (-(5 * u ^ 2 / 12))
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hspos : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hMpos : 0 < M3 := by linarith
  have huabs : |u| ≤ 1 / (2 * M3) := by
    dsimp [u]
    rw [abs_div, abs_of_pos hspos]
    exact (div_le_div_iff₀ hspos (by positivity : 0 < 2 * M3)).2
      ((le_div_iff₀ (by positivity : 0 < 2 * M3)).1 (by simpa [s] using ht))
  have hu1 : |u| ≤ 1 := by
    have h : 1 / (2 * M3) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    exact huabs.trans h
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u, abs_nonneg u, sq_abs u]
  have hMabs : M3 * |u| ≤ 1 / 2 := by
    calc
      M3 * |u| ≤ M3 * (1 / (2 * M3)) :=
        mul_le_mul_of_nonneg_left huabs (le_of_lt hMpos)
      _ = 1 / 2 := by field_simp
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
  have hberr' : ‖b - q‖ ≤ M3 * |u| ^ 3 / 16 := by
    have h : |u| ^ 4 ≤ M3 * |u| ^ 3 / 2 := by
      have hhalf : |u| ≤ M3 / 2 := by
        have h' : 1 / (2 * M3) ≤ M3 / 2 := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith [sq_nonneg (M3 - 1)]
        exact huabs.trans h'
      have := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ |u| ^ 3)
      nlinarith
    linarith
  have hgap : ‖a - b‖ ≤ M3 * |u| ^ 3 / 4 := by
    have htri : ‖a - b‖ ≤ ‖a - q‖ + ‖b - q‖ := by
      calc
        ‖a - b‖ = ‖(a - q) + (q - b)‖ := by congr 1; ring
        _ ≤ ‖a - q‖ + ‖q - b‖ := norm_add_le _ _
        _ = ‖a - q‖ + ‖b - q‖ := congrArg _ (norm_sub_rev q b)
    have hpos : 0 ≤ M3 * |u| ^ 3 := by positivity
    linarith
  have har : ‖a‖ ≤ r := by
    have htri : ‖a‖ ≤ ‖a - q‖ + ‖q‖ := by
      simpa only [sub_add_cancel] using (norm_add_le (a - q) q)
    have hlocal : ‖a‖ ≤ 1 - 5 * u ^ 2 / 12 := by
      rw [hq] at htri
      have hm : M3 * |u| ^ 3 ≤ u ^ 2 / 2 := by
        have h := mul_le_mul_of_nonneg_right hMabs (sq_nonneg u)
        nlinarith [h, sq_abs u, abs_nonneg u]
      linarith
    have hexp : 1 - 5 * u ^ 2 / 12 ≤ r := by
      dsimp [r]
      have := Real.add_one_le_exp (-(5 * u ^ 2 / 12))
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
  have hpow_aux : ∀ k : ℕ,
      ‖a ^ (k + 1) - b ^ (k + 1)‖ ≤ (k + 1 : ℕ) * ‖a - b‖ * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hid : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
          (a ^ (k + 1) - b ^ (k + 1)) * a + b ^ (k + 1) * (a - b) := by ring
      rw [hid]
      have h₁ : ‖(a ^ (k + 1) - b ^ (k + 1)) * a‖ ≤
          ((k + 1 : ℕ) * ‖a - b‖ * r ^ k) * r := by
        rw [norm_mul]
        exact mul_le_mul ih har (norm_nonneg _) (by positivity)
      have h₂ : ‖b ^ (k + 1) * (a - b)‖ ≤ r ^ (k + 1) * ‖a - b‖ := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hbr _) (norm_nonneg _)
      calc
        ‖(a ^ (k + 1) - b ^ (k + 1)) * a + b ^ (k + 1) * (a - b)‖
            ≤ ‖(a ^ (k + 1) - b ^ (k + 1)) * a‖ +
              ‖b ^ (k + 1) * (a - b)‖ := norm_add_le _ _
        _ ≤ ((k + 1 : ℕ) * ‖a - b‖ * r ^ k) * r +
              r ^ (k + 1) * ‖a - b‖ := add_le_add h₁ h₂
        _ = (↑(k + 1 + 1) : ℝ) * ‖a - b‖ * r ^ (k + 1) := by
          rw [pow_succ]
          push_cast
          ring
  have hpow := hpow_aux (n - 1)
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
  have hrpow : r ^ (n - 1) ≤ Real.exp (-(t ^ 2 / 4)) := by
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
    have hthreequarter : 3 * (n : ℝ) / 4 ≤ (n : ℝ) - 1 := by linarith
    nlinarith [sq_nonneg u, hscale]
  rw [← hbscale]
  change ‖a ^ n - b ^ n‖ ≤ _
  calc
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ * r ^ (n - 1) := by simpa using hpow
    _ ≤ (n : ℝ) * (M3 * |u| ^ 3 / 4) * r ^ (n - 1) := by
      gcongr
    _ ≤ (n : ℝ) * (M3 * |u| ^ 3 / 4) * Real.exp (-(t ^ 2 / 4)) := by
      gcongr
    _ = (M3 / (4 * s)) * |t| ^ 3 * Real.exp (-(t ^ 2 / 4)) := by
      have hsne : s ≠ 0 := ne_of_gt hspos
      simp only [u, abs_div, abs_of_pos hspos]
      rw [div_pow]
      rw [← hs2]
      field_simp

end Causalean.Stat.CLT.BerryEsseen
