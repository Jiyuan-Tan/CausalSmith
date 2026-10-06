module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenLocalProduct
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Integrated local characteristic-function estimate

The pointwise iid product estimate is integrated over its valid frequency
window. This quantitative analytic step is independent of CDF smoothing.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a centered](hyp:hmean_int,hmean) [unit-variance](hyp:hvar_int,hvar)
real law with [integrable third absolute moment at most M3](hyp:hthird_int,hthird),
where [M3 is at least one](hyp:hM3), and [a sample size n of at least two](hyp:hn),
[the integral over the local window |t| ≤ √n/M3 of the distance between the
characteristic function of the standardized iid sum and the standard Gaussian
characteristic function, divided by |t|, is at most 9·M3/√n](goal). -/
theorem iid_unit_variance_charFun_interval_integral_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ) (hM3 : 1 ≤ M3)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (-(Real.sqrt (n : ℝ) / M3))..(Real.sqrt (n : ℝ) / M3),
      ‖(charFun μ (t / Real.sqrt (n : ℝ))) ^ n -
        charFun (gaussianReal 0 1) t‖ / |t|) ≤
      9 * M3 / Real.sqrt (n : ℝ) := by
  let s : ℝ := Real.sqrt (n : ℝ)
  let a : ℝ := s / M3
  let c : ℝ := 7 * M3 / (24 * s)
  have hs : 0 < s := by dsimp [s]; positivity
  have hM : 0 < M3 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlocal (t : ℝ) (ht : |t| ≤ a) :
      ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t| ≤
        c * t ^ 2 * Real.exp (-(t ^ 2 / 6)) := by
    have h := iid_unit_variance_charFun_local_product_bound μ M3 hM3
      hmean_int hmean hvar_int hvar hthird_int hthird n hn t (by simpa [a, s] using ht)
    by_cases ht0 : t = 0
    · subst t
      simp
    · apply (div_le_iff₀ (abs_pos.mpr ht0)).2
      calc
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖
            ≤ c * |t| ^ 3 * Real.exp (-(t ^ 2 / 6)) := by simpa [c, s] using h
        _ = (c * t ^ 2 * Real.exp (-(t ^ 2 / 6))) * |t| := by
          rw [show |t| ^ 3 = |t| * t ^ 2 by rw [← sq_abs]; ring]
          ring
  have henv (t : ℝ) :
      t ^ 2 * Real.exp (-(t ^ 2 / 6)) ≤ 5 * Real.exp (-(t ^ 2 / 12)) := by
    let y : ℝ := t ^ 2 / 12
    have hle : y ≤ Real.exp (y - 1) := by
      linarith [Real.add_one_le_exp (y - 1)]
    have hkey : y * Real.exp (-y) ≤ Real.exp (-1) := by
      calc
        _ ≤ Real.exp (y - 1) * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos (-y)).le
        _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
    have hexp : Real.exp (-1) ≤ (5 / 12 : ℝ) := by
      have h := Real.exp_one_gt_d9
      have he : Real.exp (-1) * Real.exp 1 = 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos (-1), Real.exp_pos 1]
    have hyy : y * Real.exp (-y) ≤ 5 / 12 := hkey.trans hexp
    have heq : Real.exp (-(t ^ 2 / 6)) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [y]
      ring
    rw [heq]
    have ht : t ^ 2 = 12 * y := by dsimp [y]; ring
    rw [ht]
    have hsimp : -(12 * y / 12) = -y := by ring
    rw [hsimp]
    have hm := mul_le_mul_of_nonneg_right hyy (Real.exp_pos (-y)).le
    nlinarith
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 12))) volume := by
    convert integrable_exp_neg_mul_sq (b := (1 / 12 : ℝ)) (by norm_num) using 1
    ext t
    congr 1
    ring
  have hg : Integrable (fun t : ℝ => (c * 5) * Real.exp (-(t ^ 2 / 12))) volume :=
    hgauss.const_mul _
  have hbound (t : ℝ) (ht : |t| ≤ a) :
      ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t| ≤
        (c * 5) * Real.exp (-(t ^ 2 / 12)) := by
    calc
      _ ≤ c * t ^ 2 * Real.exp (-(t ^ 2 / 6)) := hlocal t ht
      _ ≤ c * (5 * Real.exp (-(t ^ 2 / 12))) :=
        by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (henv t) hc
      _ = _ := by ring
  have hnorm :
      ‖∫ t in (-a)..a,
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|‖ ≤
        ∫ t in (-a)..a, (c * 5) * Real.exp (-(t ^ 2 / 12)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith : -a ≤ a)
    · exact Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg _))]
        apply hbound t
        have hta : -a ≤ t := le_of_lt ht.1
        exact abs_le.mpr ⟨by linarith, ht.2⟩)
    · exact hg.intervalIntegrable
  have hfull :
      (∫ t in (-a)..a, (c * 5) * Real.exp (-(t ^ 2 / 12))) ≤
        (c * 5) * Real.sqrt (12 * Real.pi) := by
    rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
    calc
      _ ≤ ∫ t : ℝ, (c * 5) * Real.exp (-(t ^ 2 / 12)) :=
        setIntegral_le_integral hg (Filter.Eventually.of_forall (fun t => by positivity))
      _ = (c * 5) * Real.sqrt (12 * Real.pi) := by
        rw [integral_const_mul]
        have hi : (∫ t : ℝ, Real.exp (-(t ^ 2 / 12))) =
            Real.sqrt (12 * Real.pi) := by
          convert integral_gaussian (1 / 12 : ℝ) using 1
          · congr 1; ext t; congr 1; ring
          · congr 1; ring
        rw [hi]
  have hsqrt : Real.sqrt (12 * Real.pi) ≤ (617 / 100 : ℝ) := by
    have hp := Real.pi_lt_d4
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 12 * Real.pi)
    nlinarith [Real.sqrt_nonneg (12 * Real.pi)]
  have hnum : (c * 5) * Real.sqrt (12 * Real.pi) ≤ 9 * M3 / s := by
    have h := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ c * 5)
    dsimp [c] at *
    apply (le_div_iff₀ hs).2
    have hsne : s ≠ 0 := ne_of_gt hs
    field_simp at *
    nlinarith
  have hmain :
      (∫ t in (-a)..a,
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|) ≤
      ‖∫ t in (-a)..a,
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  calc
    _ ≤ ‖∫ t in (-a)..a,
      ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|‖ := hmain
    _ ≤ ∫ t in (-a)..a, (c * 5) * Real.exp (-(t ^ 2 / 12)) := hnorm
    _ ≤ (c * 5) * Real.sqrt (12 * Real.pi) := hfull
    _ ≤ 9 * M3 / s := hnum
    _ = _ := rfl

end Causalean.Stat.CLT.BerryEsseen
