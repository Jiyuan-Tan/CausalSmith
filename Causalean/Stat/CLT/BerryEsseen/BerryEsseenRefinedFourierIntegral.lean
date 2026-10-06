module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenRefinedLocalProduct
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-! # Integrated refined local iid Fourier estimate

The refined characteristic-function product estimate is integrated on its
half-size frequency window with a useful numerical constant.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a centered](hyp:hmean_int,hmean) [unit-variance](hyp:hvar_int,hvar)
real law with [integrable third absolute moment at most M3](hyp:hthird_int,hthird),
where [M3 is at least one](hyp:hM3), and [a sample size n of at least four](hyp:hn),
[the integral over the refined window |t| ≤ √n/(2·M3) of the distance between
the characteristic function of the standardized iid sum and the standard
Gaussian characteristic function, divided by |t|, is at most 2·M3/√n](goal). -/
theorem iid_unit_variance_charFun_refined_interval_integral_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ) (hM3 : 1 ≤ M3)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 4 ≤ n) :
    (∫ t in (-(Real.sqrt (n : ℝ) / (2 * M3)))..
        (Real.sqrt (n : ℝ) / (2 * M3)),
      ‖(charFun μ (t / Real.sqrt (n : ℝ))) ^ n -
        charFun (gaussianReal 0 1) t‖ / |t|) ≤
      2 * M3 / Real.sqrt (n : ℝ) := by
  /- Apply iid_unit_variance_charFun_refined_local_product_bound
  pointwise; after division by |t|, integrate
  (M3/(4√n)) t² exp(-t²/4) over the entire real line.
  Its exact value is √π M3/√n, which is ≤ 2 M3/√n.
  Handle t=0 separately and use a proved Gaussian-moment integral. -/
  let s : ℝ := Real.sqrt (n : ℝ)
  let a : ℝ := s / (2 * M3)
  let c : ℝ := M3 / (4 * s)
  let g : ℝ → ℝ := fun t => t ^ 2 * Real.exp (-(t ^ 2 / 4))
  have hs : 0 < s := by dsimp [s]; positivity
  have hM : 0 < M3 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hg : Integrable g volume := by
    convert integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 4 : ℝ)) (by norm_num)
      (s := (2 : ℝ)) (by norm_num) using 1
    ext t
    simp only [g]
    rw [show -(t ^ 2 / 4) = -(1 / 4 : ℝ) * t ^ 2 by ring]
    rw [Real.rpow_two]
  have hlocal (t : ℝ) (ht : |t| ≤ a) :
      ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t| ≤ c * g t := by
    have h := iid_unit_variance_charFun_refined_local_product_bound μ M3 hM3
      hmean_int hmean hvar_int hvar hthird_int hthird n hn t (by simpa [a, s] using ht)
    by_cases ht0 : t = 0
    · subst t
      simp [g]
    · apply (div_le_iff₀ (abs_pos.mpr ht0)).2
      calc
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖
            ≤ c * |t| ^ 3 * Real.exp (-(t ^ 2 / 4)) := by simpa [c, s] using h
        _ = (c * g t) * |t| := by
          rw [show |t| ^ 3 = |t| * t ^ 2 by rw [← sq_abs]; ring]
          dsimp [g]
          ring
  have hnorm :
      ‖∫ t in (-a)..a,
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|‖ ≤
        ∫ t in (-a)..a, c * g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith : -a ≤ a)
    · exact Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg _))]
        apply hlocal t
        have hta : -a ≤ t := le_of_lt ht.1
        exact abs_le.mpr ⟨by linarith, ht.2⟩)
    · exact (hg.const_mul c).intervalIntegrable
  have hhalf : (∫ t in Set.Ioi (0 : ℝ), g t) = 2 * Real.sqrt Real.pi := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 : ℝ))
      (b := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    convert h using 1
    · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      simp only [g]
      rw [show -(t ^ 2 / 4) = -(1 / 4 : ℝ) * t ^ 2 by ring]
      rw [Real.rpow_two]
    · norm_num [Real.Gamma_add_one, Real.Gamma_one_half_eq]
      rw [show (3 : ℝ) / 2 = (1 / 2 : ℝ) + 1 by ring,
        Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      ring
  have hfull : (∫ t : ℝ, g t) = 4 * Real.sqrt Real.pi := by
    have heven (t : ℝ) : g (-t) = g t := by simp [g]
    have hneg : (∫ t in Set.Iic (0 : ℝ), g t) = ∫ t in Set.Ioi (0 : ℝ), g t := by
      simpa only [neg_zero, heven] using (integral_comp_neg_Ioi 0 g).symm
    rw [← integral_add_compl (s := Set.Ioi 0) (by simp) hg, Set.compl_Ioi, hneg]
    rw [hhalf]
    ring
  have hwindow : (∫ t in (-a)..a, c * g t) ≤ c * (4 * Real.sqrt Real.pi) := by
    rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
    calc
      _ ≤ ∫ t : ℝ, c * g t :=
        setIntegral_le_integral (hg.const_mul c)
          (Filter.Eventually.of_forall (fun t => by dsimp [g]; positivity))
      _ = c * (4 * Real.sqrt Real.pi) := by rw [integral_const_mul, hfull]
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    have hsq := Real.sq_sqrt Real.pi_nonneg
    nlinarith [Real.sqrt_nonneg Real.pi, Real.pi_lt_four]
  have hnum : c * (4 * Real.sqrt Real.pi) ≤ 2 * M3 / s := by
    have h := mul_le_mul_of_nonneg_left hpi (by positivity : 0 ≤ 4 * c)
    dsimp [c] at *
    apply (le_div_iff₀ hs).2
    field_simp at *
    nlinarith
  calc
    (∫ t in (-a)..a,
      ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|)
      ≤ ‖∫ t in (-a)..a,
        ‖(charFun μ (t / s)) ^ n - charFun (gaussianReal 0 1) t‖ / |t|‖ := by
          rw [Real.norm_eq_abs]
          exact le_abs_self _
    _ ≤ ∫ t in (-a)..a, c * g t := hnorm
    _ ≤ c * (4 * Real.sqrt Real.pi) := hwindow
    _ ≤ 2 * M3 / s := hnum
    _ = _ := rfl

end Causalean.Stat.CLT.BerryEsseen
