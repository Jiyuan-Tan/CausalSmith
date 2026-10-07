module
public import Causalean.Mathlib.Analysis.Fourier.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Interpolating absolute weighted L² energies

The geometric interpolation inequality assumes only integrable zeroth and second moments; the
integrability statement and the additive bound also assume an almost-everywhere strongly
measurable function.
Both the geometric interpolation inequality and a scale-dependent additive bound
include κ = 0 and κ = 2. Integrability of the weighted integrand is proved separately, so
the real integral's nonintegrable-zero convention does not make the estimates meaningless.
-/

public section

open MeasureTheory
namespace Causalean.Mathlib.Analysis.Fourier

/-- [A moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2), [a positive reference scale](hyp:h,hh), and [a real location](hyp:v) give [the stated bound of its absolute power by zeroth and quadratic weights](goal). -/
theorem abs_rpow_le_scaled_quadratic (κ h v : ℝ)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hh : 0 < h) :
    |v| ^ κ ≤ h ^ κ + h ^ (κ - 2) * v ^ 2 := by
  by_cases hv : |v| ≤ h
  · exact (Real.rpow_le_rpow (abs_nonneg v) hv hκ0).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hh.le _) (sq_nonneg v)))
  · have hvpos : 0 < |v| := lt_trans hh (lt_of_not_ge hv)
    have hpow : |v| ^ (κ - 2) ≤ h ^ (κ - 2) :=
      Real.rpow_le_rpow_of_nonpos hh (le_of_lt (lt_of_not_ge hv)) (by linarith)
    have hid : |v| ^ κ = |v| ^ (κ - 2) * v ^ 2 := by
      rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add hvpos]
      congr 1
      ring
    rw [hid]
    exact (mul_le_mul_of_nonneg_right hpow (sq_nonneg v)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hh.le _))

/-- [A complex-valued function with almost-everywhere strong measurability](hyp:g,hg), [a moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2), and [finite ordinary and quadratic squared energies](hyp:h0,h2) have [an integrable weighted squared energy](goal). -/
theorem integrable_weightedEnergy (g : ℝ → ℂ) (κ : ℝ)
    (hg : AEStronglyMeasurable g) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (h0 : Integrable (fun v => ‖g v‖ ^ 2))
    (h2 : Integrable (fun v => v ^ 2 * ‖g v‖ ^ 2)) :
    Integrable (fun v => |v| ^ κ * ‖g v‖ ^ 2) := by
  have hm : AEStronglyMeasurable (fun v : ℝ => |v| ^ κ * ‖g v‖ ^ 2) := by
    exact ((Real.continuous_rpow_const hκ0).comp continuous_abs).aestronglyMeasurable.mul
      (hg.norm.pow 2)
  refine (h0.add h2).mono' hm (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (abs_nonneg v) κ) (sq_nonneg _))]
  have hb := abs_rpow_le_scaled_quadratic κ 1 v hκ0 hκ2 zero_lt_one
  simp only [Real.one_rpow, one_mul] at hb
  simpa only [Pi.add_apply, add_mul, one_mul] using
    mul_le_mul_of_nonneg_right hb (sq_nonneg ‖g v‖)

/-- For [a complex-valued function g on the real line](hyp:g), [a moment exponent κ between zero and two](hyp:κ,hκ0,hκ2), and [integrable |g|² and v²·|g(v)|²](hyp:h0,h2), [the integral of |v|^κ·|g(v)|² is at most E₀^(1 − κ/2)·E₂^(κ/2), where E₀ is the integral of |g|² and E₂ the integral of v²·|g(v)|²](goal). -/
theorem weightedEnergy_le_interpolation (g : ℝ → ℂ) (κ : ℝ)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (h0 : Integrable (fun v => ‖g v‖ ^ 2))
    (h2 : Integrable (fun v => v ^ 2 * ‖g v‖ ^ 2)) :
    weightedEnergy κ g ≤
      (energy g) ^ (1 - κ / 2) * (weightedEnergy 2 g) ^ (κ / 2) := by
  rcases eq_or_lt_of_le hκ0 with hk | hk
  · subst κ
    simp [weightedEnergy_zero]
  rcases eq_or_lt_of_le hκ2 with hk2 | hk2
  · subst κ
    simp
  let a : ℝ := 1 - κ / 2
  let b : ℝ := κ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hpq : a⁻¹.HolderConjugate b⁻¹ := Real.HolderConjugate.inv_inv ha hb hab
  have hmem : ∀ (f : ℝ → ℝ) (c : ℝ), (∀ v, 0 ≤ f v) →
      Integrable f → 0 < c →
      MemLp (fun v => f v ^ c) (ENNReal.ofReal c⁻¹) := by
    intro f c hf hi hc
    have hm := (Real.continuous_rpow_const hc.le).comp_aestronglyMeasurable hi.1
    apply (integrable_norm_rpow_iff hm
      (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)))
      ENNReal.ofReal_ne_top).mp
    have hid : (fun v => ‖f v ^ c‖ ^ (ENNReal.ofReal c⁻¹).toReal) = f := by
      funext v
      rw [ENNReal.toReal_ofReal (inv_pos.mpr hc).le, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (hf v) c),
        ← Real.rpow_mul (hf v), mul_inv_cancel₀ hc.ne', Real.rpow_one]
    rwa [hid]
  have hf := hmem (fun v => ‖g v‖ ^ 2) a (fun v => sq_nonneg _) h0 ha
  have hh := hmem (fun v => v ^ 2 * ‖g v‖ ^ 2) b
    (fun v => mul_nonneg (sq_nonneg v) (sq_nonneg _)) h2 hb
  have hpow0 : (fun v => ((‖g v‖ ^ 2 : ℝ) ^ a) ^ a⁻¹) = (fun v => ‖g v‖ ^ 2) := by
    funext v
    rw [← Real.rpow_mul (sq_nonneg _), mul_inv_cancel₀ ha.ne', Real.rpow_one]
  have hpow2 : (fun v => ((v ^ 2 * ‖g v‖ ^ 2 : ℝ) ^ b) ^ b⁻¹) =
      (fun v => v ^ 2 * ‖g v‖ ^ 2) := by
    funext v
    rw [← Real.rpow_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      mul_inv_cancel₀ hb.ne', Real.rpow_one]
  have hprod : (fun v => (‖g v‖ ^ 2 : ℝ) ^ a *
      (v ^ 2 * ‖g v‖ ^ 2) ^ b) = (fun v => |v| ^ κ * ‖g v‖ ^ 2) := by
    funext v
    rw [Real.mul_rpow (sq_nonneg v) (sq_nonneg _)]
    calc
      (‖g v‖ ^ 2 : ℝ) ^ a * ((v ^ 2 : ℝ) ^ b * (‖g v‖ ^ 2 : ℝ) ^ b) =
          (v ^ 2 : ℝ) ^ b * ((‖g v‖ ^ 2 : ℝ) ^ a * (‖g v‖ ^ 2 : ℝ) ^ b) := by ring
      _ = (v ^ 2 : ℝ) ^ b * ‖g v‖ ^ 2 := by
        rw [← Real.rpow_add_of_nonneg (sq_nonneg _) ha.le hb.le, hab, Real.rpow_one]
      _ = |v| ^ κ * ‖g v‖ ^ 2 := by
        rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg v)]
        congr 2
        dsimp [b]
        ring
  have hhölder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (sq_nonneg ‖g v‖) a)
    (Filter.Eventually.of_forall fun v =>
      Real.rpow_nonneg (mul_nonneg (sq_nonneg v) (sq_nonneg ‖g v‖)) b) hf hh
  simp only [one_div, inv_inv] at hhölder
  rw [hpow0, hpow2, hprod] at hhölder
  rw [weightedEnergy_two]
  simpa only [weightedEnergy, energy, a, b] using hhölder

/-- [A complex-valued function with almost-everywhere strong measurability](hyp:g,hg), [a moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2), [a positive reference scale](hyp:h,hh), and [finite ordinary and quadratic squared energies](hyp:h0,h2) satisfy [the scale-dependent additive weighted-energy bound](goal). -/
theorem weightedEnergy_le_scaled (g : ℝ → ℂ) (κ h : ℝ)
    (hg : AEStronglyMeasurable g) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hh : 0 < h)
    (h0 : Integrable (fun v => ‖g v‖ ^ 2))
    (h2 : Integrable (fun v => v ^ 2 * ‖g v‖ ^ 2)) :
    weightedEnergy κ g ≤ h ^ κ * energy g + h ^ (κ - 2) * weightedEnergy 2 g := by
  have hw := integrable_weightedEnergy g κ hg hκ0 hκ2 h0 h2
  have hr := (h0.const_mul (h ^ κ)).add (h2.const_mul (h ^ (κ - 2)))
  have hi := integral_mono hw hr (fun v => by
    simpa only [Pi.add_apply, add_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right
        (abs_rpow_le_scaled_quadratic κ h v hκ0 hκ2 hh) (sq_nonneg ‖g v‖))
  rw [weightedEnergy_two]
  simpa only [weightedEnergy, energy, Pi.add_apply,
    add_mul, mul_assoc, integral_add (h0.const_mul _) (h2.const_mul _),
    integral_const_mul] using hi

end Causalean.Mathlib.Analysis.Fourier
