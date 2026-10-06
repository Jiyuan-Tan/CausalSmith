module
public import Causalean.Stat.Privacy.LaplaceMechanism

/-!
# Exact Laplace second moments

The density-weighted square is integrable, and its integral is exactly twice
the squared scale. Bochner and nonnegative extended-integral interfaces are
provided for the existing `laplaceMeasure`; no new distribution is defined.
-/

public section

namespace Causalean.Stat.Privacy

open MeasureTheory Set Causalean.Stat.Privacy
open scoped ENNReal

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [the square
times the centered Laplace density is integrable with respect to Lebesgue measure](goal).

Follow the primary module's `integrable_abs_mul_laplacePDF` half-line method:
use `Real.GammaIntegral_convergent` at shape 3, scale by `1 / b`, and reflect
the positive half-line. This is a separate obligation from evaluating the integral.
-/
theorem integrable_sq_mul_laplacePDF (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2 * laplacePDF b x) := by
  let f : ℝ → ℝ := fun x => (2 * b)⁻¹ * (x ^ 2 * Real.exp (-x / b))
  have hright : IntegrableOn f (Ioi 0) := by
    have hbase := Real.GammaIntegral_convergent (s := (3 : ℝ)) (by norm_num)
    have hscaled : IntegrableOn
        (fun x : ℝ => Real.exp (-(1 / b * x)) *
          (1 / b * x) ^ ((3 : ℝ) - 1)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1)) 0
        (one_div_pos.mpr hb)).mpr (by simpa using hbase)
    have hs : IntegrableOn
        (fun x : ℝ => (2 * b)⁻¹ * (b ^ 2 * (Real.exp (-(1 / b * x)) *
          (1 / b * x) ^ ((3 : ℝ) - 1)))) (Ioi 0) :=
      (hscaled.const_mul (b ^ 2)).const_mul (2 * b)⁻¹
    refine hs.congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp only [f, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
    rw [show -(1 / b * x) = -x / b by ring]
    field_simp [hb.ne']
  have hright_abs : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    refine hright.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change f x = f |x|
    rw [abs_of_pos (by simpa only [mem_Ioi] using hx)]
  have hall : Integrable (fun x => f |x|) := by
    have hleft : IntegrableOn (fun x => f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x :=
        (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright_abs
    rw [← integrableOn_univ]
    simpa only [Iic_union_Ioi] using hleft.union hright_abs
  refine hall.congr (ae_of_all _ fun x => ?_)
  simp only [f, laplacePDF, sq_abs]
  ring

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [the
positive-half-line quadratic exponential integral equals twice the cubed scale](goal).

Apply `Real.integral_rpow_mul_exp_neg_mul_Ioi` with shape 3 and rate `1 / b`,
then evaluate `Real.Gamma 3` and convert natural real powers to integer powers.
-/
theorem integral_sq_mul_exp_neg_div_Ioi (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-x / b)) = 2 * b ^ 3 := by
  calc
    _ = ∫ x : ℝ in Ioi 0, x ^ ((3 : ℝ) - 1) *
        Real.exp (-((1 / b) * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
      rw [show -x / b = -(1 / b * x) by ring]
    _ = (1 / (1 / b)) ^ (3 : ℝ) * Real.Gamma (3 : ℝ) :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (one_div_pos.mpr hb)
    _ = 2 * b ^ 3 := by
      rw [show Real.Gamma (3 : ℝ) = 2 by norm_num]
      rw [one_div_one_div, show b ^ (3 : ℝ) = b ^ (3 : ℕ) from Real.rpow_natCast b 3]
      ring

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has an integrable square](goal).

Transfer `integrable_sq_mul_laplacePDF` through
`integrable_withDensity_iff_integrable_smul'` and prove density nonnegativity
from the existing definition (the primary module's helper is private).
-/
theorem laplaceMeasure_integrable_sq (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2) (laplaceMeasure b) := by
  have hnonneg (x : ℝ) : 0 ≤ laplacePDF b x := by
    unfold laplacePDF
    positivity
  rw [laplaceMeasure,
    integrable_withDensity_iff_integrable_smul' (measurable_laplacePDF b).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, mul_comm] using
    integrable_sq_mul_laplacePDF b hb

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has second moment exactly twice the squared scale](goal).

Rewrite the with-density integral, use `integral_comp_abs` for the even
integrand, and substitute `integral_sq_mul_exp_neg_div_Ioi`. Keep the exact
coefficient 2; an upper bound is not a substitute for this identity.
-/
theorem laplaceMeasure_integral_sq (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 ∂laplaceMeasure b = 2 * b ^ 2 := by
  have hnonneg (x : ℝ) : 0 ≤ laplacePDF b x := by
    unfold laplacePDF
    positivity
  rw [laplaceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplacePDF b).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul]
  let f : ℝ → ℝ := fun x => (2 * b)⁻¹ * (x ^ 2 * Real.exp (-x / b))
  rw [show (fun x : ℝ => laplacePDF b x * x ^ 2) = fun x => f |x| by
    funext x
    simp only [f, laplacePDF, sq_abs]
    ring, integral_comp_abs]
  have hright : (∫ x in Ioi (0 : ℝ), f x) = (2 * b)⁻¹ * (2 * b ^ 3) := by
    rw [show f = fun x => (2 * b)⁻¹ * (x ^ 2 * Real.exp (-x / b)) by rfl,
      integral_const_mul, integral_sq_mul_exp_neg_div_Ioi b hb]
  rw [hright]
  field_simp [hb.ne']

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a centered
Laplace draw has nonnegative extended second moment exactly twice the squared scale](goal). -/
theorem laplaceMeasure_lintegral_sq (b : ℝ) (hb : 0 < b) :
    ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂laplaceMeasure b =
      ENNReal.ofReal (2 * b ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (laplaceMeasure_integrable_sq b hb)
    (ae_of_all _ fun x => sq_nonneg x), laplaceMeasure_integral_sq b hb]

end Causalean.Stat.Privacy
