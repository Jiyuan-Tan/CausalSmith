module
public import Causalean.Mathlib.Analysis.RealInterpolation.ScaleIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Scalar normalization and dilation

The beta integral and Euler reflection formula evaluate the normalization
integral exactly. Positive dilation supplies the exponent in the operator
estimate. All integration identities are for nonnegative extended integrals,
so no nonintegrable-zero convention for a real integral can enter the result.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [An exponent strictly between zero and one](hyp:p,hp) gives
[the reflection-value beta integral on the unit interval](goal).

This is the first normalization obligation: take s=p and t=1-p in the complex
beta/Gamma identity, use Gamma(1)=1 and Euler reflection, then take real parts.
Complex.betaIntegral_convergent supplies integrability for the lintegral conversion.
No half-line substitution is part of this lemma. -/
theorem lintegral_beta_reflection (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (x ^ (p - 1) * (1 - x) ^ (-p))) =
        ENNReal.ofReal (Real.pi / Real.sin (Real.pi * p)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ ((p : ℂ) - 1) *
    (1 - (x : ℂ)) ^ ((1 - (p : ℂ)) - 1)
  have hconv : IntegrableOn f (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (Complex.betaIntegral_convergent (by simpa using hp.1)
        (by simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith [hp.2]))
  have heq : ∀ x ∈ Ioo (0 : ℝ) 1,
      (f x).re = x ^ (p - 1) * (1 - x) ^ (-p) := by
    intro x hx
    simp only [f, ← Complex.ofReal_sub, ← Complex.ofReal_one,
      ← Complex.ofReal_cpow hx.1.le, ← Complex.ofReal_cpow (sub_pos.mpr hx.2).le,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    congr 2
    ring
  have hae : (fun x => (f x).re) =ᵐ[volume.restrict (Ioo 0 1)]
      (fun x => x ^ (p - 1) * (1 - x) ^ (-p)) :=
    (ae_restrict_mem measurableSet_Ioo).mono heq
  have hint := hconv.re.congr hae
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioo).mono (fun x hx =>
      mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (sub_pos.mpr hx.2).le _)))]
  have hbeta : Complex.betaIntegral (p : ℂ) (1 - (p : ℂ)) =
      ((Real.Gamma p * Real.Gamma (1 - p) : ℝ) : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
      (s := (p : ℂ)) (t := 1 - (p : ℂ)) (by simpa using hp.1)
      (by simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith [hp.2])
    rw [show (p : ℂ) + (1 - (p : ℂ)) = 1 by ring, Complex.Gamma_one, one_mul] at h
    simpa only [ Complex.Gamma_one, one_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.Gamma_ofReal, Complex.ofReal_mul] using h.symm
  have hvalue : (∫ x in Ioo (0 : ℝ) 1, (f x).re) =
      Real.pi / Real.sin (Real.pi * p) := by
    have hr : (∫ x in Ioo (0 : ℝ) 1, (f x).re) =
        (∫ x in Ioo (0 : ℝ) 1, f x).re := integral_re hconv
    rw [hr]
    change (∫ x in Ioo (0 : ℝ) 1, f x).re = _
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    change (Complex.betaIntegral (p : ℂ) (1 - (p : ℂ))).re = _
    rw [hbeta, Complex.ofReal_re, Real.Gamma_mul_Gamma_one_sub]
  rw [← integral_congr_ae hae, hvalue]

/-- [An exponent strictly between zero and one](hyp:p,_hp) gives
[the half-line-to-unit-interval beta substitution](goal).

Use x=u/(1-u), with Jacobian (1-u)^(-2), or the inverse u=x/(1+x).
Establish a differentiable bijection between the open intervals and invoke the
nonnegative change-of-variables theorem. This obligation does not evaluate Gamma. -/
theorem lintegral_rpow_div_one_add_eq_beta (p : ℝ) (_hp : p ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (p - 1) / (1 + x))) =
      ∫⁻ x in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (x ^ (p - 1) * (1 - x) ^ (-p)) := by
  let φ : ℝ → ℝ := fun u => u / (1 - u)
  have himage : φ '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hu.1 (sub_pos.mpr hu.2)
    · intro hx
      have hd : 0 < 1 + x := by linarith [show 0 < x from hx]
      refine ⟨x / (1 + x), ⟨div_pos hx hd, (div_lt_one hd).mpr (by linarith)⟩, ?_⟩
      dsimp [φ]
      field_simp
      ring
  have hinj : InjOn φ (Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    dsimp [φ] at huv
    have h := (div_eq_div_iff (sub_pos.mpr hu.2).ne' (sub_pos.mpr hv.2).ne').mp huv
    nlinarith
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt φ (1 / (1 - u) ^ 2) (Ioo 0 1) u := by
    intro u hu
    have h := (hasDerivAt_id u).div ((hasDerivAt_id u).const_sub 1)
      (sub_pos.mpr hu.2).ne'
    convert! h.hasDerivWithinAt (s := Ioo (0 : ℝ) 1) using 1
    simp [id_eq, sub_add_cancel]
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hd : 0 < 1 - u := sub_pos.mpr hu.2
  dsimp only
  rw [abs_of_pos (by positivity : 0 < 1 / (1 - u) ^ 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - u) ^ 2)]
  congr 1
  dsimp [φ]
  rw [Real.div_rpow hu.1.le hd.le, Real.rpow_sub hd, Real.rpow_one, Real.rpow_neg hd.le]
  have hpow : (1 - u) ^ p ≠ 0 := (Real.rpow_pos_of_pos hd p).ne'
  have hadd : 1 + u / (1 - u) = 1 / (1 - u) := by
    field_simp
    ring
  rw [hadd]
  field_simp

/-- [An exponent strictly between zero and one](hyp:p,hp) gives
[Euler's positive-half-line beta integral](goal).

Reuse Complex.Gamma_mul_Gamma_eq_betaIntegral and Real.Gamma_mul_Gamma_one_sub.
The substitution x=u/(1-u) transfers the beta integral from (0,1) to (0,∞);
establish integrability before converting the real integral to a lintegral. -/
theorem lintegral_rpow_div_one_add (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (p - 1) / (1 + x))) =
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * p)) := by
  rw [lintegral_rpow_div_one_add_eq_beta p hp, lintegral_beta_reflection p hp]

/-- [An exponent strictly between zero and one](hyp:θ,hθ) gives
[the exact quadratic normalization integral](goal).

Substitute x=t² in lintegral_rpow_div_one_add with p=1-θ; the Jacobian contributes
the factor 1/2. Reuse the sine symmetry sin(π*(1-θ))=sin(π*θ). -/
theorem lintegral_quadratic_kernel (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (1 - 2 * θ) / (1 + t ^ 2))) =
      ENNReal.ofReal (Real.pi / (2 * Real.sin (Real.pi * θ))) := by
  have hp : 1 - θ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have himage : (fun t : ℝ => t ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact sq_pos_of_pos (show 0 < t from ht)
    · intro hx
      exact ⟨Real.sqrt x, Real.sqrt_pos.mpr hx, Real.sq_sqrt hx.le⟩
  have hinj : InjOn (fun t : ℝ => t ^ 2) (Ioi (0 : ℝ)) := by
    intro t ht u hu heq
    nlinarith [show 0 < t from ht, show 0 < u from hu]
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * t) (Ioi 0) t := by
    intro t ht
    convert! ((hasDerivAt_id t).pow 2).hasDerivWithinAt (s := Ioi (0 : ℝ)) using 1
    simp [id_eq]
  have hsub := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun x : ℝ => ENNReal.ofReal (x ^ ((1 - θ) - 1) / (1 + x)))
  rw [himage] at hsub
  have hkernel : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (|2 * t|) * ENNReal.ofReal ((t ^ 2) ^ ((1 - θ) - 1) / (1 + t ^ 2)) =
        ENNReal.ofReal 2 * ENNReal.ofReal (t ^ (1 - 2 * θ) / (1 + t ^ 2)) := by
    intro t ht
    change 0 < t at ht
    rw [abs_of_pos (mul_pos (by norm_num) ht),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [← Real.rpow_natCast_mul ht.le]
    norm_num only [Nat.cast_ofNat]
    have he : (2 : ℝ) * (1 - θ - 1) = -2 * θ := by ring
    rw [he]
    have hpow : t * t ^ (-2 * θ) = t ^ (1 - 2 * θ) := by
      simpa only [Real.rpow_one, sub_eq_add_neg, neg_mul] using
        (Real.rpow_add ht 1 (-2 * θ)).symm
    rw [mul_assoc, ← mul_div_assoc, hpow]
  rw [setLIntegral_congr_fun measurableSet_Ioi hkernel,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_rpow_div_one_add (1 - θ) hp] at hsub
  have hsin : Real.sin (Real.pi * (1 - θ)) = Real.sin (Real.pi * θ) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  rw [hsin] at hsub
  apply (ENNReal.mul_right_inj (by norm_num : ENNReal.ofReal 2 ≠ 0)
    ENNReal.ofReal_ne_top).mp
  rw [← hsub, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- [Positive finite weights](hyp:a,b,ha,hb) and [an interior exponent](hyp:θ,hθ)
give [the exact geometric weight after normalized harmonic-kernel integration](goal).

Use t=s*sqrt(a.toReal/b.toReal), the preceding normalization integral, and
ENNReal.ofReal/real-power conversion. Off positive finite weights this statement
is deliberately not asserted: infinity divided by infinity is not a quadratic weight. -/
theorem normalized_lintegral_harmonicWeight (a b : ℝ≥0∞)
    (ha : 0 < a ∧ a < ⊤) (hb : 0 < b ∧ b < ⊤)
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    normalizationSq θ * (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-1 - 2 * θ)) * harmonicWeight a b t) =
      ENNReal.rpow a (1 - θ) * ENNReal.rpow b θ := by
  have hA : 0 < a.toReal := ENNReal.toReal_pos_iff.mpr ha
  have hB : 0 < b.toReal := ENNReal.toReal_pos_iff.mpr hb
  have haR : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal ha.2.ne
  have hbR : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hb.2.ne
  let c : ℝ := Real.sqrt (b.toReal / a.toReal)
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hB hA)
  have hc2 : c ^ 2 = b.toReal / a.toReal := Real.sq_sqrt (div_pos hB hA).le
  let F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ 2 / (1 + t ^ 2))
  have hF : Measurable ((Ioi (0 : ℝ)).indicator F) := by
    apply Measurable.indicator _ measurableSet_Ioi
    dsimp [F]
    fun_prop
  have hharm : ∀ t : ℝ, harmonicWeight a b t = a * F (t * c) := by
    intro t
    have hd : 0 < a.toReal + t ^ 2 * b.toReal :=
      add_pos_of_pos_of_nonneg hA (mul_nonneg (sq_nonneg t) hB.le)
    rw [harmonicWeight, ← haR, ← hbR,
      ← ENNReal.ofReal_mul (sq_nonneg t),
      ← ENNReal.ofReal_add hA.le (mul_nonneg (sq_nonneg t) hB.le),
      ← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_div_of_pos hd,
      ← ENNReal.ofReal_mul hA.le]
    congr 1
    rw [mul_pow, hc2]
    field_simp
  have hbase : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 - 2 * θ)) * F t) =
      ENNReal.ofReal (Real.pi / (2 * Real.sin (Real.pi * θ))) := by
    rw [← lintegral_quadratic_kernel θ hθ]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp [F]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← mul_div_assoc]
    congr 1
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  have hscale := lintegral_weighted_dilation F hF c hc θ
  have hint : (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-1 - 2 * θ)) * harmonicWeight a b t) =
        a * ENNReal.ofReal (c ^ (2 * θ)) *
          ENNReal.ofReal (Real.pi / (2 * Real.sin (Real.pi * θ))) := by
    simp_rw [hharm, mul_left_comm (ENNReal.ofReal _) a]
    rw [lintegral_const_mul' _ _ ha.2.ne, hscale, hbase, mul_assoc]
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hθ.1)
      (by nlinarith [Real.pi_pos, hθ.2])
  have hnorm : normalizationSq θ *
      ENNReal.ofReal (Real.pi / (2 * Real.sin (Real.pi * θ))) = 1 := by
    rw [normalizationSq, ← ENNReal.ofReal_mul (by positivity)]
    have he : (2 * Real.sin (Real.pi * θ) / Real.pi) *
        (Real.pi / (2 * Real.sin (Real.pi * θ))) = 1 := by
      field_simp
    rw [he, ENNReal.ofReal_one]
  have hcoeff : a.toReal * c ^ (2 * θ) = a.toReal ^ (1 - θ) * b.toReal ^ θ := by
    have hcp : c ^ (2 * θ) = (b.toReal / a.toReal) ^ θ := by
      rw [← hc2, ← Real.rpow_natCast_mul hc.le]
      norm_num
    rw [hcp, Real.div_rpow hB.le hA.le, Real.rpow_sub hA, Real.rpow_one]
    ring
  rw [hint]
  calc
    _ = (normalizationSq θ *
        ENNReal.ofReal (Real.pi / (2 * Real.sin (Real.pi * θ)))) *
        (a * ENNReal.ofReal (c ^ (2 * θ))) := by ring
    _ = a * ENNReal.ofReal (c ^ (2 * θ)) := by rw [hnorm, one_mul]
    _ = ENNReal.rpow a (1 - θ) * ENNReal.rpow b θ := by
      rw [ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow,
        ← haR, ← hbR, ENNReal.ofReal_rpow_of_pos hA,
        ENNReal.ofReal_rpow_of_pos hB,
        ← ENNReal.ofReal_mul hA.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _), hcoeff]


end Causalean.Mathlib.Analysis.RealInterpolation
