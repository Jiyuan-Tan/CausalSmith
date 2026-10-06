module
public import Causalean.Stat.CLT.BerryEsseen.CosineCubic
public import Causalean.Stat.CLT.BerryEsseen.SymmetrizedThirdMoment
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.Basic

/-! # Wide-window scalar characteristic-function damping

Prawitz's cubic modulus estimate is isolated for one centered unit-variance
law. Unlike a Taylor triangle bound on a small frequency window, it gives
useful damping up to frequencies of order the inverse third moment.

Reference: Tyurin, arXiv:0912.0726, Lemma 1 (pervoe) and the displayed
definition of b(t,γ). The optimal cosine-remainder coefficient is below
0.1, so replacing it by 1/10 yields the conservative polynomial below.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a centered](hyp:hmean_int,hmean) [unit-variance](hyp:hvar_int,hvar) law
with [integrable third absolute moment at most M3](hyp:hthird_int,hthird),
[the squared modulus of the characteristic function at every real frequency
t is at most 1 − t² + (M3 + 1)·|t|³/5](goal). -/
theorem unit_variance_charFun_norm_sq_cubic_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (t : ℝ) :
    ‖charFun μ t‖ ^ 2 ≤ 1 - t ^ 2 + (M3 + 1) * |t| ^ 3 / 5 := by
  -- The product law turns the squared modulus into a cosine expectation.
  have hexp : Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((t * (p.1 - p.2) : ℝ) * Complex.I)) (μ.prod μ) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall ?_)
    intro p
    simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hproduct : (∫ p : ℝ × ℝ,
      Complex.exp ((t * (p.1 - p.2) : ℝ) * Complex.I) ∂μ.prod μ) =
      charFun μ t * starRingEnd ℂ (charFun μ t) := by
    rw [← charFun_neg, charFun_apply_real, charFun_apply_real,
      ← integral_prod_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcos : (∫ p : ℝ × ℝ, Real.cos (t * (p.1 - p.2)) ∂μ.prod μ) =
      ‖charFun μ t‖ ^ 2 := by
    have h := integral_re hexp
    rw [hproduct, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re] at h
    simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] using h
  -- Centering cancels the mixed term, so the difference has second moment two.
  have h₂₁ := hvar_int.comp_fst μ
  have h₂₂ := hvar_int.comp_snd μ
  have hmix := hmean_int.mul_prod hmean_int
  have hsum : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (μ.prod μ) :=
    h₂₁.add h₂₂
  have hsq : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) := by
    convert hsum.sub (hmix.const_mul 2) using 1
    ext p
    dsimp
    ring
  have hsecond : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂μ.prod μ) = 2 := by
    have heq : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) =
        (fun p => (p.1 ^ 2 + p.2 ^ 2) - 2 * (p.1 * p.2)) := by
      funext p
      ring
    rw [heq, integral_sub hsum (hmix.const_mul 2),
      integral_add h₂₁ h₂₂, integral_const_mul,
      integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y),
      integral_fun_fst (fun x : ℝ => x ^ 2),
      integral_fun_snd (fun x : ℝ => x ^ 2)]
    norm_num [hmean, hvar]
  obtain ⟨hcube, hcube_bound⟩ :=
    symmetrized_unit_third_moment_le μ hmean_int hmean hvar_int hvar hthird_int
  have hcos_int : Integrable (fun p : ℝ × ℝ => Real.cos (t * (p.1 - p.2)))
      (μ.prod μ) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall ?_)
    intro p
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * (p.1 - p.2))
  have hmajor_int : Integrable (fun p : ℝ × ℝ =>
      1 - (t ^ 2 / 2) * (p.1 - p.2) ^ 2 +
        (|t| ^ 3 / 10) * |p.1 - p.2| ^ 3) (μ.prod μ) :=
    ((integrable_const (1 : ℝ)).sub (hsq.const_mul (t ^ 2 / 2))).add
      (hcube.const_mul (|t| ^ 3 / 10))
  have hbound := integral_mono hcos_int hmajor_int (fun p => show
      Real.cos (t * (p.1 - p.2)) ≤
        1 - (t ^ 2 / 2) * (p.1 - p.2) ^ 2 +
          (|t| ^ 3 / 10) * |p.1 - p.2| ^ 3 from by
    have h := cos_le_quadratic_add_cubic (t * (p.1 - p.2))
    simp only [mul_pow, abs_mul] at h
    convert h using 1
    ring)
  have hquadratic : Integrable (fun p : ℝ × ℝ =>
      1 - (t ^ 2 / 2) * (p.1 - p.2) ^ 2) (μ.prod μ) :=
    (integrable_const (1 : ℝ)).sub (hsq.const_mul (t ^ 2 / 2))
  rw [hcos, integral_add hquadratic
    (hcube.const_mul (|t| ^ 3 / 10)),
    integral_sub (integrable_const (1 : ℝ)) (hsq.const_mul (t ^ 2 / 2)),
    integral_const_mul, integral_const_mul, hsecond] at hbound
  have hthird_bound : (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂μ.prod μ) ≤
      2 * (M3 + 1) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hthird_bound
    (show 0 ≤ |t| ^ 3 / 10 by positivity)
  simp only [integral_const, probReal_univ, one_smul] at hbound
  nlinarith only [hbound, hscaled]

end Causalean.Stat.CLT.BerryEsseen
