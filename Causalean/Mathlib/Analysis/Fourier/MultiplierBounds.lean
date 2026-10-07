module
public import Causalean.Mathlib.Analysis.Fourier.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Quantitative inverse Gaussian multiplier bounds

For a bandwidth h, a sixth convolution of sinc frequency boxes is supported in
`[-3/(πh), 3/(πh)]`. Bounds `‖F‖∞ ≤ a h` and `‖F'‖∞ ≤ b h²` are the reusable
inputs; this module does not construct that convolution. On its support the inverse
Gaussian factor is at most `exp(18 (σ/h)²)`. Squared norms therefore cost
`exp(36 (σ/h)²)`. Integrating the support length gives fully visible L² constants.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Causalean.Mathlib.Analysis.Fourier

/-- [A Gaussian scale parameter](hyp:σ) and [a complex frequency profile](hyp:F) determine [the inverse-Gaussian frequency multiplier](goal) [by multiplication with the reciprocal Gaussian characteristic function](step:1). -/
def inverseGaussian (σ : ℝ) (F : ℝ → ℂ) : ℝ → ℂ :=
  fun ξ => F ξ * (Real.exp (σ ^ 2 * (2 * Real.pi * ξ) ^ 2 / 2) : ℂ)

/-- [A complex frequency profile](hyp:F) with [one continuous derivative](hyp:hF) and [a Gaussian scale parameter](hyp:σ) give [an inverse-Gaussian multiplier with one continuous derivative](goal). -/
theorem inverseGaussian_contDiff (F : ℝ → ℂ) (σ : ℝ) (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (inverseGaussian σ F) := by
  unfold inverseGaussian
  apply hF.mul
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul
      ((contDiff_const.mul contDiff_id).pow 2)).div_const 2))

/-- [A complex frequency profile](hyp:F) with [compact spectral support](hyp:hF) and [a Gaussian scale parameter](hyp:σ) give [an inverse-Gaussian multiplier with compact spectral support](goal). -/
theorem inverseGaussian_hasCompactSupport (F : ℝ → ℂ) (σ : ℝ)
    (hF : HasCompactSupport F) : HasCompactSupport (inverseGaussian σ F) := by
  exact hF.mul_right

/-- A continuous profile supported in a bounded interval has energy bounded by
its squared height times the interval length. -/
private theorem energy_le_interval (g : ℝ → ℂ) (r M : ℝ)
    (hg : Continuous g) (hr : 0 ≤ r)
    (hs : Function.support g ⊆ Icc (-r) r)
    (hm : ∀ x ∈ Icc (-r) r, ‖g x‖ ≤ M) :
    energy g ≤ (2 * r) * M ^ 2 := by
  have hz : ∀ x, x ∉ Icc (-r) r → ‖g x‖ ^ 2 = 0 := by
    intro x hx
    have : g x = 0 := Function.notMem_support.mp (fun h => hx (hs h))
    simp [this]
  have hi : Integrable (fun x => ‖g x‖ ^ 2) :=
    (hg.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc hz)
  unfold energy
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ _ in Icc (-r) r, M ^ 2 :=
      setIntegral_mono_on hi.integrableOn
        (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
        (fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hm x hx) 2)
    _ = (2 * r) * M ^ 2 := by
      rw [setIntegral_const]
      rw [Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (show 0 ≤ r - -r by linarith)]
      simp only [smul_eq_mul]
      ring

/-- The inverse Gaussian exponent on the sinc-six interval is bounded by
18 times the squared scale-to-bandwidth ratio. -/
private theorem gaussian_exponent_le (σ h x : ℝ) (hh : 0 < h)
    (hx : x ∈ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h))) :
    σ ^ 2 * (2 * Real.pi * x) ^ 2 / 2 ≤ 18 * (σ / h) ^ 2 := by
  have hp : 0 < Real.pi * h := mul_pos Real.pi_pos hh
  have hab : |x| ≤ 3 / (Real.pi * h) := abs_le.mpr hx
  have hx2 := pow_le_pow_left₀ (abs_nonneg x) hab 2
  rw [sq_abs] at hx2
  have heq : 18 * (σ / h) ^ 2 =
      σ ^ 2 * (2 * Real.pi) ^ 2 / 2 * (3 / (Real.pi * h)) ^ 2 := by
    field_simp
    ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hx2
    (show 0 ≤ σ ^ 2 * (2 * Real.pi) ^ 2 / 2 by positivity)]

/-- [A continuous complex frequency profile](hyp:F,hF), [a Gaussian scale parameter and positive bandwidth](hyp:σ,h,hh), [a nonnegative height constant](hyp:a,ha), [sinc-six spectral support](hyp:hsupport), and [a uniform height bound](hyp:hbound) imply [the stated squared L² bound for the inverse-Gaussian multiplier](goal). -/
theorem inverseGaussian_energy_le (F : ℝ → ℂ) (σ h a : ℝ)
    (hF : Continuous F) (hh : 0 < h) (ha : 0 ≤ a)
    (hsupport : Function.support F ⊆ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)))
    (hbound : ∀ ξ, ‖F ξ‖ ≤ a * h) :
    energy (inverseGaussian σ F) ≤
      (6 / Real.pi) * a ^ 2 * h * Real.exp (36 * (σ / h) ^ 2) := by
  have hs : Function.support (inverseGaussian σ F) ⊆
      Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)) := by
    intro x hx
    apply hsupport
    contrapose! hx
    simp [Function.mem_support, inverseGaussian, Function.notMem_support.mp hx]
  have hg : Continuous (inverseGaussian σ F) := by
    unfold inverseGaussian
    fun_prop
  have hm : ∀ x ∈ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)),
      ‖inverseGaussian σ F x‖ ≤ a * h * Real.exp (18 * (σ / h) ^ 2) := by
    intro x hx
    simp only [inverseGaussian, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hbound x) (Real.exp_le_exp.mpr (gaussian_exponent_le σ h x hh hx))
      (le_of_lt (Real.exp_pos _)) (mul_nonneg ha hh.le)
  have he := energy_le_interval (inverseGaussian σ F) (3 / (Real.pi * h))
    (a * h * Real.exp (18 * (σ / h) ^ 2)) hg (by positivity) hs hm
  calc
    _ ≤ _ := he
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have hex : (2 : ℝ) * (18 * (σ / h) ^ 2) = 36 * (σ / h) ^ 2 := by ring
      norm_num only [Nat.cast_ofNat] at *
      rw [hex]
      field_simp
      ring

/-- Product and chain rules give the Gaussian logarithmic derivative. -/
private theorem inverseGaussian_deriv (F : ℝ → ℂ) (σ x : ℝ)
    (hF : DifferentiableAt ℝ F x) :
    deriv (inverseGaussian σ F) x =
      (deriv F x + F x * (4 * Real.pi ^ 2 * σ ^ 2 * x : ℝ)) *
        (Real.exp (σ ^ 2 * (2 * Real.pi * x) ^ 2 / 2) : ℂ) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (σ ^ 2 * (2 * Real.pi * t) ^ 2 / 2))
      (Real.exp (σ ^ 2 * (2 * Real.pi * x) ^ 2 / 2) *
        (4 * Real.pi ^ 2 * σ ^ 2 * x)) x := by
    have he : HasDerivAt (fun t : ℝ => σ ^ 2 * (2 * Real.pi * t) ^ 2 / 2)
        (4 * Real.pi ^ 2 * σ ^ 2 * x) x := by
      convert (((((hasDerivAt_id x).const_mul (2 * Real.pi)).pow 2).const_mul
        (σ ^ 2)).div_const 2) using 1
      all_goals first | rfl | (simp only [id_eq, Nat.cast_ofNat, pow_one, Nat.reduceSub]; ring)
    exact he.exp
  have hp := (hF.hasDerivAt.mul hd.ofReal_comp).deriv
  change deriv (inverseGaussian σ F) x = _ at hp
  rw [hp]
  push_cast
  ring

/-- For [a complex frequency profile F with one continuous derivative](hyp:F,hF), [a nonnegative Gaussian scale σ and positive bandwidth h](hyp:σ,h,hσ,hh), and [nonnegative height constants a and b](hyp:a,b,ha,hb), suppose [F vanishes outside the interval of radius 3/(πh) around zero](hyp:hsupport) and [|F| ≤ a·h and |F′| ≤ b·h² everywhere](hyp:hbound,hderiv). Then [the integral of the squared modulus of the derivative of the inverse-Gaussian multiplier of F is at most (6/π)·(b + 12π·a)²·h³·(1 + σ/h)⁴·exp(36·(σ/h)²)](goal). -/
theorem inverseGaussian_deriv_energy_le (F : ℝ → ℂ) (σ h a b : ℝ)
    (hF : ContDiff ℝ 1 F) (hh : 0 < h) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupport : Function.support F ⊆ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)))
    (hbound : ∀ ξ, ‖F ξ‖ ≤ a * h) (hderiv : ∀ ξ, ‖deriv F ξ‖ ≤ b * h ^ 2) :
    energy (deriv (inverseGaussian σ F)) ≤
      (6 / Real.pi) * (b + 12 * Real.pi * a) ^ 2 * h ^ 3 *
        (1 + σ / h) ^ 4 * Real.exp (36 * (σ / h) ^ 2) := by
  have hG := inverseGaussian_contDiff F σ hF
  have hsG : Function.support (inverseGaussian σ F) ⊆
      Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)) := by
    intro x hx
    apply hsupport
    contrapose! hx
    simp [Function.mem_support, inverseGaussian, Function.notMem_support.mp hx]
  have hsD : Function.support (deriv (inverseGaussian σ F)) ⊆
      Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)) :=
    support_deriv_subset.trans (closure_minimal hsG isClosed_Icc)
  have ht : 0 ≤ σ / h := div_nonneg hσ hh.le
  have hc : 0 ≤ b + 12 * Real.pi * a := by positivity
  have hpoly : b + 12 * Real.pi * a * (σ / h) ^ 2 ≤
      (b + 12 * Real.pi * a) * (1 + σ / h) ^ 2 := by
    have ht1 : 1 ≤ (1 + σ / h) ^ 2 := by nlinarith
    have ht2 : (σ / h) ^ 2 ≤ (1 + σ / h) ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left ht1 hb
    have h2 := mul_le_mul_of_nonneg_left ht2
      (show 0 ≤ 12 * Real.pi * a by positivity)
    nlinarith only [h1, h2]
  have hm : ∀ x ∈ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)),
      ‖deriv (inverseGaussian σ F) x‖ ≤
        (h ^ 2 * (b + 12 * Real.pi * a) * (1 + σ / h) ^ 2) *
          Real.exp (18 * (σ / h) ^ 2) := by
    intro x hx
    have hlog : |4 * Real.pi ^ 2 * σ ^ 2 * x| ≤ 12 * Real.pi * σ ^ 2 / h := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2 * σ ^ 2)]
      calc
        _ ≤ (4 * Real.pi ^ 2 * σ ^ 2) * (3 / (Real.pi * h)) :=
          mul_le_mul_of_nonneg_left (abs_le.mpr hx) (by positivity)
        _ = _ := by field_simp; ring
    rw [inverseGaussian_deriv F σ x ((hF.differentiable (by norm_num)) x)]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hsum : ‖deriv F x + F x * (4 * Real.pi ^ 2 * σ ^ 2 * x : ℝ)‖ ≤
        h ^ 2 * (b + 12 * Real.pi * a * (σ / h) ^ 2) := by
      calc
        _ ≤ ‖deriv F x‖ + ‖F x * (4 * Real.pi ^ 2 * σ ^ 2 * x : ℝ)‖ := norm_add_le _ _
        _ ≤ b * h ^ 2 + (a * h) * (12 * Real.pi * σ ^ 2 / h) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hderiv x) (mul_le_mul (hbound x) hlog (abs_nonneg _) (by positivity))
        _ = _ := by field_simp
    calc
      _ ≤ (h ^ 2 * (b + 12 * Real.pi * a * (σ / h) ^ 2)) *
          Real.exp (18 * (σ / h) ^ 2) :=
        mul_le_mul hsum (Real.exp_le_exp.mpr (gaussian_exponent_le σ h x hh hx))
          (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by nlinarith [mul_le_mul_of_nonneg_left hpoly (sq_nonneg h)]) (by positivity)
  have he := energy_le_interval (deriv (inverseGaussian σ F)) (3 / (Real.pi * h))
    ((h ^ 2 * (b + 12 * Real.pi * a) * (1 + σ / h) ^ 2) *
      Real.exp (18 * (σ / h) ^ 2)) (hG.continuous_deriv (by norm_num))
        (by positivity) hsD hm
  calc
    _ ≤ _ := he
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      have hex : (2 : ℝ) * (18 * (σ / h) ^ 2) = 36 * (σ / h) ^ 2 := by ring
      rw [hex]
      field_simp
      ring

end Causalean.Mathlib.Analysis.Fourier
