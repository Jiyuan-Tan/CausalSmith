module
public import Causalean.Mathlib.Analysis.RealInterpolation.ScalarIntegral
public import Causalean.Mathlib.Analysis.RealInterpolation.SupportedTonelli
public import Causalean.Mathlib.Analysis.RealInterpolation.WeightedMinimum
public import Causalean.Mathlib.Analysis.RealInterpolation.WeightedSupport

/-!
# Exact normalized interpolation of weighted L² spaces

Pointwise quadratic minimization gives the harmonic-weight K-functional. The
endpoint-sum hypothesis supplies sigma-finite support, sufficient for Tonelli
on an arbitrary declared measure space. Scalar kernel evaluation then gives
exactly the geometric-weight energy, including infinite energies. Neither
uniform bounds on the weights nor a global sigma-finiteness assumption is used.

Reference: Chandler-Wilde, Hewett, Moiola (2015), Theorem 3.1, arXiv:1404.3599v4.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [A function with a finite endpoint-sum decomposition](hyp:f,hf)
under [positive finite measurable weights](hyp:w0,w1,hw0,hw1,hw) allows
[interchange of the harmonic-kernel integrals](goal), for [any exponent](hyp:θ)
and [any declared measure](hyp:μ).

Restrict μ to the nonzero support of f, install the preceding SigmaFinite result,
apply Tonelli to the jointly measurable extended nonnegative integrand, and extend
back because the integrand vanishes outside this support. Do not assume μ sigma-finite. -/
theorem lintegral_harmonic_energy_comm {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞)
    (hw0 : Measurable w0) (hw1 : Measurable w1)
    (hw : ∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤)
    (θ : ℝ) (f : S →ₘ[μ] ℂ)
    (hf : ∃ f0 f1 : S →ₘ[μ] ℂ, f = f0 + f1 ∧
      wNorm w0 μ f0 < ⊤ ∧ wNorm w1 μ f1 < ⊤) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 - 2 * θ)) *
      ∫⁻ x, harmonicWeight (w0 x) (w1 x) t * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) =
    ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-1 - 2 * θ)) * harmonicWeight (w0 x) (w1 x) t) *
        (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have := sigmaFinite_restrict_support_of_endpoint_sum μ w0 w1 hw0 hw1 hw f hf
  let F : ℝ × S → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (p.1 ^ (-1 - 2 * θ)) *
      harmonicWeight (w0 p.2) (w1 p.2) p.1 * (‖f p.2‖₊ : ℝ≥0∞) ^ 2
  have hp : Measurable (fun p : ℝ × S => ENNReal.ofReal (p.1 ^ (-1 - 2 * θ))) :=
    (measurable_fst.pow measurable_const).ennreal_ofReal
  have ht : Measurable (fun p : ℝ × S => ENNReal.ofReal (p.1 ^ 2)) :=
    (measurable_fst.pow_const 2).ennreal_ofReal
  have h0 := hw0.comp (measurable_snd : Measurable (Prod.snd : ℝ × S → S))
  have h1 := hw1.comp (measurable_snd : Measurable (Prod.snd : ℝ × S → S))
  have hH : Measurable (fun p : ℝ × S => harmonicWeight (w0 p.2) (w1 p.2) p.1) :=
    (h0.mul (ht.mul h1)).div (h0.add (ht.mul h1))
  have hF : Measurable F :=
    (hp.mul hH).mul ((f.measurable.comp measurable_snd).enorm.pow_const 2)
  have hzero : ∀ t x, x ∉ {x | f x ≠ 0} → F (t, x) = 0 := by
    intro t x hx
    have hx0 : f x = 0 := by simpa using hx
    simp [F, hx0]
  have hswap := lintegral_lintegral_swap_of_sigmaFinite_support
    (volume.restrict (Ioi (0 : ℝ))) μ {x | f x ≠ 0} F hF hzero
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (t, x) ∂μ := by
      apply lintegral_congr
      intro t
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [F, mul_assoc]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (t, x)) ∂μ := hswap
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const' ((‖f x‖₊ : ℝ≥0∞) ^ 2)
        (fun t => ENNReal.ofReal (t ^ (-1 - 2 * θ)) * harmonicWeight (w0 x) (w1 x) t)
        (by finiteness)

/-- [Positive finite almost-everywhere measurable endpoint weights](hyp:w0,w1,hw0,hw1,hw)
give [exact equality of normalized quadratic interpolation energy and geometric-weight
L² energy](goal), for [an interior exponent](hyp:θ,hθ) and
[a function in the endpoint sum](hyp:f,hf), on [any measure space](hyp:μ).

This is the complete weighted L² contract. Rewrite the K-functional using its
harmonic minimum, interchange the nonnegative integrals using sigma-finite support,
and apply normalized_lintegral_harmonicWeight almost everywhere. Infinite values
are retained on both sides. Reference: https://arxiv.org/html/1404.3599v4, Theorem 3.1. -/
theorem weighted_l2_interpolation {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞)
    (hw0 : Measurable w0) (hw1 : Measurable w1)
    (hw : ∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤)
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (f : S →ₘ[μ] ℂ)
    (hf : ∃ f0 f1 : S →ₘ[μ] ℂ, f = f0 + f1 ∧
      wNorm w0 μ f0 < ⊤ ∧ wNorm w1 μ f1 < ⊤) :
    kNormSq (wNorm w0 μ) (wNorm w1 μ) θ f =
      ∫⁻ x, ENNReal.rpow (w0 x) (1 - θ) * ENNReal.rpow (w1 x) θ *
        (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  unfold kNormSq
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun t ht => congrArg (fun z => ENNReal.ofReal (t ^ (-1 - 2 * θ)) * z)
      (kFunctionalSq_wNorm μ w0 w1 hw0 hw1 hw t ht f))]
  rw [lintegral_harmonic_energy_comm μ w0 w1 hw0 hw1 hw θ f hf,
    ← lintegral_const_mul' (normalizationSq θ) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hw] with x hx
  rw [← mul_assoc, normalized_lintegral_harmonicWeight
    (w0 x) (w1 x) ⟨hx.1, hx.2.1⟩ ⟨hx.2.2.1, hx.2.2.2⟩ θ hθ]

end Causalean.Mathlib.Analysis.RealInterpolation
