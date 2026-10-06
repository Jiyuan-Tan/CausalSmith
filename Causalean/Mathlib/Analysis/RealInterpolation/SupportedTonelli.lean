module
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Tonelli on sigma-finite support

A jointly measurable nonnegative kernel can be integrated in either order when
one measure is s-finite and the other is sigma-finite on a set containing the
kernel's support. The ambient second measure may be arbitrary. This is a support
restriction wrapper around Mathlib's Tonelli theorem, retaining infinite values.
-/

public section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [A jointly measurable nonnegative kernel](hyp:F,hF) that
[vanishes outside a fixed set in its second variable](hyp:s,hzero) admits
[interchange of its two integrals](goal), for [an s-finite first measure](hyp:ν)
and [a second measure sigma-finite on that set](hyp:μ).

Restrict the second measure to the support set, use Mathlib's Tonelli theorem,
and remove the restriction with setLIntegral_eq_of_support_subset. No global
sigma-finiteness of the second measure is required. -/
theorem lintegral_lintegral_swap_of_sigmaFinite_support
    {T S : Type*} [MeasurableSpace T] [MeasurableSpace S]
    (ν : Measure T) [SFinite ν] (μ : Measure S) (s : Set S)
    [SigmaFinite (μ.restrict s)] (F : T × S → ℝ≥0∞)
    (hF : Measurable F) (hzero : ∀ t x, x ∉ s → F (t, x) = 0) :
    (∫⁻ t, ∫⁻ x, F (t, x) ∂μ ∂ν) = ∫⁻ x, ∫⁻ t, F (t, x) ∂ν ∂μ := by
  have hrestrict (t : T) : (∫⁻ x in s, F (t, x) ∂μ) = ∫⁻ x, F (t, x) ∂μ := by
    apply setLIntegral_eq_of_support_subset
    intro x hx
    by_contra hxs
    exact hx (hzero t x hxs)
  calc
    _ = ∫⁻ t, ∫⁻ x in s, F (t, x) ∂μ ∂ν := by simp_rw [hrestrict]
    _ = ∫⁻ x in s, ∫⁻ t, F (t, x) ∂ν ∂μ :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra hxs
      exact hx (by simp [hzero _ x hxs])

end Causalean.Mathlib.Analysis.RealInterpolation
