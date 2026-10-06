module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Weighted inverse-Fourier energies

Reusable real-line energies with Lebesgue measure. The Fourier convention used by the
other modules is Mathlib's `𝓕⁻ G(v) = ∫ ξ, exp(2π i ξv) G(ξ)`, so its unweighted
Plancherel constant is one and its quadratic moment constant is `(2π)⁻²`.
-/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Causalean.Mathlib.Analysis.Fourier

/-- [The ordinary squared L² energy](goal) of [a complex-valued function on the real line](hyp:g) is [the Lebesgue integral of its squared modulus](step:1). -/
def energy (g : ℝ → ℂ) : ℝ := ∫ v, ‖g v‖ ^ 2

/-- [The weighted squared L² energy](goal) for [a moment exponent](hyp:κ) and [a complex-valued function on the real line](hyp:g) is [the Lebesgue integral weighted by the κ-th power of distance from zero](step:1). -/
def weightedEnergy (κ : ℝ) (g : ℝ → ℂ) : ℝ := ∫ v, |v| ^ κ * ‖g v‖ ^ 2

/-- [A complex-valued function on the real line](hyp:g) has [nonnegative ordinary squared L² energy](goal). -/
theorem energy_nonneg (g : ℝ → ℂ) : 0 ≤ energy g :=
  integral_nonneg fun _ => sq_nonneg _

/-- [A moment exponent](hyp:κ) and [a complex-valued function on the real line](hyp:g) have [nonnegative weighted squared L² energy](goal). -/
theorem weightedEnergy_nonneg (κ : ℝ) (g : ℝ → ℂ) : 0 ≤ weightedEnergy κ g :=
  integral_nonneg fun v => mul_nonneg (Real.rpow_nonneg (abs_nonneg v) κ) (sq_nonneg _)

/-- [A complex-valued function on the real line](hyp:g) has [weighted energy at exponent zero equal to its ordinary squared L² energy](goal). -/
theorem weightedEnergy_zero (g : ℝ → ℂ) : weightedEnergy 0 g = energy g := by
  simp [weightedEnergy, energy]

/-- [A complex-valued function on the real line](hyp:g) has [weighted energy at exponent two equal to its squared-distance weighted integral](goal). -/
theorem weightedEnergy_two (g : ℝ → ℂ) :
    weightedEnergy 2 g = ∫ v, v ^ 2 * ‖g v‖ ^ 2 := by
  simp [weightedEnergy, sq_abs]

end Causalean.Mathlib.Analysis.Fourier
