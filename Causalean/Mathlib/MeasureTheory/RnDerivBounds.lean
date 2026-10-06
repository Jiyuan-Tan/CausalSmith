module
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Setwise bounds from Radon--Nikodym derivative bounds

This module converts almost-everywhere lower bounds on Radon--Nikodym derivatives into
lower bounds on the real-valued masses of arbitrary sets.
-/

public section

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory

/-- Given [a measurable sample type](hyp:α), [two finite measures](hyp:μ,ν), [absolute
continuity of the first with respect to the second](hyp:hAC), [a real lower bound](hyp:c),
[an almost-everywhere lower bound on the real-valued Radon--Nikodym derivative](hyp:hden),
and [a set](hyp:E), [the first measure of that set is at least the lower bound times the
second measure of the set](goal). -/
theorem measureReal_lower_of_rnDeriv_lower {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hAC : μ ≪ ν) (c : ℝ)
    (hden : ∀ᵐ x ∂ν, c ≤ (μ.rnDeriv ν x).toReal)
    (E : Set α) :
    c * ν.real E ≤ μ.real E := by
  have hconst : IntegrableOn (fun _ : α => c) E ν := by
    exact (integrable_const c).integrableOn
  have hrn : IntegrableOn (fun x => (μ.rnDeriv ν x).toReal) E ν :=
    (Measure.integrable_toReal_rnDeriv).integrableOn
  have hbound : (fun _ : α => c) ≤ᵐ[ν.restrict E]
      (fun x => (μ.rnDeriv ν x).toReal) :=
    ae_restrict_of_ae hden
  have hle := setIntegral_mono_ae_restrict hconst hrn hbound
  simpa [Measure.setIntegral_toReal_rnDeriv hAC E, mul_comm] using hle

end Causalean.Mathlib.MeasureTheory
