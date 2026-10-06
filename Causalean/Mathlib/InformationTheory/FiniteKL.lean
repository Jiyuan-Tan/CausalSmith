module
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Kullback--Leibler divergence on finite measurable spaces

This file identifies measure-theoretic Kullback--Leibler divergence on a finite
discrete space with the familiar finite sum of mass ratios. It is the bridge
between Mathlib's general-measure KL API and finite-alphabet entropy arguments.
-/

public section

namespace Causalean.Mathlib.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal
open _root_.InformationTheory

/-- For [probability measures `μ` and `ν` on a finite discrete space](hyp:μ,ν), if
[`μ` is absolutely continuous with respect to `ν`](hyp:hμν), then [their real-valued
Kullback--Leibler divergence is the sum of each `μ`-mass times the logarithm of its
ratio to the corresponding `ν`-mass](goal).

The zero-mass summands vanish, so the displayed formula uses ordinary real division
without a separate support convention. -/
theorem klDiv_toReal_eq_sum_measureReal
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (_root_.InformationTheory.klDiv μ ν).toReal =
      ∑ x : α, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
  rw [_root_.InformationTheory.toReal_klDiv_of_measure_eq hμν (by simp)]
  rw [integral_fintype .of_finite]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hμx : μ {x} = 0
  · simp [measureReal_def, hμx]
  have hνx : ν {x} ≠ 0 := fun h => hμx (hμν h)
  have hrn : μ.rnDeriv ν x = μ {x} / ν {x} := by
    have hae := Measure.withDensity_rnDeriv_eq μ ν hμν
    have happ := congrArg (fun m : Measure α => m {x}) hae
    simp only [MeasurableSet.singleton, withDensity_apply, Measure.restrict_singleton,
      lintegral_smul_measure, lintegral_dirac, smul_eq_mul] at happ
    exact (ENNReal.eq_div_iff hνx (measure_ne_top ν {x})).2 happ
  simp only [llr_def, hrn]
  rw [ENNReal.toReal_div]
  rfl

end Causalean.Mathlib.InformationTheory
