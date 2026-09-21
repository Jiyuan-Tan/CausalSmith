module
public import Causalean.Stat.Bootstrap.Efron
public import Causalean.Stat.Inference.VarianceEstimation

/-!
# Empirical-measure variance and `IIDSample.empiricalVar`

This module identifies Mathlib's variance of a statistic under the empirical measure of the first
`n` observations with Causalean's existing plug-in empirical variance.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- For [an i.i.d. sample](hyp:S), [a measurable real statistic](hyp:hψ), [a nonzero sample
size](hyp:hn), and [an outcome](hyp:ω), [the variance of the statistic under the empirical measure
of the first `n` observations equals Causalean's plug-in empirical variance](goal). -/
theorem variance_empiricalMeasure_eq_empiricalVar
    (S : Causalean.Stat.IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (n : ℕ) (hn : n ≠ 0) (ω : Ω) :
    variance ψ (empiricalMeasure (fun i : Fin n ↦ S.Z i ω)) =
      Causalean.Stat.IIDSample.empiricalVar S ψ n ω := by
  let _ : IsProbabilityMeasure (empiricalMeasure (fun i : Fin n ↦ S.Z i ω)) :=
    empiricalMeasure_isProbabilityMeasure _ hn
  rw [ProbabilityTheory.variance_eq_integral hψ.aemeasurable]
  have hmean :
      ∫ x, ψ x ∂empiricalMeasure (fun i : Fin n ↦ S.Z i ω) =
        S.sampleMean ψ n ω := by
    unfold empiricalMeasure
    rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
      (fun i : Fin n ↦ S.Z i ω) (Nat.pos_of_ne_zero hn) hψ]
    rw [Causalean.Stat.IIDSample.sampleMean,
      Fin.sum_univ_eq_sum_range (fun i ↦ ψ (S.Z i ω)) n]
    simp only [one_div]
  rw [hmean]
  unfold empiricalMeasure
  rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
    (f := fun x ↦ (ψ x - S.sampleMean ψ n ω) ^ 2)
    (fun i : Fin n ↦ S.Z i ω) (Nat.pos_of_ne_zero hn)
    ((hψ.sub measurable_const).pow_const 2)]
  rw [Causalean.Stat.IIDSample.empiricalVar_eq_centered]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ (ψ (S.Z i ω) - S.sampleMean ψ n ω) ^ 2) n]
  simp only [one_div]

end

end Causalean.Stat
