module
public import Causalean.Stat.Privacy.Staircase.NormalizedCoefficients

/-!
# Finite release from normalized staircase coefficients

The integrated coefficients define a probability distribution on the fourteen rays for
each input. This module isolates the finite release construction from output postprocessing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

variable {Z : Type*} [MeasurableSpace Z]

/-- For [a four-input Markov kernel](hyp:Q), [a privacy ratio greater than one](hyp:hr) at
[the supplied ratio](hyp:r), and [a measurable staircase coefficient field](hyp:D), a
[finite Markov release with the integrated ray weights](goal) exists.

The nonnegative integrals of a coefficient field are feasible weights for a
four-input Markov release on the fourteen nonconstant staircase rays. Each singleton
mass is exactly its weight times the corresponding ray coordinate.

Proof plan: use `coefficient_integrable` and `D.nonneg` to package each integral as
`ℝ≥0`, then `coefficient_normalized` for total mass one. Define each release row as
the finite sum of weighted Dirac measures and use `Kernel.ofFunOfCountable`.
`Measure.sum_fintype` and `Measure.dirac_apply_of_mem` identify singleton masses. -/
theorem exists_coefficientRelease (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r) :
    ∃ (α : RayIndex → ℝ≥0) (T : Kernel (Fin 4) RayIndex),
      IsMarkovKernel T ∧
      (∀ S, (α S : ℝ) = ∫ z, D.c z S ∂rowSum Q) ∧
      (∀ i, ∑ S, (α S : ℝ) * ray r S i = 1) ∧
      ∀ i S, T i {S} = (α S : ℝ≥0∞) * ENNReal.ofReal (ray r S i) := by
  let α : RayIndex → ℝ≥0 := fun S =>
    ⟨∫ z, D.c z S ∂rowSum Q, integral_nonneg (fun z => D.nonneg z S)⟩
  have hα (S : RayIndex) : (α S : ℝ) = ∫ z, D.c z S ∂rowSum Q := rfl
  have hnorm (i : Fin 4) : ∑ S, (α S : ℝ) * ray r S i = 1 := by
    simpa only [hα] using coefficient_normalized Q r hr D i
  let T : Kernel (Fin 4) RayIndex := Kernel.ofFunOfCountable fun i =>
    Measure.sum fun S : RayIndex =>
      ENNReal.ofReal ((α S : ℝ) * ray r S i) • Measure.dirac S
  refine ⟨α, T, ?_, hα, hnorm, ?_⟩
  · constructor
    intro i
    change IsProbabilityMeasure
      (Measure.sum fun S : RayIndex =>
        ENNReal.ofReal ((α S : ℝ) * ray r S i) • Measure.dirac S)
    apply HasSum.isProbabilityMeasure_sum_dirac
    · intro S
      exact mul_nonneg (α S).property (by
        unfold ray
        split_ifs <;> linarith)
    · simpa only [hnorm i] using
        (hasSum_fintype (fun S : RayIndex => (α S : ℝ) * ray r S i))
  · intro i S
    change (Measure.sum fun U : RayIndex =>
      ENNReal.ofReal ((α U : ℝ) * ray r U i) • Measure.dirac U) {S} = _
    rw [Measure.sum_smul_dirac_singleton]
    simpa using ENNReal.ofReal_mul (α S).property (y := ray r S i)

end Causalean.Stat.Privacy.Staircase
