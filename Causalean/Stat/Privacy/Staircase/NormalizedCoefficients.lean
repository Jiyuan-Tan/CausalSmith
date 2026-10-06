module
public import Causalean.Stat.Privacy.Staircase.CoefficientMeasures

/-!
# Normalizing coefficient measures

The measurable staircase coefficients define finite measures on the output space.
Their masses are the ray weights, and each measure is a weight times a probability
measure. A zero-mass coefficient uses an arbitrary Markov row as its fallback.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

variable {Z : Type*} [MeasurableSpace Z]

/-- The contribution measure of one nonconstant staircase ray is its coefficient
as a density against the common sum of the four Markov rows. -/
def coefficientMeasure (Q : Kernel (Fin 4) Z) (D : CoefficientField Q r)
    (S : RayIndex) : Measure Z :=
  (rowSum Q).withDensity (fun z => ENNReal.ofReal (D.c z S))

/-- The total mass of a staircase coefficient measure equals the real integral of
its coefficient, embedded in the extended nonnegative reals. -/
theorem coefficientMeasure_mass (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r) (S : RayIndex) :
    coefficientMeasure Q D S Set.univ =
      ENNReal.ofReal (∫ z, D.c z S ∂rowSum Q) := by
  rw [coefficientMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  exact (ofReal_integral_eq_lintegral_ofReal
    (coefficient_integrable Q r hr D S)
    (Filter.Eventually.of_forall fun z => D.nonneg z S)).symm

/-- For [a four-input Markov kernel](hyp:Q), [a privacy ratio greater than one](hyp:hr) at
[the supplied ratio](hyp:r), and [a measurable staircase coefficient field](hyp:D), a
[Markov postprocessing kernel representing every ray coefficient measure](goal) exists,
including zero-weight rays.

Every measurable ray coefficient measure is a nonnegative scalar multiple of
a Markov postprocessing row, including the zero-weight case. -/
theorem exists_coefficientPostprocess (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r) :
    ∃ K : Kernel RayIndex Z, IsMarkovKernel K ∧
      ∀ S : RayIndex,
        coefficientMeasure Q D S =
          ENNReal.ofReal (∫ z, D.c z S ∂rowSum Q) • K S := by
  let : Nonempty Z := nonempty_of_isProbabilityMeasure (Q 0)
  let ν : RayIndex → FiniteMeasure Z := fun S =>
    ⟨coefficientMeasure Q D S,
      isFiniteMeasure_withDensity_ofReal
        (coefficient_integrable Q r hr D S).hasFiniteIntegral⟩
  let K : Kernel RayIndex Z := Kernel.ofFunOfCountable fun S =>
    if (ν S).mass = 0 then Q 0 else (ν S).normalize
  refine ⟨K, ?_, ?_⟩
  · constructor
    intro S
    change IsProbabilityMeasure
      (if (ν S).mass = 0 then Q 0 else ((ν S).normalize : Measure Z))
    split_ifs <;> infer_instance
  · intro S
    have hmass : ((ν S).mass : ℝ≥0∞) =
        ENNReal.ofReal (∫ z, D.c z S ∂rowSum Q) := by
      rw [FiniteMeasure.ennreal_mass]
      exact coefficientMeasure_mass Q r hr D S
    change (ν S : Measure Z) =
      ENNReal.ofReal (∫ z, D.c z S ∂rowSum Q) • K S
    rw [← hmass]
    by_cases hzero : (ν S).mass = 0
    · have hν : ν S = 0 := (ν S).mass_zero_iff.mp hzero
      simp [K, hν]
    · apply Measure.ext
      intro s hs
      simp only [K, Kernel.ofFunOfCountable, Kernel.coe_mk, if_neg hzero]
      rw [Measure.smul_apply, smul_eq_mul]
      have h := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
        ((ν S).self_eq_mass_mul_normalize s)
      simpa only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h

end Causalean.Stat.Privacy.Staircase
