module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.Envelope
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.FixedCount

/-!
# Exact-count fibres for nested-event factorial moments

The fixed-count iid identity is transported to each count fibre of the finite
Poisson sample law. The result is total at zero Poisson mass and zero event mass.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

/-- Under an [observation probability law](hyp:P), a [Poisson intensity](hyp:lam), two
[events](hyp:A,B) with [measurable membership](hyp:hA,hB) and [the first contained in the
second](hyp:hAB), an [order](hyp:v) with [positive order](hyp:hv), and a [sample-size
fibre](hyp:n), the [integral of the weighted nested-event factorial over the samples of exactly
that size, under the finite Poisson sample law, equals the Poisson probability of that size times
the falling factorial of the size of the given order, times the smaller-event probability, times
the larger-event probability raised to the order minus one](goal). -/
theorem integral_weightedFactorial_countFibre
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (v n : ℕ) (hv : 1 ≤ v) :
    (∫ s, weightedFactorial A B v s ∂
      (finitePoissonSampleLaw P lam).restrict
        (FiniteSample.count ⁻¹' ({n} : Set ℕ))) =
      ((poissonMeasure lam) ({n} : Set ℕ)).toReal *
        (n.descFactorial v : ℝ) * (P A).toReal * (P B).toReal ^ (v - 1) := by
  rw [finitePoissonSampleLaw_restrict_count_eq, integral_smul_measure]
  rw [integral_map (measurable_fixedSizeEmbed n).aemeasurable
    (measurable_weightedFactorial A B hA hB v).aestronglyMeasurable]
  rw [integral_weightedFactorial_fixedCount P A B hA hB hAB v n hv]
  simp only [smul_eq_mul]
  ring

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
