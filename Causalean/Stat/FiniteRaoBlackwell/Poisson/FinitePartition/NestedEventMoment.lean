module
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.Fibre

/-!
# Nested-event factorial moment of a finite Poisson sample

The fixed-count identity is mixed over the Poisson sample size to give a total,
division-free joint factorial moment. A positive-mass corollary expresses the
same identity as a conditional-mean proportion of the larger-event moment.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

/-- Under an [observation probability law](hyp:P), a [Poisson intensity](hyp:lam), two
[events](hyp:A,B) with [measurable membership](hyp:hA,hB) and [the first contained in the
second](hyp:hAB), and an [order](hyp:v) with [positive order](hyp:hv), the [weighted
nested-event factorial is integrable under the finite Poisson sample law](goal). -/
theorem integrable_weightedFactorial (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (v : ℕ) (hv : 1 ≤ v) :
    Integrable (weightedFactorial A B v) (finitePoissonSampleLaw P lam) := by
  /- Bound the nonnegative statistic by count.descFactorial v after the
     ordered-tuple expansion (weightedFactorial_nonneg_le_countFactorial),
     then use poisson_descFactorial_integrable and
     finitePoissonSampleLaw_map_count. The measurable_weightedFactorial
     lemma supplies strong measurability. -/
  have hcount : Integrable
      (fun s : FiniteSample X => (s.count.descFactorial v : ℝ))
      (finitePoissonSampleLaw P lam) := by
    have h := Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      lam v
    rw [← finitePoissonSampleLaw_map_count P lam] at h
    simpa only [Function.comp_def] using h.comp_aemeasurable
      measurable_finiteSample_count.aemeasurable
  exact integrable_of_le_of_le
    (measurable_weightedFactorial A B hA hB v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s =>
      (weightedFactorial_nonneg_le_countFactorial A B hAB v hv s).1)
    (Filter.Eventually.of_forall fun s =>
      (weightedFactorial_nonneg_le_countFactorial A B hAB v hv s).2)
    (integrable_zero _ _ _) hcount

/-- Under an [observation probability law](hyp:P), a [Poisson intensity](hyp:lam), two
[events](hyp:A,B) with [measurable membership](hyp:hA,hB) and [the first contained in the
second](hyp:hAB), and an [order](hyp:v) with [positive order](hyp:hv), the [expectation, under the
finite Poisson sample law, of the smaller-event count times the falling factorial of order one
less than the given order of the larger-event count minus one equals the intensity raised to the
order, times the smaller-event probability, times the larger-event probability raised to the
order minus one](goal). -/
theorem finitePoisson_nestedEvent_factorialMoment
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (v : ℕ) (hv : 1 ≤ v) :
    (∫ s, weightedFactorial A B v s ∂finitePoissonSampleLaw P lam) =
      (lam : ℝ) ^ v * (P A).toReal * (P B).toReal ^ (v - 1) := by
  /- Disintegrate along the measurable sample count. On fibre n, use
     integral_weightedFactorial_countFibre.
     The resulting Poisson sum is the scalar descFactorial moment. The
     integrability lemma licenses countable integral interchange. -/
  let μ := finitePoissonSampleLaw P lam
  let S : ℕ → Set (FiniteSample X) := fun n =>
    FiniteSample.count ⁻¹' ({n} : Set ℕ)
  have hdis : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro s hi hj
    exact hij (hi.symm.trans hj)
  have hcover : (⋃ n, S n) = Set.univ := by
    ext s
    simp [S]
  have hsum : μ = Measure.sum (fun n => μ.restrict (S n)) := by
    calc
      μ = μ.restrict Set.univ := (Measure.restrict_univ).symm
      _ = μ.restrict (⋃ n, S n) := by rw [hcover]
      _ = Measure.sum (fun n => μ.restrict (S n)) :=
        Measure.restrict_iUnion hdis
          (fun n => measurable_finiteSample_count (MeasurableSet.singleton n))
  have hf : Integrable (weightedFactorial A B v) μ :=
    integrable_weightedFactorial P lam A B hA hB hAB v hv
  have hscalar : Integrable (fun n : ℕ => (n.descFactorial v : ℝ))
      (poissonMeasure lam) :=
    Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable lam v
  have hs : Summable (fun n : ℕ =>
      ((poissonMeasure lam) {n}).toReal * (n.descFactorial v : ℝ)) := by
    rw [← Measure.sum_smul_dirac (poissonMeasure lam)] at hscalar
    simpa using hscalar.summable_of_dirac
  calc
    (∫ s, weightedFactorial A B v s ∂μ) =
        ∑' n, ∫ s, weightedFactorial A B v s ∂μ.restrict (S n) := by
      conv_lhs => rw [hsum]
      exact integral_sum_measure (hsum ▸ hf)
    _ = ∑' n, (((poissonMeasure lam) {n}).toReal *
        (n.descFactorial v : ℝ)) *
        ((P A).toReal * (P B).toReal ^ (v - 1)) := by
      congr 1
      funext n
      rw [integral_weightedFactorial_countFibre P lam A B hA hB hAB v n hv]
      ring
    _ = (∑' n, ((poissonMeasure lam) {n}).toReal *
        (n.descFactorial v : ℝ)) *
        ((P A).toReal * (P B).toReal ^ (v - 1)) :=
      hs.tsum_mul_right _
    _ = (lam : ℝ) ^ v * (P A).toReal * (P B).toReal ^ (v - 1) := by
      have hm := Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment lam v
      rw [integral_countable hscalar] at hm
      have hseries : (∑' n, ((poissonMeasure lam) {n}).toReal *
          (n.descFactorial v : ℝ)) = (lam : ℝ) ^ v := by
        simpa only [measureReal_def, smul_eq_mul] using hm
      rw [hseries]
      ring

/-- Under an [observation probability law](hyp:P), a [Poisson intensity](hyp:lam), two
[events](hyp:A,B) with [measurable membership](hyp:hA,hB) and [the first contained in the
second](hyp:hAB), [positive larger-event probability](hyp:hBpos), and an [order](hyp:v)
with [positive order](hyp:hv), the [nested weighted factorial moment equals the
event-probability ratio times the containing-event factorial moment](goal). -/
theorem finitePoisson_nestedEvent_conditionalMean
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hBpos : 0 < (P B).toReal)
    (v : ℕ) (hv : 1 ≤ v) :
    (∫ s, weightedFactorial A B v s ∂finitePoissonSampleLaw P lam) =
      ((P A).toReal / (P B).toReal) *
        (∫ s, weightedFactorial B B v s ∂finitePoissonSampleLaw P lam) := by
  rw [finitePoisson_nestedEvent_factorialMoment P lam A B hA hB hAB v hv,
    finitePoisson_nestedEvent_factorialMoment P lam B B hB hB
      (Set.Subset.refl B) v hv]
  field_simp [ne_of_gt hBpos]

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
