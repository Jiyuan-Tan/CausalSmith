module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.FixedCount

/-!
# Finite Poisson nested-event ratio mean

For arbitrary probability laws and measurable nested events, the total mean
identity multiplies the success-fraction expectation by containing-event mass.
It covers zero event mass and zero intensity without division. The module also
exposes the positive-mass quotient formula and explicit degenerate cases.
-/

public section

open MeasureTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

variable {X : Type*} [MeasurableSpace X]

/-- Under [an observation probability law](hyp:P), [a nonnegative Poisson intensity](hyp:lambda),
two [events](hyp:A,B) with [measurable membership](hyp:hA,hB), and [containment of the first
in the second](hyp:hAB), [containing-event probability times the expected total success
fraction equals smaller-event probability times one minus the probability that no sample point
falls in the containing event, namely one minus the exponential of minus the intensity times the
containing-event probability](goal). The success fraction is the smaller-event count divided by
the containing-event count, set to zero when the latter count is zero. -/
theorem finitePoisson_successFraction_mean_mul
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    P.real B * (∫ s, successFraction A B s ∂finitePoissonSampleLaw P lambda) =
      P.real A * (1 - Real.exp (-(lambda : ℝ) * P.real B)) := by
  /- Apply integral_finitePoissonSampleLaw_eq_integral_iid to successFraction
  with bound C=1, supplied by successFraction_bounds and Real.norm_eq_abs.
  Move P.real B inside the outer scalar integral with integral_const_mul,
  rewrite pointwise with iid_successFraction_mean_mul, and move P.real A
  outside. poisson_integral_one_sub_pow closes the resulting scalar identity;
  its mass bounds are measureReal_nonneg and measureReal_mono to Set.univ.
  This assembly never cancels P.real B or lambda, so both degenerate cases
  remain covered. `integral_const_mul` has no integrability premise. After
  rewriting the mixture equality, a calc step using its
  symmetry moves P.real B inside the integral over poissonMeasure lambda.
  The next step is integral_congr_ae (Filter.Eventually.of_forall fun n =>
    iid_successFraction_mean_mul P n hA hB hAB).
  A forward integral_const_mul then factors out P.real A. The last scalar
  rewrite is poisson_integral_one_sub_pow lambda (P.real B), with
  hp1 obtained from measureReal_mono (Set.subset_univ B) and probReal_univ.
  For the mixture's norm bound use successFraction_bounds hAB s followed by
  rw [Real.norm_eq_abs, abs_of_nonneg ...]. No new helper layer is needed. -/
  have hp0 : 0 ≤ P.real B := measureReal_nonneg
  have hp1 : P.real B ≤ 1 := by
    simpa only [probReal_univ] using
      (measureReal_mono (μ := P) (Set.subset_univ B))
  rw [integral_finitePoissonSampleLaw_eq_integral_iid P lambda
    (successFraction A B) (measurable_successFraction hA hB) 1
    (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (successFraction_bounds hAB s).1]
      exact (successFraction_bounds hAB s).2)]
  calc
    P.real B *
        (∫ n : ℕ, (∫ x : Fin n → X, successFraction A B (fixedSizeEmbed n x)
          ∂Measure.pi (fun _ : Fin n => P)) ∂ProbabilityTheory.poissonMeasure lambda) =
        ∫ n : ℕ, P.real B *
          (∫ x : Fin n → X, successFraction A B (fixedSizeEmbed n x)
            ∂Measure.pi (fun _ : Fin n => P)) ∂ProbabilityTheory.poissonMeasure lambda :=
      (integral_const_mul _ _).symm
    _ = ∫ n : ℕ, P.real A * (1 - (1 - P.real B) ^ n)
        ∂ProbabilityTheory.poissonMeasure lambda :=
      integral_congr_ae (Filter.Eventually.of_forall fun n =>
        iid_successFraction_mean_mul P n hA hB hAB)
    _ = P.real A * (∫ n : ℕ, (1 - (1 - P.real B) ^ n)
        ∂ProbabilityTheory.poissonMeasure lambda) := integral_const_mul _ _
    _ = P.real A * (1 - Real.exp (-(lambda : ℝ) * P.real B)) := by
      rw [poisson_integral_one_sub_pow lambda (P.real B)]

/-- Under [an observation probability law](hyp:P), [a nonnegative Poisson intensity](hyp:lambda),
two [events](hyp:A,B) with [measurable membership](hyp:hA,hB), [containment of the first in
the second](hyp:hAB), and [positive containing-event probability](hyp:hPB), [the expected
total success fraction equals the event-probability ratio times the nonempty-count
probability](goal). -/
theorem finitePoisson_successFraction_mean
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hPB : 0 < P.real B) :
    (∫ s, successFraction A B s ∂finitePoissonSampleLaw P lambda) =
      (P.real A / P.real B) * (1 - Real.exp (-(lambda : ℝ) * P.real B)) := by
  have h := finitePoisson_successFraction_mean_mul P lambda hA hB hAB
  calc
    (∫ s, successFraction A B s ∂finitePoissonSampleLaw P lambda) =
        (P.real A * (1 - Real.exp (-(lambda : ℝ) * P.real B))) / P.real B := by
      apply (eq_div_iff (ne_of_gt hPB)).2
      simpa only [mul_comm] using h
    _ = (P.real A / P.real B) *
        (1 - Real.exp (-(lambda : ℝ) * P.real B)) := by ring

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean
