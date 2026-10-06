module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.PoissonMixture
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Zero-count probabilities and degenerate success-fraction means

The iid zero-count event is a product of complement events. Averaging its
probability over a Poisson size gives the exponential empty-event probability.
Zero containing-event mass and zero intensity then yield zero success fractions
almost surely or in expectation, independently of the positive-count ratio proof.
-/

public section

open MeasureTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

variable {X : Type*} [MeasurableSpace X]

/-- Under [an observation probability law](hyp:P), [a tuple size](hyp:n), and [an event
with measurable membership](hyp:B,hB), [the probability that its iid event count is zero
equals the complement probability raised to the tuple size](goal). -/
theorem iid_eventCount_zero_probability
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ)
    {B : Set X} (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin n => P)).real {x | iidEventCount B x = 0} =
      (1 - P.real B) ^ n := by
  /- Identify the zero-count set with Set.univ.pi (fun _ : Fin n => Bᶜ)
  using nonnegativity of every zero-one summand. Apply Measure.pi_pi,
  ENNReal.toReal_prod, measureReal_compl, and probability mass of univ.
  This is a product probability calculation, with no ratio lemma dependency. -/
  classical
  have hset : {x : Fin n → X | iidEventCount B x = 0} =
      Set.univ.pi (fun _ : Fin n => Bᶜ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_compl_iff, iidEventCount]
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => by split_ifs <;> norm_num)]
    simp
  rw [hset, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp [← measureReal_def, measureReal_compl hB]

/-- Under [an observation probability law](hyp:P), [a nonnegative Poisson intensity](hyp:lambda),
and [an event with measurable membership](hyp:B,hB), [the probability of no sample point in
the event equals the exponential of its negative intensity](goal). -/
theorem finitePoisson_eventCount_zero_probability
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    {B : Set X} (hB : MeasurableSet B) :
    (finitePoissonSampleLaw P lambda).real {s | eventCount B s = 0} =
      Real.exp (-(lambda : ℝ) * P.real B) := by
  /- Average the bounded indicator of the zero-count event, use
  iid_eventCount_zero_probability, then the scalar generating-function result.
  This also supplies an economical proof of the zero-mass ae result below. -/
  classical
  let E : Set (FiniteSample X) := {s | eventCount B s = 0}
  have hE : MeasurableSet E :=
    (measurable_eventCount hB) (measurableSet_singleton 0)
  have hmix := integral_finitePoissonSampleLaw_eq_integral_iid P lambda
    (E.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hE) 1 (fun s => by
      by_cases hs : s ∈ E <;> simp [Set.indicator, hs])
  rw [integral_indicator_const 1 hE] at hmix
  simp only [smul_eq_mul, mul_one] at hmix
  have hiid : ∀ n : ℕ,
      (∫ x : Fin n → X, E.indicator (fun _ => (1 : ℝ)) (fixedSizeEmbed n x)
        ∂Measure.pi (fun _ : Fin n => P)) = (1 - P.real B) ^ n := by
    intro n
    have heq : (fun x : Fin n → X =>
        E.indicator (fun _ => (1 : ℝ)) (fixedSizeEmbed n x)) =
        {x : Fin n → X | iidEventCount B x = 0}.indicator (fun _ => (1 : ℝ)) := by
      ext x
      simp [E, Set.indicator]
    have hn : MeasurableSet {x : Fin n → X | iidEventCount B x = 0} :=
      (measurable_iidEventCount hB n) (measurableSet_singleton 0)
    rw [heq, integral_indicator_const (1 : ℝ) hn]
    simpa using iid_eventCount_zero_probability P n hB
  simp_rw [hiid] at hmix
  have hp0 : 0 ≤ P.real B := measureReal_nonneg
  have hp1 : P.real B ≤ 1 := by
    exact (measureReal_mono (μ := P) (Set.subset_univ B)).trans (by simp)
  have hint : Integrable (fun n : ℕ => (1 - P.real B) ^ n)
      (ProbabilityTheory.poissonMeasure lambda) :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hp1) n)]
        exact pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith))
  have hgen := poisson_integral_one_sub_pow lambda (P.real B) hp0 hp1
  rw [integral_sub (integrable_const 1) hint] at hgen
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hgen
  change (finitePoissonSampleLaw P lambda).real E = _
  linarith

/-- Under [an observation probability law](hyp:P), [a nonnegative Poisson intensity](hyp:lambda),
two [events](hyp:A,B) with [measurable membership](hyp:hA,hB), [containment of the first in
the second](hyp:hAB), and [zero containing-event mass](hyp:hPB), [the total success
fraction is almost surely zero](goal). -/
theorem successFraction_ae_zero_of_mass_zero
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hPB : P B = 0) :
    successFraction A B =ᵐ[finitePoissonSampleLaw P lambda] (fun _ => 0) := by
  /- Use finitePoisson_eventCount_zero_probability with P.real B=0 to show
  the measurable zero-count event has probability one. On that event the
  explicit successFraction branch is zero. A private helper converting
  real probability one of a measurable set to almost-sure membership can
  also discharge the zero-intensity theorem. No cancellation of event mass
  or use of the open ratio-mean identity is allowed here. -/
  classical
  have hE : MeasurableSet {s : FiniteSample X | eventCount B s = 0} :=
    (measurable_eventCount hB) (measurableSet_singleton 0)
  have hprob := finitePoisson_eventCount_zero_probability P lambda hB
  have hreal : P.real B = 0 := by simp [measureReal_def, hPB]
  rw [hreal, mul_zero, Real.exp_zero] at hprob
  have hae := (mem_ae_iff_prob_eq_one hE).2
    ((ENNReal.toReal_eq_one_iff _).1 hprob)
  filter_upwards [hae] with s hs
  simp [successFraction, Set.mem_ofPred_eq.mp hs]

/-- Under [an observation probability law](hyp:P), [a nonnegative Poisson intensity](hyp:lambda),
two [events](hyp:A,B) with [measurable membership](hyp:hA,hB), [containment of the first in
the second](hyp:hAB), and [zero containing-event mass](hyp:hPB), [the expected total
success fraction is zero](goal). -/
theorem finitePoisson_successFraction_mean_of_mass_zero
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hPB : P B = 0) :
    (∫ s, successFraction A B s ∂finitePoissonSampleLaw P lambda) = 0 := by
  rw [integral_congr_ae (successFraction_ae_zero_of_mass_zero P lambda hA hB hAB hPB)]
  simp

/-- Under [an observation probability law](hyp:P), two [events](hyp:A,B) with [measurable
membership](hyp:hA,hB) and [containment of the first in the second](hyp:hAB), [the expected
total success fraction at zero Poisson intensity is zero](goal). -/
theorem finitePoisson_successFraction_mean_zero_intensity
    (P : Measure X) [IsProbabilityMeasure P]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    (∫ s, successFraction A B s ∂finitePoissonSampleLaw P 0) = 0 := by
  /- finitePoisson_eventCount_zero_probability at rate zero gives probability
  one of zero B-count, irrespective of P(B). Conclude the integrand is ae zero
  by its zero branch and use integral_congr_ae. Alternatively apply the closed
  bounded mixture identity and the scalar zero-rate Dirac law. Do not depend
  on the headline ratio mean (which belongs to a later import layer). -/
  classical
  have hE : MeasurableSet {s : FiniteSample X | eventCount B s = 0} :=
    (measurable_eventCount hB) (measurableSet_singleton 0)
  have hprob := finitePoisson_eventCount_zero_probability P 0 hB
  simp only [NNReal.coe_zero, neg_zero, zero_mul, Real.exp_zero] at hprob
  have hae := (mem_ae_iff_prob_eq_one hE).2
    ((ENNReal.toReal_eq_one_iff _).1 hprob)
  have hzero : successFraction A B =ᵐ[finitePoissonSampleLaw P 0] (fun _ => 0) := by
    filter_upwards [hae] with s hs
    simp [successFraction, Set.mem_ofPred_eq.mp hs]
  rw [integral_congr_ae hzero]
  simp

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean
