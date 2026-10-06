module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bounded-statistic averaging over finite Poisson sample sizes

This independent module supplies the bounded finite-sample mixture identity
and the scalar Poisson generating-function calculation, including zero rate.
The exact iid count-fibre law is supplied by FinitePartition.Basic.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

variable {X : Type*} [MeasurableSpace X]

/-- Under [an observation probability law](hyp:P), [a nonnegative Poisson intensity](hyp:lambda),
[a finite-sample statistic](hyp:f) with [measurable dependence on the sample](hyp:hf), and
[a uniform real bound](hyp:C,hbound), [its finite-Poisson expectation equals the Poisson
average of its fixed-size iid expectations](goal). -/
theorem integral_finitePoissonSampleLaw_eq_integral_iid
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    (f : FiniteSample X → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ s, ‖f s‖ ≤ C) :
    (∫ s, f s ∂finitePoissonSampleLaw P lambda) =
      ∫ n : ℕ, (∫ x : Fin n → X, f (fixedSizeEmbed n x)
        ∂Measure.pi (fun _ : Fin n => P)) ∂poissonMeasure lambda := by
  have hint : Integrable (fun z : ℕ × (ℕ → X) => f (streamToFiniteSample z))
      ((poissonMeasure lambda).prod (iidStreamLaw P)) :=
    Integrable.of_bound (hf.comp measurable_streamToFiniteSample).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hbound (streamToFiniteSample z))
  unfold finitePoissonSampleLaw
  rw [integral_map measurable_streamToFiniteSample.aemeasurable hf.aestronglyMeasurable]
  unfold poissonIIDStreamLaw
  rw [integral_prod _ hint]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro n
  have hm : Measurable (fun z : ℕ → X => fun i : Fin n => z i) := by fun_prop
  have hfn := hf.comp (measurable_fixedSizeEmbed (X := X) n)
  dsimp only
  rw [← iidStreamLaw_map_finPrefix P n]
  exact (integral_map (μ := iidStreamLaw P) hm.aemeasurable
    hfn.aestronglyMeasurable).symm

/-- A [nonnegative Poisson intensity](hyp:lambda), [an event probability](hyp:p), and
[its lower and upper probability bounds](hyp:hp0,hp1) give [the Poisson average of one
minus its complement raised to the random sample size](goal). -/
theorem poisson_integral_one_sub_pow (lambda : ℝ≥0) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ n : ℕ, (1 - (1 - p) ^ n) ∂poissonMeasure lambda) =
      1 - Real.exp (-(lambda : ℝ) * p) := by
  have hpow : HasSum
      (fun n : ℕ => (Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ n /
        (n.factorial : ℝ)) * (1 - p) ^ n)
      (Real.exp (-(lambda : ℝ) * p)) := by
    convert! (NormedSpace.expSeries_div_hasSum_exp ((lambda : ℝ) * (1 - p))).mul_left
      (Real.exp (-(lambda : ℝ))) using 1
    · ext n
      rw [mul_pow]
      ring
    · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
      congr 1
      ring
  have hsum := (hasSum_one_poissonMeasure lambda).sub hpow
  rw [integral_poissonMeasure]
  convert hsum.tsum_eq using 1
  congr 1
  ext n
  simp only [smul_eq_mul]
  ring

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean
