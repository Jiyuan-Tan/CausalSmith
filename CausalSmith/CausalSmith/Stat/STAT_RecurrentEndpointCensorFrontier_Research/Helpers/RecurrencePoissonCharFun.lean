module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrencePoissonMoments
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite Poisson recurrence characteristic functions

The independent count-and-stream construction gives the Poisson exponential
formula for measurable point scores. Partitioning by the actual count and
summing the exponential series proves the identity needed in roadmap (19).
-/

public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

variable {X : Type*} [MeasurableSpace X]

/-- For a fixed count, the iid point-score characteristic function factors. -/
-- @node: recurrence_poisson_fixed_count_charFun
lemma recurrence_poisson_fixed_count_charFun (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (f : X → ℝ) (u : ℝ) :
    (∫ x : Fin n → X, Complex.exp (Complex.I *
      (u * ∑ i, f (x i) : ℝ)) ∂Measure.pi (fun _ => P)) =
      (∫ x, Complex.exp (Complex.I * (u * f x : ℝ)) ∂P) ^ n := by
  classical
  have he (x : Fin n → X) :
      Complex.exp (Complex.I * (u * ∑ i, f (x i) : ℝ)) =
        ∏ i, Complex.exp (Complex.I * (u * f (x i) : ℝ)) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [he]
  simpa using integral_fintype_prod_eq_pow
    (ι := Fin n) (μ := P) (fun x => Complex.exp (Complex.I * (u * f x : ℝ)))

/-- A measurable finite-Poisson point score obeys the genuine exponential
formula, obtained from the Poisson count fibres rather than assumed. -/
-- @node: recurrence_poisson_sum_charFun
lemma recurrence_poisson_sum_charFun (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (u : ℝ) :
    (∫ s : FiniteSample X, Complex.exp (Complex.I *
      (u * ∑ i : Fin s.1, f (s.2 i) : ℝ)) ∂finitePoissonSampleLaw P rate) =
      Complex.exp ((rate : ℂ) *
        ((∫ x, Complex.exp (Complex.I * (u * f x : ℝ)) ∂P) - 1)) := by
  classical
  let μ := finitePoissonSampleLaw P rate
  let g : FiniteSample X → ℂ := fun s =>
    Complex.exp (Complex.I * (u * ∑ i : Fin s.1, f (s.2 i) : ℝ))
  let z : ℂ := ∫ x, Complex.exp (Complex.I * (u * f x : ℝ)) ∂P
  have hg : Measurable g := by
    dsimp [g]
    have := measurable_recurrence_poisson_sum f hf
    fun_prop
  have hi : Integrable g μ := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun s => by
      simp [g, Complex.norm_exp, Complex.mul_re])
  let S : ℕ → Set (FiniteSample X) := fun n => FiniteSample.count ⁻¹' {n}
  have hU : (⋃ n, S n) = univ := by ext s; simp [S]
  have hd : Pairwise (Disjoint on S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro s hs ht
    exact hij (by simpa [S] using hs.symm.trans ht)
  have hc (n : ℕ) : (∫ s in S n, g s ∂μ) =
      (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial : ℝ) • z ^ n := by
    rw [show μ = finitePoissonSampleLaw P rate from rfl]
    dsimp [S]
    rw [finitePoissonSampleLaw_restrict_count_eq, integral_smul_measure,
      integral_map (measurable_fixedSizeEmbed n).aemeasurable hg.aestronglyMeasurable]
    have he := recurrence_poisson_fixed_count_charFun P n f u
    change (poissonMeasure rate {n}).toReal •
      (∫ x : Fin n → X, Complex.exp (Complex.I *
        (u * ∑ i, f (x i) : ℝ)) ∂Measure.pi (fun _ => P)) = _
    rw [he, poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hp := integral_iUnion (μ := μ) (f := g)
    (fun n => measurable_finiteSample_count (measurableSet_singleton n)) hd
    (show IntegrableOn g (⋃ n, S n) μ by simpa [hU] using hi)
  rw [hU, Measure.restrict_univ] at hp
  change (∫ s, g s ∂μ) = _
  rw [hp]
  change (∑' n : ℕ, ∫ s in S n, g s ∂μ) = _
  simp_rw [hc]
  calc
    (∑' n : ℕ, (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / n.factorial : ℝ) • z ^ n) =
        (Real.exp (-(rate : ℝ)) : ℂ) *
          ∑' n : ℕ, ((rate : ℂ) * z) ^ n / n.factorial := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_natCast, mul_pow]
      ring
    _ = (Real.exp (-(rate : ℝ)) : ℂ) * Complex.exp ((rate : ℂ) * z) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((rate : ℂ) * z)).tsum_eq,
        ← Complex.exp_eq_exp_ℂ]
    _ = _ := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring

/-- Compensation subtracts the linear part of the Poisson exponent, giving
exactly the exponential kernel used in the critical Taylor expansion. -/
-- @node: recurrence_poisson_compensated_charFun
lemma recurrence_poisson_compensated_charFun (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f P) (u : ℝ) :
    (∫ s : FiniteSample X, Complex.exp (Complex.I *
      (u * ((∑ i : Fin s.1, f (s.2 i)) -
        (rate : ℝ) * ∫ x, f x ∂P) : ℝ)) ∂finitePoissonSampleLaw P rate) =
      Complex.exp ((rate : ℂ) * ∫ x,
        (Complex.exp (Complex.I * (u * f x : ℝ)) - 1 -
          Complex.I * (u * f x : ℝ)) ∂P) := by
  have he : Integrable (fun x => Complex.exp (Complex.I * (u * f x : ℝ))) P := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => by
      simp [Complex.norm_exp, Complex.mul_re])
  have hl : Integrable (fun x => Complex.I * (u * f x : ℝ)) P := by
    exact (hfi.const_mul u).ofReal.const_mul Complex.I
  have hk : (∫ x, (Complex.exp (Complex.I * (u * f x : ℝ)) - 1 -
        Complex.I * (u * f x : ℝ)) ∂P) =
      (∫ x, Complex.exp (Complex.I * (u * f x : ℝ)) ∂P) - 1 -
        Complex.I * (u * ∫ x, f x ∂P : ℝ) := by
    have hs : Integrable (fun x => Complex.exp (Complex.I * (u * f x : ℝ)) - 1) P :=
      he.sub (integrable_const (1 : ℂ))
    rw [integral_sub hs hl,
      integral_sub he (integrable_const (1 : ℂ)), integral_const,
      integral_const_mul, integral_complex_ofReal, integral_const_mul]
    simp
  have hp (s : FiniteSample X) :
      Complex.exp (Complex.I *
        (u * ((∑ i : Fin s.1, f (s.2 i)) -
          (rate : ℝ) * ∫ x, f x ∂P) : ℝ)) =
        Complex.exp (-(Complex.I * (u * (rate : ℝ) * ∫ x, f x ∂P : ℝ))) *
          Complex.exp (Complex.I * (u * ∑ i : Fin s.1, f (s.2 i) : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [integral_const_mul, recurrence_poisson_sum_charFun P rate f hf u,
    ← Complex.exp_add, hk]
  congr 1
  push_cast
  ring

/-- Conditional on a fixed exposure array, independent subject Poisson
scores have the sum of their compensated exponents. -/
-- @node: recurrence_poisson_iid_compensated_charFun
lemma recurrence_poisson_iid_compensated_charFun (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ j, Measurable (f j)) (hfi : ∀ j, Integrable (f j) P) (u : ℝ) :
    (∫ z : Fin n → FiniteSample X, Complex.exp (Complex.I *
      (u * recurrenceExposureScore P rate n (fun _ : Unit => f) () z : ℝ))
      ∂Measure.pi (fun _ => finitePoissonSampleLaw P rate)) =
      Complex.exp (∑ j : Fin n, (rate : ℂ) * ∫ x,
        (Complex.exp (Complex.I * (u * f j x : ℝ)) - 1 -
          Complex.I * (u * f j x : ℝ)) ∂P) := by
  classical
  have hp (z : Fin n → FiniteSample X) :
      Complex.exp (Complex.I *
        (u * recurrenceExposureScore P rate n (fun _ : Unit => f) () z : ℝ)) =
        ∏ j : Fin n, Complex.exp (Complex.I *
          (u * ((∑ i : Fin (z j).1, f j ((z j).2 i)) -
            (rate : ℝ) * ∫ x, f j x ∂P) : ℝ)) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [recurrenceExposureScore, Complex.ofReal_mul, Complex.ofReal_sum,
      Finset.mul_sum]
  simp_rw [hp]
  rw [integral_fintype_prod_eq_prod (fun j (s : FiniteSample X) =>
    Complex.exp (Complex.I * (u * ((∑ i : Fin s.1, f j (s.2 i)) -
      (rate : ℝ) * ∫ x, f j x ∂P) : ℝ)))]
  simp_rw [recurrence_poisson_compensated_charFun P rate _ (hf _) (hfi _) u]
  rw [Complex.exp_sum]

/-- Averaging the fixed-exposure Poisson characteristic function over an
independent exposure law gives the unconditional formula. Unit modulus
supplies global integrability without an averaged score moment assumption. -/
-- @node: recurrence_poisson_random_exposure_charFun
lemma recurrence_poisson_random_exposure_charFun
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [IsProbabilityMeasure Q]
    (P : Measure X) [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ)
    (f : E → Fin n → X → ℝ)
    (hf : ∀ e j, Measurable (f e j)) (hfi : ∀ e j, Integrable (f e j) P)
    (hscore : Measurable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2)) (u : ℝ) :
    (∫ p : E × (Fin n → FiniteSample X), Complex.exp (Complex.I *
      (u * recurrenceExposureScore P rate n f p.1 p.2 : ℝ))
      ∂Q.prod (Measure.pi (fun _ => finitePoissonSampleLaw P rate))) =
    ∫ e, Complex.exp (∑ j : Fin n, (rate : ℂ) * ∫ x,
      (Complex.exp (Complex.I * (u * f e j x : ℝ)) - 1 -
        Complex.I * (u * f e j x : ℝ)) ∂P) ∂Q := by
  have hi : Integrable (fun p : E × (Fin n → FiniteSample X) =>
      Complex.exp (Complex.I *
        (u * recurrenceExposureScore P rate n f p.1 p.2 : ℝ)))
      (Q.prod (Measure.pi (fun _ => finitePoissonSampleLaw P rate))) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun p => by
      simp [Complex.norm_exp, Complex.mul_re])
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun e =>
    recurrence_poisson_iid_compensated_charFun P rate n (f e) (hf e) (hfi e) u)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
