module
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Causalean.Stat.RecurrentEvent.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite Poisson sum formula

The expectation of a nonnegative sum over a finite Poisson sample is the
integral against its primitive intensity measure. This is the independent
count-and-stream calculation used by the stopped-event identities.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {A : Type*} [MeasurableSpace A]

/-- [An observation law](hyp:P), [a nonnegative Poisson rate](hyp:rate), and
[a measurable nonnegative score](hyp:f,hf) give [an expected finite-sample
sum equal to its integral against the rate-scaled observation law](goal). -/
theorem finitePoissonSample_lintegral_sum (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ s,
      ∑ i : Fin s.1, f (s.2 i)
      ∂Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        P rate) =
      ∫⁻ x, f x ∂((rate : ℝ≥0∞) • P) := by
  /- Partition by the Poisson count using the finite-sample count-fibre
  theorem; exchange the finite point sum with the iid product integral;
  finish with the first moment of the scalar Poisson count. -/
  classical
  let μ := Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw P rate
  let g : Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X → ℝ≥0∞ :=
    fun s => ∑ i : Fin s.1, f (s.2 i)
  have hg : Measurable g := by
    intro t ht
    change @MeasurableSet _
      (⨅ n, (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)) (g ⁻¹' t)
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change MeasurableSet ((fun x : Fin n → X => ∑ i, f (x i)) ⁻¹' t)
    exact (Finset.measurable_sum _
      (fun i _ => hf.comp (measurable_pi_apply i))) ht
  have hcount (n : ℕ) :
      (∫⁻ s, g s ∂μ.restrict
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample.count ⁻¹'
          ({n} : Set ℕ))) =
      (poissonMeasure rate) {n} * (n : ℝ≥0∞) * (∫⁻ x, f x ∂P) := by
    rw [finitePoissonSampleLaw_restrict_count_eq]
    rw [lintegral_smul_measure,
      lintegral_map hg
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_fixedSizeEmbed n)]
    change (poissonMeasure rate) {n} *
      (∫⁻ x : Fin n → X, ∑ i : Fin n, f (x i) ∂Measure.pi (fun _ => P)) = _
    rw [lintegral_finsetSum]
    swap
    · intro i _
      exact hf.comp (measurable_pi_apply i)
    have hi (i : Fin n) :
        (∫⁻ x : Fin n → X, f (x i) ∂Measure.pi (fun _ => P)) =
          ∫⁻ x, f x ∂P := by
      exact (measurePreserving_eval (μ := fun _ : Fin n => P) i).lintegral_comp hf
    simp only [hi, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    simp [mul_assoc]
  have hpart :
      (∫⁻ s, g s ∂μ) =
        ∑' n : ℕ, ∫⁻ s, g s ∂μ.restrict
          (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample.count ⁻¹'
            ({n} : Set ℕ)) := by
    let S : ℕ → Set (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X) :=
      fun n => Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample.count ⁻¹'
        ({n} : Set ℕ)
    have hU : (⋃ n, S n) = Set.univ := by
      ext s
      simp [S]
    rw [← lintegral_iUnion (μ := μ) (s := S)]
    · simp [hU, S]
    · intro n
      exact measurable_finiteSample_count (X := X) (MeasurableSet.singleton n)
    · intro i j hij
      exact Set.disjoint_left.mpr (by
        intro s hi hj
        exact hij (by simpa [S] using hi.symm.trans hj))
  rw [hpart]
  simp_rw [hcount]
  rw [ENNReal.tsum_mul_right]
  have hm : (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure rate) =
      (rate : ℝ≥0∞) := by
    have h := Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment rate
    have hi := (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rate).integrable
      (by norm_num)
    have hr := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun n : ℕ => Nat.cast_nonneg n))
    rw [h] at hr
    simpa [ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal] using hr.symm
  have hsum : (∑' n : ℕ, (poissonMeasure rate) {n} * (n : ℝ≥0∞)) =
      (rate : ℝ≥0∞) := by
    rw [lintegral_countable'] at hm
    simpa only [mul_comm] using hm
  rw [hsum, lintegral_smul_measure, smul_eq_mul]

/-- [A recurrent-event model](hyp:M) and [a measurable nonnegative time
score](hyp:f,hf) give [a Poisson event-time sum whose mean is the integral
against the model's time intensity](goal). -/
theorem Model.poisson_time_lintegral (M : Model A X) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (letI := M.pointProb
     ∫⁻ s,
       ∑ i : Fin s.1, f (M.time (s.2 i))
       ∂Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
         M.pointLaw M.poissonRate) =
      ∫⁻ t in Ico (0 : ℝ) M.horizon,
        f t * (M.intensity t : ℝ≥0∞) ∂volume := by
  letI := M.pointProb
  calc
    (∫⁻ s, ∑ i : Fin s.1, f (M.time (s.2 i))
        ∂finitePoissonSampleLaw M.pointLaw M.poissonRate) =
        ∫⁻ x, (f ∘ M.time) x ∂((M.poissonRate : ℝ≥0∞) • M.pointLaw) :=
      finitePoissonSample_lintegral_sum M.pointLaw M.poissonRate
        (f ∘ M.time) (hf.comp M.measurable_time)
    _ = ∫⁻ t, f t ∂Measure.map M.time
        ((M.poissonRate : ℝ≥0∞) • M.pointLaw) :=
      (lintegral_map hf M.measurable_time).symm
    _ = ∫⁻ t in Ico (0 : ℝ) M.horizon,
        f t * (M.intensity t : ℝ≥0∞) ∂volume := by
      rw [M.primitive_intensity,
        lintegral_withDensity_eq_lintegral_mul _
          M.measurable_intensity.coe_nnreal_ennreal hf]
      congr 1
      funext t
      exact mul_comm _ _

/-- [A recurrent-event model](hyp:M) and [a fixed death time](hyp:d) give [a
mean primitive recurrence count equal to intensity integrated before that
death time and the fixed horizon](goal). -/
theorem Model.poisson_count_before_death (M : Model A X) (d : ℝ) :
    (letI := M.pointProb
     ∫⁻ s,
      ∑ i : Fin s.1,
        if M.time (s.2 i) < d ∧ M.time (s.2 i) < M.horizon
        then (1 : ℝ≥0∞) else 0
      ∂Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        M.pointLaw M.poissonRate) =
      ∫⁻ t in Ico (0 : ℝ) M.horizon,
        if t < d then (M.intensity t : ℝ≥0∞) else 0 ∂volume := by
  letI := M.pointProb
  /- Apply `M.poisson_time_lintegral` to the measurable indicator
  `fun t => if t < d ∧ t < M.horizon then 1 else 0`. On `Ico 0 M.horizon`,
  the second inequality is automatic; simplify the indicator and use
  `lintegral_congr` for the resulting pointwise equality. Keep the strict
  death inequality: an atom of the independent death law is removed only
  after averaging, not in this fixed-death identity. -/
  have hf : Measurable (fun t : ℝ =>
      if t < d ∧ t < M.horizon then (1 : ℝ≥0∞) else 0) := by
    exact Measurable.ite (measurableSet_Iio.inter measurableSet_Iio)
      measurable_const measurable_const
  calc
    (∫⁻ s,
      ∑ i : Fin s.1,
        if M.time (s.2 i) < d ∧ M.time (s.2 i) < M.horizon
        then (1 : ℝ≥0∞) else 0
      ∂finitePoissonSampleLaw M.pointLaw M.poissonRate) =
        ∫⁻ t in Ico (0 : ℝ) M.horizon,
          (if t < d ∧ t < M.horizon then (1 : ℝ≥0∞) else 0) *
            (M.intensity t : ℝ≥0∞) ∂volume :=
      M.poisson_time_lintegral _ hf
    _ = ∫⁻ t in Ico (0 : ℝ) M.horizon,
          if t < d then (M.intensity t : ℝ≥0∞) else 0 ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ico
      intro t ht
      have hth : t < M.horizon := ht.2
      by_cases htd : t < d <;> simp [htd, hth]

end Causalean.Stat.RecurrentEvent
