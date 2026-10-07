module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Basic

/-!
# Count-vector coefficients and independent Poisson fibres

The histogram probability of an iid finite label word combines with its
Poisson total count to give independent Poisson cell counts. The independent
stream law has the corresponding fixed-count product fibres.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

/-- Given [label masses](hyp:p) [summing to one](hyp:hp), [a Poisson mean](hyp:lambda),
and [a prescribed vector of label counts](hyp:c), [the Poisson mass of the total
count times the total probability of label words with that histogram equals the
product of the label-specific Poisson masses](goal). -/
theorem poisson_label_word_coefficient_eq
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (c : I → ℕ) :
    (poissonMeasure lambda) ({∑ i, c i} : Set ℕ) *
      (∑ w : Fin (∑ i, c i) → I,
        if ∀ i, wordHistogram w i = c i then
          ∏ k, (p (w k) : ℝ≥0∞) else 0) =
      ∏ i, (poissonMeasure (lambda * p i)) ({c i} : Set ℕ) := by
  classical
  let n := ∑ i, c i
  let H := histogramWords n c
  have hweight (w : Fin n → I) (hw : w ∈ H) :
      ∏ k, (p (w k) : ℝ≥0∞) = ∏ i, (p i : ℝ≥0∞) ^ c i := by
    rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin n)) w
      (fun k => (p (w k) : ℝ≥0∞))]
    apply Finset.prod_congr rfl
    intro i _
    have hi := (Finset.mem_filter.1 hw).2 i
    have hfactor : (∏ k ∈ (Finset.univ.filter fun k : Fin n => w k = i),
        (p (w k) : ℝ≥0∞)) =
        (p i : ℝ≥0∞) ^ wordHistogram w i := by
      rw [wordHistogram]
      calc
        (∏ k ∈ (Finset.univ.filter fun k : Fin n => w k = i),
            (p (w k) : ℝ≥0∞)) =
            ∏ _k ∈ (Finset.univ.filter fun k : Fin n => w k = i),
              (p i : ℝ≥0∞) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [(Finset.mem_filter.1 hk).2]
        _ = (p i : ℝ≥0∞) ^
            (Finset.univ.filter fun k : Fin n => w k = i).card := by
          rw [Finset.prod_const]
    rw [hfactor, hi]
  have hsum :
      (∑ w : Fin n → I,
        if ∀ i, wordHistogram w i = c i then
          ∏ k, (p (w k) : ℝ≥0∞) else 0) =
      (H.card : ℝ≥0∞) * ∏ i, (p i : ℝ≥0∞) ^ c i := by
    simp only [← Finset.sum_filter]
    change (∑ w ∈ H, ∏ k, (p (w k) : ℝ≥0∞)) =
      (H.card : ℝ≥0∞) * ∏ i, (p i : ℝ≥0∞) ^ c i
    rw [Finset.sum_congr rfl (fun w hw => hweight w hw)]
    simp
  rw [hsum]
  rw [← mul_assoc]
  have hcard : H.card = Nat.multinomial Finset.univ c :=
    histogramWords_card n c rfl
  simp_rw [poissonMeasure_singleton]
  rw [hcard]
  change (ENNReal.ofReal (poissonPMFReal lambda (∑ i, c i)) *
      (Nat.multinomial Finset.univ c : ℝ≥0∞)) *
      ∏ i : I, (p i : ℝ≥0∞) ^ c i =
    ∏ i : I, ENNReal.ofReal (poissonPMFReal (lambda * p i) (c i))
  have hreal :
      poissonPMFReal lambda (∑ i, c i) *
          (Nat.multinomial Finset.univ c : ℝ) *
          ∏ i : I, (p i : ℝ) ^ c i =
        ∏ i : I, poissonPMFReal (lambda * p i) (c i) := by
    unfold poissonPMFReal
    push_cast
    simp_rw [mul_pow]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum Finset.univ c (lambda : ℝ),
      ← Real.exp_sum]
    have hpR : ∑ i : I, (p i : ℝ) = 1 := by
      exact_mod_cast hp
    have hexp : ∑ i : I, -((lambda : ℝ) * (p i : ℝ)) = -(lambda : ℝ) := by
      rw [show (fun i : I => -((lambda : ℝ) * (p i : ℝ))) =
          fun i => -(lambda : ℝ) * (p i : ℝ) by
        funext i
        ring]
      rw [← Finset.mul_sum, hpR, mul_one]
    rw [hexp]
    have hmulti := Nat.multinomial_spec Finset.univ c
    have hmultiR := congrArg (fun m : ℕ => (m : ℝ)) hmulti
    push_cast at hmultiR
    field_simp
    rw [← hmultiR]
    ring
  have hof := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => poissonPMFReal_nonneg)] at hof
  have hp0 : 0 ≤ poissonPMFReal lambda (∑ i, c i) := poissonPMFReal_nonneg
  have hppow : ∀ i : I, 0 ≤ (p i : ℝ) ^ c i := fun i => by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hp0 (Nat.cast_nonneg _)),
    ENNReal.ofReal_mul hp0, ENNReal.ofReal_natCast,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hppow i)] at hof
  simp_rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _)] at hof
  simp only [ENNReal.ofReal_coe_nnreal] at hof
  exact hof

/-- Given [an iid observation law](hyp:P), [label masses](hyp:p),
[a Poisson mean](hyp:lambda), and [a prescribed label-count vector](hyp:c), [the
independent finite-Poisson stream law on that count-vector fibre is the product
of the count probabilities times independent fixed-length iid streams](goal). -/
theorem independentStreamLaw_restrict_countVector_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (lambda : ℝ≥0) (c : I → ℕ) :
    (Measure.pi (fun i : I => finitePoissonSampleLaw P (lambda * p i))).restrict
        {s | ∀ i, (s i).count = c i} =
      (∏ i, (poissonMeasure (lambda * p i)) ({c i} : Set ℕ)) •
        Measure.pi (fun i : I =>
          Measure.map (fixedSizeEmbed (c i))
            (Measure.pi (fun _ : Fin (c i) => P))) := by
  classical
  have hB : {s : I → FiniteSample X | ∀ i, (s i).count = c i} =
      Set.univ.pi (fun i : I => FiniteSample.count ⁻¹' ({c i} : Set ℕ)) := by
    ext s
    simp
  letI (i : I) : IsProbabilityMeasure
      (Measure.map (fixedSizeEmbed (c i))
        (Measure.pi fun _ : Fin (c i) => P)) :=
    Measure.isProbabilityMeasure_map
      (measurable_fixedSizeEmbed (c i)).aemeasurable
  letI (i : I) : IsFiniteMeasure
      (poissonMeasure (lambda * p i) ({c i} : Set ℕ) •
        Measure.map (fixedSizeEmbed (c i))
          (Measure.pi fun _ : Fin (c i) => P)) :=
    ⟨by
      rw [Measure.smul_apply, measure_univ]
      simpa using measure_lt_top
        (poissonMeasure (lambda * p i)) ({c i} : Set ℕ)⟩
  letI (i : I) : SigmaFinite
      (poissonMeasure (lambda * p i) ({c i} : Set ℕ) •
        Measure.map (fixedSizeEmbed (c i))
          (Measure.pi fun _ : Fin (c i) => P)) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [hB, Measure.restrict_pi_pi]
  simp_rw [finitePoissonSampleLaw_restrict_count_eq]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib.symm

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

