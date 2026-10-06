module
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Poisson count-vector series

Factorial-normalized product-Poisson coefficients form summable count-vector series.
-/

public section

namespace Causalean.Stat.Concentration.Poisson

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Stat

/-- For [a finite coordinate type](hyp:I) and [nonnegative coordinate
rates](hyp:rate), the product Poisson factorial likelihood sums to one over all
count vectors. The result is [the unit-mass identity for the product Poisson factorial likelihood](goal). -/
lemma poissonFactorial_countVector_tsum_one {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) :
    (∑' counts : I → ℕ, ∏ i : I,
      Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ counts i /
        (counts i).factorial) = 1 := by
  let μ : Measure (I → ℕ) := Measure.pi (fun i => poissonMeasure (rate i))
  letI : IsProbabilityMeasure μ := by
    unfold μ
    infer_instance
  rw [← probability_real_singleton_tsum μ]
  apply tsum_congr
  intro counts
  unfold μ
  rw [Measure.real_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [poissonMeasure_singleton, ENNReal.toReal_ofReal]
  positivity


/-- For [a finite coordinate type](hyp:I) and [nonnegative coordinate
rates](hyp:rate), the sum of the factorial-normalized monomials over all count
vectors equals the exponential of the total rate. The result is [the exponential identity for the factorial-normalized count-vector series](goal). -/
lemma factorial_countVector_tsum_eq_exp_sum {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) :
    (∑' counts : I → ℕ, ∏ i : I,
      (rate i : ℝ) ^ counts i / (counts i).factorial) =
        Real.exp (∑ i : I, (rate i : ℝ)) := by
  let S : ℝ := ∑ i : I, (rate i : ℝ)
  let raw : (I → ℕ) → ℝ := fun counts => ∏ i : I,
    (rate i : ℝ) ^ counts i / (counts i).factorial
  have hterm (counts : I → ℕ) :
      (∏ i : I, Real.exp (-(rate i : ℝ)) *
        (rate i : ℝ) ^ counts i / (counts i).factorial) =
        Real.exp (-S) * raw counts := by
    rw [show (∏ i : I, Real.exp (-(rate i : ℝ)) *
        (rate i : ℝ) ^ counts i / (counts i).factorial) =
      ∏ i : I, Real.exp (-(rate i : ℝ)) *
        ((rate i : ℝ) ^ counts i / (counts i).factorial) by
      apply Finset.prod_congr rfl
      intro i _
      ring,
      Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 1
    unfold S
    rw [← Finset.sum_neg_distrib]
  have hnorm := poissonFactorial_countVector_tsum_one rate
  rw [show (∑' counts : I → ℕ, ∏ i : I,
      Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ counts i /
        (counts i).factorial) =
      ∑' counts, Real.exp (-S) * raw counts by
        apply tsum_congr
        exact hterm,
    tsum_mul_left] at hnorm
  change (∑' counts, raw counts) = Real.exp S
  calc
    (∑' counts, raw counts) =
        Real.exp S * (Real.exp (-S) * ∑' counts, raw counts) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ = Real.exp S := by rw [hnorm, mul_one]


/-- For [a finite coordinate type](hyp:I) and [nonnegative coordinate
rates](hyp:rate), the product Poisson factorial likelihood is summable over all
count vectors, including zero-rate coordinates. The result is [summability of the product Poisson factorial likelihood](goal). -/
lemma summable_poissonFactorial_countVector {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) :
    Summable fun counts : I → ℕ => ∏ i : I,
      Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ counts i /
        (counts i).factorial := by
  let μ : Measure (I → ℕ) := Measure.pi (fun i => poissonMeasure (rate i))
  letI : IsProbabilityMeasure μ := by
    unfold μ
    infer_instance
  have hm : Summable fun counts : I → ℕ => μ.real {counts} := by
    apply ENNReal.summable_toReal
    have h := MeasureTheory.Measure.tsum_indicator_apply_singleton μ
      (Set.univ : Set (I → ℕ)) MeasurableSet.univ
    simpa using h.trans_ne (measure_ne_top μ Set.univ)
  apply hm.congr
  intro counts
  unfold μ
  rw [Measure.real_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [poissonMeasure_singleton, ENNReal.toReal_ofReal]
  positivity


/-- For [nonnegative coordinate rates](hyp:rate), a [nonnegative count-vector
envelope](hyp:f,hf) that is [pointwise dominated by the product Poisson
factorial likelihood](hyp:hdom) has total mass at most one. The result is [the unit upper bound on the dominated envelope’s total mass](goal). -/
lemma tsum_le_one_of_le_poissonFactorial {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) (f : (I → ℕ) → ℝ)
    (hf : ∀ counts, 0 ≤ f counts)
    (hdom : ∀ counts, f counts ≤ ∏ i : I,
      Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ counts i /
        (counts i).factorial) :
    (∑' counts, f counts) ≤ 1 := by
  have hg := summable_poissonFactorial_countVector rate
  have hfSummable : Summable f :=
    Summable.of_nonneg_of_le hf hdom hg
  calc
    (∑' counts, f counts) ≤ ∑' counts : I → ℕ, ∏ i : I,
        Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ counts i /
          (counts i).factorial :=
      Summable.tsum_le_tsum hdom hfSummable hg
    _ = 1 := poissonFactorial_countVector_tsum_one rate

end Causalean.Stat.Concentration.Poisson
