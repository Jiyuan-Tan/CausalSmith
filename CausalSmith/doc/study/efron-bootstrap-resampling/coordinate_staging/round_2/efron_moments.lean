module
public import Causalean.Mathlib.Probability.IidMeanVariance
public import Causalean.Stat.Bootstrap.EfronFiniteRepresentation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact bootstrap moments of the sample mean

This module computes the first moment of the bootstrap sample mean and the second moment of its
square-root-`n` centered version.  Both identities are exact finite-sample statements.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Given [a real vector of length `n`](hyp:x), its [finite average](goal) is `1/n` times the sum
of its coordinates, using Lean's reciprocal convention at `n = 0`. -/
def finAverage (x : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, x i

/-- For [nonempty real data](hyp:hn), [the bootstrap expectation of the resample mean equals the
original data mean](goal). -/
theorem integral_finAverage_bootstrapResample (x : Fin n → ℝ) (hn : n ≠ 0) :
    ∫ y, finAverage y ∂bootstrapResample x = finAverage x := by
  let _ : IsProbabilityMeasure (empiricalMeasure x) :=
    empiricalMeasure_isProbabilityMeasure x hn
  have hId : Integrable (fun z : ℝ => z) (empiricalMeasure x) := by
    unfold empiricalMeasure Causalean.Stat.Concentration.finiteSampleMeasure
    apply Integrable.smul_measure
    · rw [integrable_finsetSum_measure]
      intro i hi
      exact integrable_dirac' stronglyMeasurable_id (by simp)
    · simp [hn]
  rw [show bootstrapResample x = Measure.pi (fun _ : Fin n => empiricalMeasure x) by rfl]
  rw [show finAverage = fun y : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, id (y i) by
    funext y
    simp [finAverage]]
  rw [Causalean.Mathlib.Probability.iid_average_integral
    (empiricalMeasure x) n (Nat.pos_of_ne_zero hn) id hId]
  unfold empiricalMeasure
  rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
    x (Nat.pos_of_ne_zero hn) measurable_id]
  simp [one_div]

/-- For [nonempty real data](hyp:hn), [the bootstrap second moment of the square-root-`n`
centered resample mean equals the empirical centered second moment](goal). -/
theorem integral_centered_finAverage_sq_bootstrapResample (x : Fin n → ℝ) (hn : n ≠ 0) :
    ∫ y, (Real.sqrt n * (finAverage y - finAverage x)) ^ 2 ∂bootstrapResample x =
      (n : ℝ)⁻¹ * ∑ i, (x i - finAverage x) ^ 2 := by
  let _ : IsProbabilityMeasure (empiricalMeasure x) :=
    empiricalMeasure_isProbabilityMeasure x hn
  have hIdSq : Integrable (fun z : ℝ => z ^ 2) (empiricalMeasure x) := by
    unfold empiricalMeasure Causalean.Stat.Concentration.finiteSampleMeasure
    apply Integrable.smul_measure
    · rw [integrable_finsetSum_measure]
      intro i hi
      exact integrable_dirac' (stronglyMeasurable_id.pow 2) (by simp)
    · simp [hn]
  have hId : MemLp (fun z : ℝ => z) 2 (empiricalMeasure x) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hIdSq
  have hvar := Causalean.Mathlib.Probability.iid_average_variance
    (empiricalMeasure x) n (fun z : ℝ => z) hId
  have hmean :
      ∫ y, finAverage y ∂bootstrapResample x = finAverage x :=
    integral_finAverage_bootstrapResample x hn
  have hfin_meas : Measurable (finAverage : (Fin n → ℝ) → ℝ) := by
    unfold finAverage
    fun_prop
  have hpopmean :
      ∫ z, z ∂empiricalMeasure x = finAverage x := by
    have h := Causalean.Stat.Concentration.integral_finiteSampleMeasure
      x (Nat.pos_of_ne_zero hn) measurable_id
    simpa only [empiricalMeasure, id_eq, one_div, finAverage] using h
  calc
    ∫ y, (Real.sqrt n * (finAverage y - finAverage x)) ^ 2 ∂bootstrapResample x =
        (n : ℝ) * ∫ y, (finAverage y - finAverage x) ^ 2 ∂bootstrapResample x := by
          rw [← integral_const_mul]
          congr 1
          funext y
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = (n : ℝ) * ProbabilityTheory.variance finAverage (bootstrapResample x) := by
          congr 1
          rw [ProbabilityTheory.variance_eq_integral hfin_meas.aemeasurable]
          rw [hmean]
    _ = ProbabilityTheory.variance (fun z : ℝ => z) (empiricalMeasure x) := by
          rw [show finAverage = fun sample : Fin n → ℝ =>
              (n : ℝ)⁻¹ * ∑ i, (fun z : ℝ => z) (sample i) by
                funext sample
                simp [finAverage]]
          rw [show bootstrapResample x =
              Measure.pi (fun _ : Fin n => empiricalMeasure x) by rfl]
          rw [hvar]
          field_simp
    _ = ∫ z, (z - finAverage x) ^ 2 ∂empiricalMeasure x := by
          rw [ProbabilityTheory.variance_eq_integral
            (X := fun z : ℝ => z) measurable_id.aemeasurable]
          rw [hpopmean]
    _ = (n : ℝ)⁻¹ * ∑ i, (x i - finAverage x) ^ 2 := by
          have h := Causalean.Stat.Concentration.integral_finiteSampleMeasure
            (f := fun z : ℝ => (z - finAverage x) ^ 2)
            x (Nat.pos_of_ne_zero hn) (by fun_prop)
          simpa only [empiricalMeasure, one_div] using h

end

end Causalean.Stat
