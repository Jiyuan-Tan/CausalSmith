module
public import Causalean.Stat.Bootstrap.EfronResampling.FiniteRepresentation
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Basic
public import Causalean.Mathlib.Probability.IidMeanVariance
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

/-- For [a real vector](hyp:x), its [scalar finite average](goal) is the canonical finite mean
specialized to real-valued coordinates. -/
@[deprecated finMean (since := "2026-09-19")]
def finAverage (x : Fin n → ℝ) : ℝ :=
  finMean x

/-- For [real data](hyp:x) with [nonzero length](hyp:hn), [the bootstrap expectation of the
resample mean equals the original data mean](goal). -/
theorem integral_finMean_bootstrapResample (x : Fin n → ℝ) (hn : n ≠ 0) :
    ∫ y, finMean y ∂bootstrapResample x = finMean x := by
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
  rw [show finMean = fun y : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, id (y i) by
    funext y
    simp [finMean]]
  rw [Causalean.Mathlib.Probability.iid_average_integral
    (empiricalMeasure x) n (Nat.pos_of_ne_zero hn) id hId]
  unfold empiricalMeasure
  rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
    x (Nat.pos_of_ne_zero hn) measurable_id]
  simp [one_div]

/-- For [real data](hyp:x) with [nonzero length](hyp:hn), [the bootstrap second moment of the
square-root-scaled centered resample mean equals the empirical centered second moment](goal). -/
theorem integral_centered_finMean_sq_bootstrapResample (x : Fin n → ℝ) (hn : n ≠ 0) :
    ∫ y, (Real.sqrt n * (finMean y - finMean x)) ^ 2 ∂bootstrapResample x =
      (n : ℝ)⁻¹ * ∑ i, (x i - finMean x) ^ 2 := by
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
      ∫ y, finMean y ∂bootstrapResample x = finMean x :=
    integral_finMean_bootstrapResample x hn
  have hfin_meas : Measurable (finMean : (Fin n → ℝ) → ℝ) := by
    unfold finMean
    fun_prop
  have hpopmean :
      ∫ z, z ∂empiricalMeasure x = finMean x := by
    have h := Causalean.Stat.Concentration.integral_finiteSampleMeasure
      x (Nat.pos_of_ne_zero hn) measurable_id
    simpa only [empiricalMeasure, id_eq, one_div, finMean, smul_eq_mul] using h
  calc
    ∫ y, (Real.sqrt n * (finMean y - finMean x)) ^ 2 ∂bootstrapResample x =
        (n : ℝ) * ∫ y, (finMean y - finMean x) ^ 2 ∂bootstrapResample x := by
          rw [← integral_const_mul]
          congr 1
          funext y
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = (n : ℝ) * ProbabilityTheory.variance finMean (bootstrapResample x) := by
          congr 1
          rw [ProbabilityTheory.variance_eq_integral hfin_meas.aemeasurable]
          rw [hmean]
    _ = ProbabilityTheory.variance (fun z : ℝ => z) (empiricalMeasure x) := by
          rw [show finMean = fun sample : Fin n → ℝ =>
              (n : ℝ)⁻¹ * ∑ i, (fun z : ℝ => z) (sample i) by
                funext sample
                simp [finMean]]
          rw [show bootstrapResample x =
              Measure.pi (fun _ : Fin n => empiricalMeasure x) by rfl]
          rw [hvar]
          field_simp
    _ = ∫ z, (z - finMean x) ^ 2 ∂empiricalMeasure x := by
          rw [ProbabilityTheory.variance_eq_integral
            (X := fun z : ℝ => z) measurable_id.aemeasurable]
          rw [hpopmean]
    _ = (n : ℝ)⁻¹ * ∑ i, (x i - finMean x) ^ 2 := by
          have h := Causalean.Stat.Concentration.integral_finiteSampleMeasure
            (f := fun z : ℝ => (z - finMean x) ^ 2)
            x (Nat.pos_of_ne_zero hn) (by fun_prop)
          simpa only [empiricalMeasure, one_div] using h

/-- For [real data](hyp:x) with [nonzero length](hyp:hn), [the bootstrap expectation of the
legacy scalar average equals the original data average](goal). -/
@[deprecated integral_finMean_bootstrapResample (since := "2026-09-19")]
theorem integral_finAverage_bootstrapResample (x : Fin n → ℝ) (hn : n ≠ 0) :
    ∫ y, finAverage y ∂bootstrapResample x = finAverage x := by
  simpa [finAverage] using integral_finMean_bootstrapResample x hn

/-- For [real data](hyp:x) with [nonzero length](hyp:hn), [the bootstrap second moment of the
legacy centered scalar average equals the empirical centered second moment](goal). -/
@[deprecated integral_centered_finMean_sq_bootstrapResample (since := "2026-09-19")]
theorem integral_centered_finAverage_sq_bootstrapResample (x : Fin n → ℝ) (hn : n ≠ 0) :
    ∫ y, (Real.sqrt n * (finAverage y - finAverage x)) ^ 2 ∂bootstrapResample x =
      (n : ℝ)⁻¹ * ∑ i, (x i - finAverage x) ^ 2 := by
  simpa [finAverage] using integral_centered_finMean_sq_bootstrapResample x hn

end

end Causalean.Stat
