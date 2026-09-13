import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessQuantitative

/-!
# Exponential-tilt transport identities

This file records the distribution-function and first-moment calculations used
to transport the sparse witness's derivative bound along the exponential tilt.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: exponentialInterventionDensity_intervalIntegral
/-- The exponential intervention density has its stated closed-form distribution function.  [the stated conclusion](goal) follows. -/
lemma exponentialInterventionDensity_intervalIntegral (x : ℝ) :
    (∫ z in (0 : ℝ)..x, exponentialInterventionDensity z) =
      (Real.exp (4 * x) - 1) / (Real.exp 4 - 1) := by
  have hden : Real.exp 4 - 1 ≠ 0 := by
    linarith [thirteen_lt_exp_four]
  have hd (z : ℝ) : HasDerivAt
      (fun u : ℝ => (Real.exp (4 * u) - 1) / (Real.exp 4 - 1))
      (exponentialInterventionDensity z) z := by
    have he : HasDerivAt (fun u : ℝ => Real.exp (4 * u))
        (4 * Real.exp (4 * z)) z := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (4 * z)).comp z (hasDerivAt_const_mul (x := z) 4)
    simpa [exponentialInterventionDensity] using
      (he.sub_const 1).div_const (Real.exp 4 - 1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z)
    (by apply Continuous.intervalIntegrable; unfold exponentialInterventionDensity; fun_prop)]
  simp

-- @node: exponentialInterventionCDF_le_identity
/-- The exponential-tilt distribution function lies below the uniform distribution function.  Given [the stated inputs and conditions](hyp:hx), [the stated conclusion](goal) follows. -/
lemma exponentialInterventionCDF_le_identity {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z in (0 : ℝ)..x, exponentialInterventionDensity z) ≤ x := by
  rw [exponentialInterventionDensity_intervalIntegral]
  have hH := (cancellationPrimitive_mem_negUnitInterval hx).2
  unfold cancellationPrimitive at hH
  linarith

-- @node: exponentialInterventionDensity_firstMoment
/-- The exponential intervention density has the exact first moment used in the sparse gap.  [the stated conclusion](goal) follows. -/
lemma exponentialInterventionDensity_firstMoment :
    (∫ z in Set.Icc (0 : ℝ) 1, z * exponentialInterventionDensity z) =
      1 / (1 - Real.exp (-4)) - 1 / 4 := by
  have hden : Real.exp 4 - 1 ≠ 0 := by
    linarith [thirteen_lt_exp_four]
  let F : ℝ → ℝ := fun z => Real.exp (4 * z) * (z - 1 / 4) / (Real.exp 4 - 1)
  have hd (z : ℝ) : HasDerivAt F (z * exponentialInterventionDensity z) z := by
    have he : HasDerivAt (fun u : ℝ => Real.exp (4 * u))
        (4 * Real.exp (4 * z)) z := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (4 * z)).comp z (hasDerivAt_const_mul (x := z) 4)
    have hz : HasDerivAt (fun u : ℝ => u - 1 / 4) 1 z :=
      (hasDerivAt_id z).sub_const (1 / 4)
    have hraw : HasDerivAt F
        ((4 * Real.exp (4 * z) * (z - 1 / 4) + Real.exp (4 * z)) /
          (Real.exp 4 - 1)) z := by
      simpa only [F, Pi.mul_apply, mul_one] using
        (he.mul hz).div_const (Real.exp 4 - 1)
    apply hraw.congr_deriv
    unfold exponentialInterventionDensity
    field_simp
    ring
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z)
    (by apply Continuous.intervalIntegrable; unfold exponentialInterventionDensity; fun_prop)]
  dsimp only [F]
  simp only [mul_one, mul_zero, Real.exp_zero, zero_sub, one_mul]
  rw [Real.exp_neg]
  field_simp [hden, Real.exp_ne_zero]
  ring

-- @node: exponentialInterventionDensity_centeredMean
/-- The exponential-tilt mean excess over the uniform mean has its exact closed form.  [the stated conclusion](goal) follows. -/
lemma exponentialInterventionDensity_centeredMean :
    (∫ z in Set.Icc (0 : ℝ) 1, z * exponentialInterventionDensity z) - 1 / 2 =
      1 / (1 - Real.exp (-4)) - 3 / 4 := by
  rw [exponentialInterventionDensity_firstMoment]
  ring

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
