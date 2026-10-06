module
public import Mathlib.Probability.CentralLimitTheorem

/-! # Scaling a scalar iid law to unit variance

These identities separate variance normalization from the quantitative
unit-variance normal approximation. They apply to any positive variance.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- Dividing a centered scalar law by its positive standard deviation gives
an integrable law of mean zero and variance one; its third absolute moment
is divided by the cube of that standard deviation. -/
theorem standardized_law_moments
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ2 M3 : ℝ) (hσ2 : 0 < σ2)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ2)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3) :
    let ν := μ.map (fun x : ℝ => x / Real.sqrt σ2)
    Integrable (fun x : ℝ => x) ν ∧
      (∫ x : ℝ, x ∂ν = 0) ∧
      Integrable (fun x : ℝ => x ^ 2) ν ∧
      (∫ x : ℝ, x ^ 2 ∂ν = 1) ∧
      Integrable (fun x : ℝ => |x| ^ 3) ν ∧
      (∫ x : ℝ, |x| ^ 3 ∂ν ≤ M3 / (Real.sqrt σ2) ^ 3) := by
  have hr : 0 < Real.sqrt σ2 := Real.sqrt_pos.2 hσ2
  have h2 : ∀ y : ℝ, (y / Real.sqrt σ2) ^ 2 = y ^ 2 / (Real.sqrt σ2) ^ 2 :=
    fun y => div_pow y (Real.sqrt σ2) 2
  have h3 : ∀ y : ℝ, |y / Real.sqrt σ2| ^ 3 = |y| ^ 3 / (Real.sqrt σ2) ^ 3 := by
    intro y
    rw [abs_div, abs_of_pos hr, div_pow]
  change Integrable (fun x : ℝ => x) (μ.map (fun y => y / Real.sqrt σ2)) ∧
    (∫ x : ℝ, x ∂μ.map (fun y => y / Real.sqrt σ2)) = 0 ∧
    Integrable (fun x : ℝ => x ^ 2) (μ.map (fun y => y / Real.sqrt σ2)) ∧
    (∫ x : ℝ, x ^ 2 ∂μ.map (fun y => y / Real.sqrt σ2)) = 1 ∧
    Integrable (fun x : ℝ => |x| ^ 3) (μ.map (fun y => y / Real.sqrt σ2)) ∧
    (∫ x : ℝ, |x| ^ 3 ∂μ.map (fun y => y / Real.sqrt σ2)) ≤
      M3 / (Real.sqrt σ2) ^ 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 (by
      simpa [Function.comp_def] using hmean_int.div_const (Real.sqrt σ2))
  · rw [integral_map (by fun_prop) (by fun_prop), integral_div, hmean, zero_div]
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 (by
      simpa only [Function.comp_def, h2] using hvar_int.div_const ((Real.sqrt σ2) ^ 2))
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [h2]
    rw [integral_div, hvar, Real.sq_sqrt (le_of_lt hσ2), div_self (ne_of_gt hσ2)]
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 (by
      simpa only [Function.comp_def, h3] using hthird_int.div_const ((Real.sqrt σ2) ^ 3))
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [h3]
    rw [integral_div]
    exact (div_le_div_iff_of_pos_right (pow_pos hr 3)).2 hthird

/-- For [a positive scale σ2](hyp:hσ2),
[the n-fold iid product of a law gives the event "sum divided by √n·√σ2 is at
most x" the same probability as the n-fold iid product of the law rescaled by
1/√σ2 gives the event "sum divided by √n is at most x"](goal): standardizing
each coordinate before summing is the same as standardizing the sum
afterward. -/
theorem standardized_iid_sum_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ2 : ℝ) (hσ2 : 0 < σ2)
    (n : ℕ) (x : ℝ) :
    (Measure.pi (fun _ : Fin n => μ))
        {v : Fin n → ℝ |
          (∑ i : Fin n, v i) / (Real.sqrt (n : ℝ) * Real.sqrt σ2) ≤ x} =
      (Measure.pi (fun _ : Fin n =>
        μ.map (fun y : ℝ => y / Real.sqrt σ2)))
        {v : Fin n → ℝ |
          (∑ i : Fin n, v i) / Real.sqrt (n : ℝ) ≤ x} := by
  have hr : 0 < Real.sqrt σ2 := Real.sqrt_pos.2 hσ2
  let f : ℝ → ℝ := fun y => y / Real.sqrt σ2
  have hf : Measurable f := by fun_prop
  have : ∀ _ : Fin n, SigmaFinite (μ.map f) := by
    intro i
    infer_instance
  have hmap : (Measure.pi (fun _ : Fin n => μ)).map (fun v i => f (v i)) =
      Measure.pi (fun _ : Fin n => μ.map f) :=
    Measure.pi_map_pi (fun _ => hf.aemeasurable)
  have hset : (fun v : Fin n → ℝ => fun i => f (v i)) ⁻¹'
      {v : Fin n → ℝ | (∑ i : Fin n, v i) / Real.sqrt (n : ℝ) ≤ x} =
      {v : Fin n → ℝ | (∑ i : Fin n, v i) /
        (Real.sqrt (n : ℝ) * Real.sqrt σ2) ≤ x} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, f, ← Finset.sum_div]
    -- This identity also covers n = 0, when √n = 0.
    rw [div_div, mul_comm (Real.sqrt σ2)]
  rw [← hmap, Measure.map_apply (by fun_prop)
    (measurableSet_le (by fun_prop) measurable_const), hset]

end Causalean.Stat.CLT.BerryEsseen
