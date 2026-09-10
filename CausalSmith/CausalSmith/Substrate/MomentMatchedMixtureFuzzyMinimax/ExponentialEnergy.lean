import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exponential energies of bounded priors

This module isolates the scalar analytic core of moment matching.  It expands the
exponential-kernel energy of two bounded probability priors into their moments and bounds the
quadratic energy left after matching finitely many moments.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax

/-- The exponential-series tail after matched degree `degree` at argument `z` is the sum of all
terms whose degree is strictly larger than `degree`. -/
noncomputable def exponentialSeriesTail (degree : ℕ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, if degree < n then z ^ n / (n.factorial : ℝ) else 0

/-- The `n`th raw moment of a real-valued prior is its integral of `θ ^ n`. -/
noncomputable def priorMoment (π : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ θ, θ ^ n ∂π

/-- The exponential energy of two real-valued priors averages `exp (lambda * θ * θ')` over
independent draws from the two priors. -/
noncomputable def exponentialPriorEnergy (π ρ : Measure ℝ) (lambda : ℝ) : ℝ :=
  ∫ θ, ∫ θ', Real.exp (lambda * θ * θ') ∂ρ ∂π

private theorem ae_abs_le_of_supported
    (π : Measure ℝ) [IsProbabilityMeasure π] (a : ℝ)
    (hsupp : π {θ | |θ| ≤ a} = 1) :
    ∀ᵐ θ ∂π, |θ| ≤ a := by
  have hset : MeasurableSet {θ : ℝ | |θ| ≤ a} :=
    measurableSet_le continuous_abs.measurable measurable_const
  change {θ : ℝ | |θ| ≤ a} ∈ ae π
  rw [mem_ae_iff, measure_compl hset (measure_ne_top π _), measure_univ, hsupp,
    tsub_self]


private theorem exponentialPriorEnergy_eq_tsum
    (π ρ : Measure ℝ) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hsuppπ : π {θ | |θ| ≤ a} = 1) (hsuppρ : ρ {θ | |θ| ≤ a} = 1) :
    exponentialPriorEnergy π ρ lambda =
      ∑' n : ℕ, lambda ^ n / (n.factorial : ℝ) * priorMoment π n * priorMoment ρ n := by
  have hinner (θ : ℝ) :
      HasSum (fun n : ℕ ↦ lambda ^ n / (n.factorial : ℝ) * θ ^ n * priorMoment ρ n)
        (∫ θ', Real.exp (lambda * θ * θ') ∂ρ) := by
    have h := MeasureTheory.hasSum_integral_of_dominated_convergence (μ := ρ)
      (fun n (_ : ℝ) ↦ (lambda * |θ| * a) ^ n / (n.factorial : ℝ))
      (F := fun n θ' ↦ lambda ^ n / (n.factorial : ℝ) * θ ^ n * θ' ^ n)
      (f := fun θ' ↦ Real.exp (lambda * θ * θ'))
      (fun n ↦ by fun_prop)
      (fun n ↦ by
        filter_upwards [ae_abs_le_of_supported ρ a hsuppρ] with θ' hθ'
        simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs,
          abs_of_nonneg hlambda]
        rw [abs_of_nonneg (show (0 : ℝ) ≤ n.factorial by positivity)]
        calc
          lambda ^ n / (n.factorial : ℝ) * |θ| ^ n * |θ'| ^ n =
              (lambda ^ n * |θ| ^ n * |θ'| ^ n) / (n.factorial : ℝ) := by ring
          _ ≤ (lambda ^ n * |θ| ^ n * a ^ n) / (n.factorial : ℝ) := by gcongr
          _ = (lambda * |θ| * a) ^ n / (n.factorial : ℝ) := by rw [mul_pow, mul_pow])
      (by
        filter_upwards with θ'
        exact Real.summable_pow_div_factorial (lambda * |θ| * a))
      (by
        convert integrable_const (μ := ρ) (Real.exp (lambda * |θ| * a)) using 1
        funext θ'
        rw [Real.exp_eq_exp_ℝ]
        exact (NormedSpace.expSeries_div_hasSum_exp (lambda * |θ| * a)).tsum_eq)
      (by
        filter_upwards with θ'
        rw [Real.exp_eq_exp_ℝ]
        exact (NormedSpace.expSeries_div_hasSum_exp (lambda * θ * θ')).congr_fun
          (fun n ↦ by ring))
    simpa only [priorMoment, integral_const_mul, mul_assoc] using h
  have houter := MeasureTheory.hasSum_integral_of_dominated_convergence (μ := π)
    (fun n (_ : ℝ) ↦ (lambda * a ^ 2) ^ n / (n.factorial : ℝ))
    (F := fun n θ ↦ lambda ^ n / (n.factorial : ℝ) * θ ^ n * priorMoment ρ n)
    (f := fun θ ↦ ∫ θ', Real.exp (lambda * θ * θ') ∂ρ)
    (fun n ↦ by fun_prop)
    (fun n ↦ by
      filter_upwards [ae_abs_le_of_supported π a hsuppπ] with θ hθ
      have hm : |priorMoment ρ n| ≤ a ^ n := by
        have hbound : ∀ᵐ x ∂ρ, ‖x ^ n‖ ≤ a ^ n := by
          filter_upwards [ae_abs_le_of_supported ρ a hsuppρ] with x hx
          rw [norm_pow, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg x) hx n
        simpa [priorMoment, Real.norm_eq_abs] using
          (norm_integral_le_of_norm_le_const hbound)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_nonneg hlambda, abs_of_nonneg (Nat.cast_nonneg n.factorial)]
      calc
        lambda ^ n / (n.factorial : ℝ) * |θ| ^ n * |priorMoment ρ n| =
            (lambda ^ n * |θ| ^ n * |priorMoment ρ n|) / (n.factorial : ℝ) := by ring
        _ ≤ (lambda ^ n * a ^ n * a ^ n) / (n.factorial : ℝ) := by gcongr
        _ = (lambda * a ^ 2) ^ n / (n.factorial : ℝ) := by ring)
    (by
      filter_upwards with θ
      exact Real.summable_pow_div_factorial (lambda * a ^ 2))
    (by
      convert integrable_const (μ := π) (Real.exp (lambda * a ^ 2)) using 1
      funext θ
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp (lambda * a ^ 2)).tsum_eq)
    (by
      filter_upwards with θ
      exact hinner θ)
  rw [exponentialPriorEnergy]
  convert houter.tsum_eq.symm using 1
  apply congrArg tsum
  funext n
  simp only [priorMoment, integral_mul_const, integral_const_mul]

/-- Every raw moment of a probability prior supported on `[-a,a]` has absolute value at most
`a ^ n`. -/
theorem abs_priorMoment_le_pow_of_supported
    (π : Measure ℝ) [IsProbabilityMeasure π] (a : ℝ) (n : ℕ) (ha : 0 ≤ a)
    (hsupp : π {θ | |θ| ≤ a} = 1) :
    |priorMoment π n| ≤ a ^ n := by
  have hset : MeasurableSet {θ : ℝ | |θ| ≤ a} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hmem : ∀ᵐ θ ∂π, |θ| ≤ a := by
    change {θ : ℝ | |θ| ≤ a} ∈ ae π
    rw [mem_ae_iff, measure_compl hset (measure_ne_top π _), measure_univ, hsupp,
      tsub_self]
  have hbound : ∀ᵐ θ ∂π, ‖θ ^ n‖ ≤ a ^ n := hmem.mono fun θ hθ ↦ by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg θ) hθ n
  simpa [priorMoment, Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const hbound)

private theorem summable_priorMoment_product
    (π ρ : Measure ℝ) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hsuppπ : π {θ | |θ| ≤ a} = 1) (hsuppρ : ρ {θ | |θ| ≤ a} = 1) :
    Summable fun n : ℕ ↦
      lambda ^ n / (n.factorial : ℝ) * priorMoment π n * priorMoment ρ n := by
  apply (Real.summable_pow_div_factorial (lambda * a ^ 2)).of_norm_bounded
  intro n
  have hπ := abs_priorMoment_le_pow_of_supported π a n ha hsuppπ
  have hρ := abs_priorMoment_le_pow_of_supported ρ a n ha hsuppρ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow,
    abs_of_nonneg hlambda, abs_of_nonneg (show (0 : ℝ) ≤ n.factorial by positivity)]
  calc
    lambda ^ n / (n.factorial : ℝ) * |priorMoment π n| * |priorMoment ρ n| =
        (lambda ^ n * |priorMoment π n| * |priorMoment ρ n|) /
          (n.factorial : ℝ) := by ring
    _ ≤ (lambda ^ n * a ^ n * a ^ n) / (n.factorial : ℝ) := by gcongr
    _ = (lambda * a ^ 2) ^ n / (n.factorial : ℝ) := by ring

/-- For two bounded probability priors, the alternating sum of their four exponential energies
is the convergent exponential series of their squared moment differences. -/
theorem exponentialPriorEnergy_quadratic_eq_tsum
    (π0 π1 : Measure ℝ) [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    (lambda a : ℝ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1) :
    exponentialPriorEnergy π0 π0 lambda - exponentialPriorEnergy π0 π1 lambda -
          exponentialPriorEnergy π1 π0 lambda + exponentialPriorEnergy π1 π1 lambda =
      ∑' n : ℕ, lambda ^ n / (n.factorial : ℝ) *
        (priorMoment π0 n - priorMoment π1 n) ^ 2 := by
  rw [exponentialPriorEnergy_eq_tsum π0 π0 lambda a hlambda ha hsupp0 hsupp0,
    exponentialPriorEnergy_eq_tsum π0 π1 lambda a hlambda ha hsupp0 hsupp1,
    exponentialPriorEnergy_eq_tsum π1 π0 lambda a hlambda ha hsupp1 hsupp0,
    exponentialPriorEnergy_eq_tsum π1 π1 lambda a hlambda ha hsupp1 hsupp1]
  have h00 := summable_priorMoment_product π0 π0 lambda a hlambda ha hsupp0 hsupp0
  have h01 := summable_priorMoment_product π0 π1 lambda a hlambda ha hsupp0 hsupp1
  have h10 := summable_priorMoment_product π1 π0 lambda a hlambda ha hsupp1 hsupp0
  have h11 := summable_priorMoment_product π1 π1 lambda a hlambda ha hsupp1 hsupp1
  have hsum := ((h00.hasSum.sub h01.hasSum).sub h10.hasSum).add h11.hasSum
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro n
  ring

/-- If two bounded probability priors match moments through `degree`, their alternating
exponential energy is at most four times the unmatched exponential-series tail. -/
theorem exponentialPriorEnergy_quadratic_le_tail
    (π0 π1 : Measure ℝ) [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    (lambda a : ℝ) (degree : ℕ) (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, priorMoment π0 n = priorMoment π1 n) :
    exponentialPriorEnergy π0 π0 lambda - exponentialPriorEnergy π0 π1 lambda -
          exponentialPriorEnergy π1 π0 lambda + exponentialPriorEnergy π1 π1 lambda ≤
      4 * exponentialSeriesTail degree (lambda * a ^ 2) := by
  rw [exponentialPriorEnergy_quadratic_eq_tsum π0 π1 lambda a hlambda ha hsupp0 hsupp1,
    exponentialSeriesTail]
  have h00 := summable_priorMoment_product π0 π0 lambda a hlambda ha hsupp0 hsupp0
  have h01 := summable_priorMoment_product π0 π1 lambda a hlambda ha hsupp0 hsupp1
  have h10 := summable_priorMoment_product π1 π0 lambda a hlambda ha hsupp1 hsupp0
  have h11 := summable_priorMoment_product π1 π1 lambda a hlambda ha hsupp1 hsupp1
  have hseries : Summable fun n : ℕ ↦
      lambda ^ n / (n.factorial : ℝ) *
        (priorMoment π0 n - priorMoment π1 n) ^ 2 := by
    apply (((h00.sub h01).sub h10).add h11).congr
    intro n
    ring
  have htail : Summable fun n : ℕ ↦
      if degree < n then (lambda * a ^ 2) ^ n / (n.factorial : ℝ) else 0 := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases hn : degree < n
        · simp only [if_pos hn]
          positivity
        · simp only [if_neg hn]
          positivity)
      (fun n ↦ by
        by_cases hn : degree < n
        · simp only [if_pos hn]
          exact le_rfl
        · simp only [if_neg hn]
          positivity)
      (Real.summable_pow_div_factorial (lambda * a ^ 2))
  have hbound (n : ℕ) :
      lambda ^ n / (n.factorial : ℝ) *
          (priorMoment π0 n - priorMoment π1 n) ^ 2 ≤
        4 * (if degree < n then (lambda * a ^ 2) ^ n / (n.factorial : ℝ) else 0) := by
    by_cases hn : degree < n
    · rw [if_pos hn]
      have h0 := abs_priorMoment_le_pow_of_supported π0 a n ha hsupp0
      have h1 := abs_priorMoment_le_pow_of_supported π1 a n ha hsupp1
      have hdiff : |priorMoment π0 n - priorMoment π1 n| ≤ 2 * a ^ n := by
        calc
          |priorMoment π0 n - priorMoment π1 n| ≤
              |priorMoment π0 n| + |priorMoment π1 n| := abs_sub _ _
          _ ≤ a ^ n + a ^ n := add_le_add h0 h1
          _ = 2 * a ^ n := by ring
      have hsq : (priorMoment π0 n - priorMoment π1 n) ^ 2 ≤ (2 * a ^ n) ^ 2 :=
        (sq_le_sq).2 (by
          rw [abs_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha n))]
          exact hdiff)
      calc
        lambda ^ n / (n.factorial : ℝ) *
            (priorMoment π0 n - priorMoment π1 n) ^ 2 ≤
          lambda ^ n / (n.factorial : ℝ) * (2 * a ^ n) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 4 * ((lambda * a ^ 2) ^ n / (n.factorial : ℝ)) := by ring
    · have hndeg : n ≤ degree := by omega
      simp [hn, hmom n hndeg]
  have hscaled := htail.mul_left 4
  have hle := hseries.tsum_le_tsum hbound hscaled
  simpa only [tsum_mul_left] using hle

end CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax
