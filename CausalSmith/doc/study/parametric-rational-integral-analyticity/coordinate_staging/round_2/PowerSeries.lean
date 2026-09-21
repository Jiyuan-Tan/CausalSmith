import Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Definitions
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated integration of scalar power series

This file packages the measure-theoretic core: a locally uniformly dominated scalar power series
may be integrated coefficient by coefficient, and the resulting parameter function is analytic.
-/

open MeasureTheory

namespace Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity

/-- Given [a finite measure](hyp:μ), [an integrand family](hyp:f), [its coefficient functions](hyp:c), [coefficient envelopes](hyp:M), [an expansion center, radius, and evaluation parameter](hyp:t₀,r,t), [a positive radius and an evaluation inside it](hyp:hr,ht), [measurable coefficients](hyp:hc), [nonnegative envelopes](hyp:hM), [almost-everywhere coefficient domination](hyp:hbound), [a summable radius-weighted envelope](hyp:hsum), and [an almost-everywhere pointwise power-series expansion](hyp:hseries), [the integral equals the series of coefficient integrals at the evaluation parameter](goal). -/
theorem integral_eq_tsum_of_powerSeries_domination
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℝ → α → ℝ) (c : ℕ → α → ℝ) (M : ℕ → ℝ)
    (t₀ r t : ℝ) (hr : 0 < r) (ht : |t - t₀| < r)
    (hc : ∀ n, AEStronglyMeasurable (c n) μ)
    (hM : ∀ n, 0 ≤ M n)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖c n x‖ ≤ M n)
    (hsum : Summable (fun n ↦ M n * r ^ n))
    (hseries : ∀ s, |s - t₀| < r →
      ∀ᵐ x ∂μ, f s x = ∑' n : ℕ, c n x * (s - t₀) ^ n) :
    ∫ x, f t x ∂μ = ∑' n : ℕ, (∫ x, c n x ∂μ) * (t - t₀) ^ n := by
  let F : ℕ → α → ℝ := fun n x ↦ c n x * (t - t₀) ^ n
  have hc_int (n : ℕ) : Integrable (c n) μ :=
    Integrable.of_bound (hc n) (M n) (hbound n)
  have hF_int (n : ℕ) : Integrable (F n) μ := (hc_int n).mul_const _
  have hF_bound (n : ℕ) :
      ∫ x, ‖F n x‖ ∂μ ≤ μ.real Set.univ * (M n * r ^ n) := by
    calc
      ∫ x, ‖F n x‖ ∂μ ≤ ∫ _x, M n * r ^ n ∂μ := by
        apply integral_mono_ae (hF_int n).norm (integrable_const _)
        filter_upwards [hbound n] with x hx
        simp only [F, norm_mul, Real.norm_eq_abs, abs_pow]
        exact mul_le_mul hx (pow_le_pow_left₀ (abs_nonneg _) (le_of_lt ht) n)
          (pow_nonneg (abs_nonneg _) n) (hM n)
      _ = μ.real Set.univ * (M n * r ^ n) := by simp
  have hF_sum : Summable (fun n ↦ ∫ x, ‖F n x‖ ∂μ) := by
    apply Summable.of_nonneg_of_le
    · exact fun n ↦ integral_nonneg (fun x ↦ norm_nonneg (F n x))
    · exact hF_bound
    · exact hsum.mul_left (μ.real Set.univ)
  calc
    ∫ x, f t x ∂μ = ∫ x, ∑' n, F n x ∂μ :=
      integral_congr_ae (hseries t ht)
    _ = ∑' n, ∫ x, F n x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
    _ = ∑' n, (∫ x, c n x ∂μ) * (t - t₀) ^ n := by
      apply tsum_congr
      intro n
      exact integral_mul_const _ _

/-- Given [a finite measure](hyp:μ), [an integrand family](hyp:f), [its coefficient functions](hyp:c), [coefficient envelopes](hyp:M), [an expansion center and radius](hyp:t₀,r), [a positive radius](hyp:hr), [measurable coefficients](hyp:hc), [nonnegative envelopes](hyp:hM), [almost-everywhere coefficient domination](hyp:hbound), [a summable radius-weighted envelope](hyp:hsum), and [an almost-everywhere pointwise power-series expansion throughout that radius](hyp:hseries), [integrating the family produces a real-analytic function at the expansion center](goal). -/
theorem analyticAt_integral_of_powerSeries_domination
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℝ → α → ℝ) (c : ℕ → α → ℝ) (M : ℕ → ℝ)
    (t₀ r : ℝ) (hr : 0 < r)
    (hc : ∀ n, AEStronglyMeasurable (c n) μ)
    (hM : ∀ n, 0 ≤ M n)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖c n x‖ ≤ M n)
    (hsum : Summable (fun n ↦ M n * r ^ n))
    (hseries : ∀ t, |t - t₀| < r →
      ∀ᵐ x ∂μ, f t x = ∑' n : ℕ, c n x * (t - t₀) ^ n) :
    AnalyticAt ℝ (fun t ↦ ∫ x, f t x ∂μ) t₀ := by
  let a : ℕ → ℝ := fun n ↦ ∫ x, c n x ∂μ
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ a
  let ρ : NNReal := ⟨r, hr.le⟩
  have hc_int (n : ℕ) : Integrable (c n) μ :=
    Integrable.of_bound (hc n) (M n) (hbound n)
  have ha_bound (n : ℕ) : ‖a n‖ ≤ μ.real Set.univ * M n := by
    calc
      ‖a n‖ ≤ ∫ x, ‖c n x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _x, M n ∂μ := by
        exact integral_mono_ae (hc_int n).norm (integrable_const _) (hbound n)
      _ = μ.real Set.univ * M n := by simp
  have hp_bound (n : ℕ) :
      ‖p n‖ * (ρ : ℝ) ^ n ≤ μ.real Set.univ * (M n * r ^ n) := by
    calc
      ‖p n‖ * (ρ : ℝ) ^ n = ‖a n‖ * r ^ n := by
        rw [show p = FormalMultilinearSeries.ofScalars ℝ a from rfl,
          FormalMultilinearSeries.ofScalars_norm]
        rfl
      _ ≤ (μ.real Set.univ * M n) * r ^ n :=
        mul_le_mul_of_nonneg_right (ha_bound n) (pow_nonneg hr.le n)
      _ = μ.real Set.univ * (M n * r ^ n) := by ring
  have hp_sum : Summable (fun n ↦ ‖p n‖ * (ρ : ℝ) ^ n) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hr.le n)
    · exact hp_bound
    · exact hsum.mul_left (μ.real Set.univ)
  have hρ_le : (ρ : ENNReal) ≤ p.radius := p.le_radius_of_summable_norm hp_sum
  have hp : HasFPowerSeriesOnBall (fun t ↦ ∫ x, f t x ∂μ) p t₀ ρ := by
    refine { r_le := hρ_le, r_pos := ?_, hasSum := ?_ }
    · exact ENNReal.coe_pos.mpr (show 0 < ρ from hr)
    · intro y hy
      have hyt : |(t₀ + y) - t₀| < r := by
        have hyrho : |y| < (ρ : ℝ) := by
          simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hy
        rw [show (ρ : ℝ) = r from rfl] at hyrho
        simpa using hyrho
      have hy_radius : y ∈ Metric.eball (0 : ℝ) p.radius :=
        Metric.mem_eball.2 (lt_of_lt_of_le (Metric.mem_eball.1 hy) hρ_le)
      have hsum_y : Summable (fun n : ℕ ↦ p n fun _ ↦ y) := p.summable hy_radius
      rw [integral_eq_tsum_of_powerSeries_domination μ f c M t₀ r (t₀ + y) hr hyt
        hc hM hbound hsum hseries]
      simpa [p, a, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hsum_y.hasSum
  exact hp.analyticAt

end Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity
