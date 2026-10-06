module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualSecondMoment

/-! Centered cell covariance and the squared-error decomposition in (25) and (28).
The probability measure parameter represents a normalized restriction to a correction cell. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- Centering both factors expresses a cell covariance as a centered-product integral. -/
-- @node: cell_covariance_centered_identity
lemma cell_covariance_centered_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (r : Ω → E) (hg : Integrable g μ) (hr : Integrable r μ)
    (hgr : Integrable (fun x => g x • r x) μ) :
    (∫ x, g x • r x ∂μ) - (∫ x, g x ∂μ) • (∫ x, r x ∂μ) =
      ∫ x, (g x - ∫ z, g z ∂μ) • (r x - ∫ z, r z ∂μ) ∂μ := by
  have hfun : (fun x => (g x - ∫ z, g z ∂μ) • (r x - ∫ z, r z ∂μ)) =
      fun x => g x • r x - g x • (∫ z, r z ∂μ) -
        (∫ z, g z ∂μ) • r x + (∫ z, g z ∂μ) • (∫ z, r z ∂μ) := by
    funext x
    simp only [sub_smul, smul_sub]
    abel
  rw [hfun]
  have h1 : Integrable (fun x => g x • (∫ z, r z ∂μ)) μ := hg.smul_const _
  have h2 : Integrable (fun x => (∫ z, g z ∂μ) • r x) μ := hr.smul _
  integral_linearity
  simp [integral_smul_const]

/-- A cell covariance is bounded by the product of its two centered envelopes. -/
-- @node: cell_covariance_norm_le
lemma cell_covariance_norm_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (r : Ω → E) (hg : Integrable g μ) (hr : Integrable r μ)
    (hgr : Integrable (fun x => g x • r x) μ) (A B : ℝ)
    (hA : 0 ≤ A)
    (ha : ∀ᵐ x ∂μ, |g x - ∫ z, g z ∂μ| ≤ A)
    (hb : ∀ᵐ x ∂μ, ‖r x - ∫ z, r z ∂μ‖ ≤ B) :
    ‖(∫ x, g x • r x ∂μ) - (∫ x, g x ∂μ) • (∫ x, r x ∂μ)‖ ≤ A * B := by
  rw [cell_covariance_centered_identity μ g r hg hr hgr]
  have hbound : ∀ᵐ x ∂μ,
      ‖(g x - ∫ z, g z ∂μ) • (r x - ∫ z, r z ∂μ)‖ ≤ A * B := by
    filter_upwards [ha, hb] with x hx hy
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hx hy (norm_nonneg _) hA
  simpa using norm_integral_le_of_norm_le_const hbound

/-- Averaging an oscillation bound gives the same bound on deviation from the cell mean. -/
-- @node: cell_mean_deviation_le
lemma cell_mean_deviation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → E) (hr : Integrable r μ) (x : Ω) (B : ℝ)
    (hb : ∀ᵐ z ∂μ, ‖r x - r z‖ ≤ B) :
    ‖r x - ∫ z, r z ∂μ‖ ≤ B := by
  have heq : r x - ∫ z, r z ∂μ = ∫ z, r x - r z ∂μ := by
    rw [integral_sub (integrable_const _) hr]
    simp
  rw [heq]
  simpa using norm_integral_le_of_norm_le_const hb

omit [CompleteSpace E] in
/-- Squared-error centering splits into a covariance and a scalar cell variance. -/
-- @node: cell_squared_error_decomposition
lemma cell_squared_error_decomposition (μ : Measure Ω) (u : Ω → ℝ) (v : Ω → E) :
    (∫ x, (u x) ^ 2 • v x ∂μ) - (∫ x, u x ∂μ) ^ 2 • (∫ x, v x ∂μ) =
      ((∫ x, (u x) ^ 2 • v x ∂μ) - (∫ x, (u x) ^ 2 ∂μ) • (∫ x, v x ∂μ)) +
      ((∫ x, (u x) ^ 2 ∂μ) - (∫ x, u x ∂μ) ^ 2) • (∫ x, v x ∂μ) := by
  rw [sub_smul]
  abel

/-- The cell variance is the centered squared integral. -/
-- @node: cell_variance_centered_identity
lemma cell_variance_centered_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu : Integrable u μ) (hu2 : Integrable (fun x => (u x) ^ 2) μ) :
    (∫ x, (u x) ^ 2 ∂μ) - (∫ x, u x ∂μ) ^ 2 =
      ∫ x, (u x - ∫ z, u z ∂μ) ^ 2 ∂μ := by
  simpa only [smul_eq_mul, ← sq] using
    cell_covariance_centered_identity μ u u hu hu (by simpa only [sq, smul_eq_mul] using hu2)

/-- Pairwise within-cell oscillations bound the covariance without a cell-count factor. -/
-- @node: cell_covariance_norm_le_of_oscillation
lemma cell_covariance_norm_le_of_oscillation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (r : Ω → E) (hg : Integrable g μ) (hr : Integrable r μ)
    (hgr : Integrable (fun x => g x • r x) μ) (A B : ℝ) (hA : 0 ≤ A)
    (ha : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, |g x - g z| ≤ A)
    (hb : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, ‖r x - r z‖ ≤ B) :
    ‖(∫ x, g x • r x ∂μ) - (∫ x, g x ∂μ) • (∫ x, r x ∂μ)‖ ≤ A * B := by
  apply cell_covariance_norm_le μ g r hg hr hgr A B hA
  · filter_upwards [ha] with x hx
    exact cell_mean_deviation_le μ g hg x A (by simpa only [Real.norm_eq_abs] using hx)
  · filter_upwards [hb] with x hx
    exact cell_mean_deviation_le μ r hr x B hx

/-- Squared oscillation bounds a cell variance, including singleton or constant cells. -/
-- @node: cell_variance_le_of_oscillation
lemma cell_variance_le_of_oscillation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu : Integrable u μ) (hu2 : Integrable (fun x => (u x) ^ 2) μ)
    (A : ℝ) (hA : 0 ≤ A) (ha : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, |u x - u z| ≤ A) :
    (∫ x, (u x) ^ 2 ∂μ) - (∫ x, u x ∂μ) ^ 2 ∈ Set.Icc 0 (A ^ 2) := by
  rw [cell_variance_centered_identity μ u hu hu2]
  constructor
  · apply integral_nonneg
    intro x
    exact sq_nonneg _
  · have hbound : ∀ᵐ x ∂μ, ‖(u x - ∫ z, u z ∂μ) ^ 2‖ ≤ A ^ 2 := by
      filter_upwards [ha] with x hx
      have hd := cell_mean_deviation_le μ u hu x A
        (by simpa only [Real.norm_eq_abs] using hx)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hs := (sq_le_sq₀ (abs_nonneg (u x - ∫ z, u z ∂μ)) hA).2
        (by simpa only [Real.norm_eq_abs] using hd)
      simpa only [sq_abs] using hs
    exact (le_abs_self _).trans (by
      simpa using
        norm_integral_le_of_norm_le_const hbound)

/-- The third remainder is bounded by squared-error covariance plus variance times mean size. -/
-- @node: cell_squared_error_norm_le
lemma cell_squared_error_norm_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (v : Ω → E) (hu : Integrable u μ)
    (hu2 : Integrable (fun x => (u x) ^ 2) μ) (hv : Integrable v μ)
    (hu2v : Integrable (fun x => (u x) ^ 2 • v x) μ)
    (A D B C : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, |u x - u z| ≤ A)
    (hd : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, |(u x) ^ 2 - (u z) ^ 2| ≤ D)
    (hb : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, ‖v x - v z‖ ≤ B)
    (hc : ‖∫ x, v x ∂μ‖ ≤ C) :
    ‖(∫ x, (u x) ^ 2 • v x ∂μ) - (∫ x, u x ∂μ) ^ 2 • (∫ x, v x ∂μ)‖ ≤
      D * B + A ^ 2 * C := by
  rw [cell_squared_error_decomposition μ u v]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact cell_covariance_norm_le_of_oscillation μ (fun x => (u x) ^ 2) v
      hu2 hv hu2v D B hD hd hb
  · have hvar := cell_variance_le_of_oscillation μ u hu hu2 A hA ha
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hvar.1]
    exact mul_le_mul hvar.2 hc (norm_nonneg _) (sq_nonneg _)

end CausalSmith.Stat.DensityEffectRoughNull
