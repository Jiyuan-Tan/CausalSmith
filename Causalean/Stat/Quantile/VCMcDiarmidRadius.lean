module
public import Causalean.Stat.Quantile.VCMcDiarmid

/-!
# Confidence radii for the VC--McDiarmid empirical-CDF bound

This module calibrates both proved branches of the VC--McDiarmid bound. When its
threshold condition holds, the large-deviation branch supplies the smaller
square-root radius; otherwise the globally valid VC radius is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Causalean.Stat.Quantile.VCMcDiarmid

open Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF

/-- For [a confidence level](hyp:α) and [a sample size](hyp:m), [the globally valid
VC--McDiarmid radius](goal) is
`sqrt (32 * log (8 * (m+1) / α) / m)`. -/
noncomputable def vcMcDiarmidGlobalRadius (α : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (32 * Real.log (8 * ((m : ℝ) + 1) / α) / (m : ℝ))

/-- For [a confidence level](hyp:α) and [a sample size](hyp:m), [the radius calibrated
from the large-threshold VC--McDiarmid branch](goal) is
`sqrt (8 * log (1 / α) / m)`. -/
noncomputable def vcMcDiarmidLargeRadius (α : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (8 * Real.log (1 / α) / (m : ℝ))

/-- For [a confidence level](hyp:α) and [a sample size](hyp:m), [the VC--McDiarmid confidence
radius](goal) is the minimum of the globally valid radius and the large-threshold radius
when the latter satisfies its validity condition, and is the global radius otherwise.

Thus every consumer automatically uses the better of the two formally proved
VC--McDiarmid bounds. This is not the sharper DKW--Massart radius obtained from
`2 * exp (-2 * m * ε²)`, which is not formalized. -/
noncomputable def vcMcDiarmidRadius (α : ℝ) (m : ℕ) : ℝ :=
  if α < 1 ∧ 4 * Real.sqrt
      (2 * Real.log (2 * ((m : ℝ) + 1)) / (m : ℝ)) ≤ vcMcDiarmidLargeRadius α m then
    min (vcMcDiarmidLargeRadius α m) (vcMcDiarmidGlobalRadius α m)
  else
    vcMcDiarmidGlobalRadius α m

/-- For [a confidence level](hyp:α) and [a sample size](hyp:m), [the selected VC--McDiarmid
confidence radius is nonnegative](goal). -/
lemma vcMcDiarmidRadius_nonneg (α : ℝ) (m : ℕ) : 0 ≤ vcMcDiarmidRadius α m := by
  unfold vcMcDiarmidRadius vcMcDiarmidLargeRadius vcMcDiarmidGlobalRadius
  split
  · exact le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact Real.sqrt_nonneg _

private lemma vcMcDiarmidGlobalRadius_pos {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1)
    {m : ℕ} (hm : 0 < m) : 0 < vcMcDiarmidGlobalRadius α m := by
  have harg : 1 < 8 * ((m : ℝ) + 1) / α := by
    rw [lt_div_iff₀ hα]
    nlinarith
  unfold vcMcDiarmidGlobalRadius
  exact Real.sqrt_pos.2 (div_pos (mul_pos (by norm_num) (Real.log_pos harg))
    (Nat.cast_pos.mpr hm))

private lemma vcMcDiarmidLargeRadius_pos {α : ℝ} (hα : 0 < α) (hα_one : α < 1)
    {m : ℕ} (hm : 0 < m) : 0 < vcMcDiarmidLargeRadius α m := by
  have harg : 1 < 1 / α := by
    exact one_lt_one_div hα hα_one
  unfold vcMcDiarmidLargeRadius
  exact Real.sqrt_pos.2 (div_pos (mul_pos (by norm_num) (Real.log_pos harg))
    (Nat.cast_pos.mpr hm))

private theorem empiricalCDF_vc_mcdiarmid_global_radius (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] {m : ℕ} (hm : 0 < m) {α : ℝ}
    (hα : 0 < α) (hα_one : α ≤ 1) :
    (Measure.pi (fun _ : Fin m => ρ))
        (fixedCDFBadSet ρ (vcMcDiarmidGlobalRadius α m)) ≤ ENNReal.ofReal α := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have harg : 0 < 8 * ((m : ℝ) + 1) / α := by positivity
  have harg_one : 1 < 8 * ((m : ℝ) + 1) / α := by
    rw [lt_div_iff₀ hα]
    nlinarith
  have hrad_sq : vcMcDiarmidGlobalRadius α m ^ 2 =
      32 * Real.log (8 * ((m : ℝ) + 1) / α) / (m : ℝ) := by
    rw [vcMcDiarmidGlobalRadius, Real.sq_sqrt]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg harg_one.le)) hmR.le
  have hreal : 8 * ((m : ℝ) + 1) *
      Real.exp (-((m : ℝ) * vcMcDiarmidGlobalRadius α m ^ 2) / 32) = α := by
    rw [hrad_sq]
    have hexponent : -((m : ℝ) *
        (32 * Real.log (8 * ((m : ℝ) + 1) / α) / (m : ℝ))) / 32 =
        -Real.log (8 * ((m : ℝ) + 1) / α) := by
      field_simp [hmR.ne']
    rw [hexponent, Real.exp_neg, Real.exp_log harg]
    field_simp [show 8 * ((m : ℝ) + 1) ≠ 0 by positivity, hα.ne']
  have hmain := empiricalCDF_vc_mcdiarmid ρ hm
    (vcMcDiarmidGlobalRadius_pos hα hα_one hm)
  rwa [hreal] at hmain

private theorem empiricalCDF_vc_mcdiarmid_large_radius (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] {m : ℕ} (hm : 0 < m) {α : ℝ}
    (hα : 0 < α) (hα_one : α < 1)
    (hvalid : 4 * Real.sqrt
      (2 * Real.log (2 * ((m : ℝ) + 1)) / (m : ℝ)) ≤ vcMcDiarmidLargeRadius α m) :
    (Measure.pi (fun _ : Fin m => ρ))
        (fixedCDFBadSet ρ (vcMcDiarmidLargeRadius α m)) ≤ ENNReal.ofReal α := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have harg : 0 < 1 / α := by positivity
  have hrad_sq : vcMcDiarmidLargeRadius α m ^ 2 =
      8 * Real.log (1 / α) / (m : ℝ) := by
    rw [vcMcDiarmidLargeRadius, Real.sq_sqrt]
    have : 0 ≤ Real.log (1 / α) :=
      (Real.log_pos (one_lt_one_div hα hα_one)).le
    positivity
  have hreal : Real.exp (-((m : ℝ) * vcMcDiarmidLargeRadius α m ^ 2) / 8) = α := by
    rw [hrad_sq]
    have hexponent : -((m : ℝ) *
        (8 * Real.log (1 / α) / (m : ℝ))) / 8 = -Real.log (1 / α) := by
      field_simp [hmR.ne']
    rw [hexponent, Real.exp_neg, Real.exp_log harg]
    field_simp [hα.ne']
  have hmain := empiricalCDF_vc_mcdiarmid_large ρ hm
    (vcMcDiarmidLargeRadius_pos hα hα_one hm) hvalid
  rwa [hreal] at hmain

/-- Given [a population probability law](hyp:ρ), [a positive sample size](hyp:hm), and
[a confidence level between zero and one](hyp:hα,hα_one), [the probability
that the empirical CDF exceeds the automatically selected `vcMcDiarmidRadius α m` is at most
`α`](goal). This radius comes from the proved VC--McDiarmid bound, not the sharp
DKW--Massart inequality. -/
theorem empiricalCDF_vc_mcdiarmid_radius (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1) :
    (Measure.pi (fun _ : Fin m => ρ)) (fixedCDFBadSet ρ (vcMcDiarmidRadius α m)) ≤
      ENNReal.ofReal α := by
  by_cases hvalid : α < 1 ∧ 4 * Real.sqrt
      (2 * Real.log (2 * ((m : ℝ) + 1)) / (m : ℝ)) ≤ vcMcDiarmidLargeRadius α m
  · rw [vcMcDiarmidRadius, if_pos hvalid]
    by_cases hbetter : vcMcDiarmidLargeRadius α m ≤ vcMcDiarmidGlobalRadius α m
    · rw [min_eq_left hbetter]
      exact empiricalCDF_vc_mcdiarmid_large_radius ρ hm hα hvalid.1 hvalid.2
    · rw [min_eq_right (le_of_not_ge hbetter)]
      exact empiricalCDF_vc_mcdiarmid_global_radius ρ hm hα hα_one
  · rw [vcMcDiarmidRadius, if_neg hvalid]
    exact empiricalCDF_vc_mcdiarmid_global_radius ρ hm hα hα_one

end Causalean.Stat.Quantile.VCMcDiarmid
