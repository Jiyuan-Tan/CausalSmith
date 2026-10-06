module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenStandardize

/-! # Third absolute moments and the Berry–Esseen endpoint

The third absolute moment of a unit-second-moment probability law is at
least one. Scaling gives the corresponding lower bound at arbitrary positive
variance, which closes the one-observation case without a normal approximation.
This module imports no quantitative central limit or smoothing theorem.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- A real probability law with second moment one and integrable third
absolute moment has third absolute moment at least one. -/
theorem unit_second_moment_third_absolute_moment_ge_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsecond_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    1 ≤ ∫ x : ℝ, |x| ^ 3 ∂μ := by
  /- No general Holder infrastructure is needed here. For r=|x|≥0,
  (r-1)^2*(2*r+1)≥0 gives (3/2)*x^2-1/2≤|x|^3.
  Integrate this pointwise inequality using integral_mono, integral_sub,
  integral_const_mul, and the probability-law normalization. -/
  have hpoint (x : ℝ) : (3 / 2 : ℝ) * x ^ 2 - 1 / 2 ≤ |x| ^ 3 := by
    have hnonneg : 0 ≤ (|x| - 1) ^ 2 * (2 * |x| + 1) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have hsquare : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith
  have hscaled_int := hsecond_int.const_mul (3 / 2 : ℝ)
  have hconst_int : Integrable (fun _ : ℝ => (1 / 2 : ℝ)) μ := integrable_const _
  have hbound := integral_mono (hscaled_int.sub hconst_int) hthird_int hpoint
  change (∫ x : ℝ, (3 / 2 : ℝ) * x ^ 2 - 1 / 2 ∂μ) ≤
    ∫ x : ℝ, |x| ^ 3 ∂μ at hbound
  rw [integral_sub hscaled_int hconst_int, integral_const_mul, hsecond] at hbound
  norm_num at hbound
  exact hbound

/-- For [a centered](hyp:hmean_int,hmean) scalar probability law with
[positive variance σ2](hyp:hσ2,hvar_int,hvar) and
[integrable third absolute moment at most M3](hyp:hthird_int,hthird),
[M3 is at least the cube of the standard deviation √σ2](goal). -/
theorem variance_third_absolute_moment_lower_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ2 M3 : ℝ) (hσ2 : 0 < σ2)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ2)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3) :
    (Real.sqrt σ2) ^ 3 ≤ M3 := by
  haveI : IsProbabilityMeasure (μ.map (fun x : ℝ => x / Real.sqrt σ2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨_, _, hi2, h2, hi3, h3⟩ := standardized_law_moments μ σ2 M3 hσ2
    hmean_int hmean hvar_int hvar hthird_int hthird
  have h := (unit_second_moment_third_absolute_moment_ge_one
    (μ.map (fun x : ℝ => x / Real.sqrt σ2)) hi2 h2 hi3).trans h3
  simpa only [one_mul] using
    (le_div_iff₀ (pow_pos (Real.sqrt_pos.2 hσ2) 3)).1 h

end Causalean.Stat.CLT.BerryEsseen
