module
public import Causalean.Stat.Quantile.Transport
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Unequal finite-mass quantile transport

This module extends the compact-support probability quantile/CDF identity to
positive finite measures normalized to probability laws, with an explicit
interval-length penalty for unequal total masses.
-/

public section

open MeasureTheory ProbabilityTheory Set Causalean.Stat
open Causalean.Stat.Quantile.Transport

namespace Causalean.Stat.Quantile.FiniteMassTransport

/-- [Positive total masses](hyp:hp,hq) and [their nonnegative bounded cumulative
mass values](hyp:hx,hxp,hy,hyq) give [a normalized discrepancy times the smaller
mass bounded by the raw discrepancy plus the mass mismatch](goal). -/
lemma min_mul_abs_div_sub_div_le
    {p q x y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hx : 0 ≤ x) (hxp : x ≤ p) (hy : 0 ≤ y) (hyq : y ≤ q) :
    min p q * |x / p - y / q| ≤ |x - y| + |p - q| := by
  /- Split on `p ≤ q`. In that branch rewrite
     `p*(x/p-y/q) = (x-y)+(q-p)*(y/q)` and use `0 ≤ y/q ≤ 1`.
     The other branch is symmetric. -/
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hydiv : 0 ≤ y / q ∧ y / q ≤ 1 :=
    ⟨div_nonneg hy hq.le, (div_le_one hq).2 hyq⟩
  have hxdiv : 0 ≤ x / p ∧ x / p ≤ 1 :=
    ⟨div_nonneg hx hp.le, (div_le_one hp).2 hxp⟩
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq]
    have hid : p * (x / p - y / q) = (x - y) + (q - p) * (y / q) := by
      field_simp
      ring
    calc
      p * |x / p - y / q| = |p * (x / p - y / q)| := by rw [abs_mul, abs_of_pos hp]
      _ = |(x - y) + (q - p) * (y / q)| := by rw [hid]
      _ ≤ |x - y| + |(q - p) * (y / q)| := abs_add_le _ _
      _ ≤ |x - y| + |p - q| := by
        have h : |(q - p) * (y / q)| ≤ |p - q| := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hpq), abs_of_nonneg hydiv.1,
            abs_sub_comm]
          simpa [abs_of_nonneg (sub_nonneg.mpr hpq)] using
            mul_le_of_le_one_right (sub_nonneg.mpr hpq) hydiv.2
        linarith
  · rw [min_eq_right hqp]
    have hid : q * (x / p - y / q) = (x - y) - (p - q) * (x / p) := by
      field_simp
      ring
    calc
      q * |x / p - y / q| = |q * (x / p - y / q)| := by rw [abs_mul, abs_of_pos hq]
      _ = |(x - y) - (p - q) * (x / p)| := by rw [hid]
      _ ≤ |x - y| + |(p - q) * (x / p)| := by
        simpa [sub_eq_add_neg] using (abs_add_le (x - y) (-((p - q) * (x / p))))
      _ ≤ |x - y| + |p - q| := by
        have h : |(p - q) * (x / p)| ≤ |p - q| := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hqp), abs_of_nonneg hxdiv.1]
          simpa [abs_of_nonneg (sub_nonneg.mpr hqp)] using
            mul_le_of_le_one_right (sub_nonneg.mpr hqp) hxdiv.2
        linarith

/-- [An ordered interval](hyp:hab), [positive masses](hyp:hp,hq), [bounded
cumulative functions](hyp:hF,hG), and [integrability of both discrepancies](hyp:hnorm,hraw)
give [the integrated normalized discrepancy bound with a mass-mismatch penalty](goal). -/
lemma min_mul_integral_abs_div_sub_div_le
    {a b p q : ℝ} {F G : ℝ → ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hq : 0 < q)
    (hF : ∀ t ∈ Icc a b, 0 ≤ F t ∧ F t ≤ p)
    (hG : ∀ t ∈ Icc a b, 0 ≤ G t ∧ G t ≤ q)
    (hnorm : IntervalIntegrable (fun t => |F t / p - G t / q|) volume a b)
    (hraw : IntervalIntegrable (fun t => |F t - G t|) volume a b) :
    min p q * (∫ t in a..b, |F t / p - G t / q|) ≤
      (∫ t in a..b, |F t - G t|) + (b - a) * |p - q| := by
  /- Integrate the preceding pointwise bound with `integral_mono_on`;
     `intervalIntegral.integral_const` gives exactly `(b-a)*|p-q|`. -/
  have hconst : IntervalIntegrable (fun _ : ℝ => |p - q|) volume a b :=
    intervalIntegrable_const
  have hleft : IntervalIntegrable
      (fun t => min p q * |F t / p - G t / q|) volume a b :=
    hnorm.const_mul _
  have hright : IntervalIntegrable
      (fun t => |F t - G t| + |p - q|) volume a b :=
    hraw.add hconst
  have hmono := intervalIntegral.integral_mono_on hab hleft hright
    (fun t ht => min_mul_abs_div_sub_div_le hp hq (hF t ht).1 (hF t ht).2
      (hG t ht).1 (hG t ht).2)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hraw hconst,
    intervalIntegral.integral_const] at hmono
  simpa only [smul_eq_mul] using hmono

/-- A [finite measure](hyp:μ) with [positive total mass](hyp:hp) has [a
normalized CDF equal to raw cumulative mass divided by total mass](goal). -/
lemma cdf_normalize_eq_div (μ : FiniteMeasure ℝ)
    (hp : 0 < (μ.mass : ℝ)) (t : ℝ) :
    cdf (μ.normalize : Measure ℝ) t =
      ((μ : Measure ℝ) (Iic t)).toReal / (μ.mass : ℝ) := by
  /- Use `cdf_eq_real` and `FiniteMeasure.normalize_eq_of_nonzero`, then
     convert the finite-measure values from `ℝ≥0` to `ℝ`. -/
  have hne : μ ≠ 0 := by
    intro h
    simp [h] at hp
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real, μ.toMeasure_normalize_eq_of_nonzero hne, Measure.smul_apply]
  change (((μ.mass⁻¹ : NNReal) : ENNReal) * (μ : Measure ℝ) (Iic t)).toReal = _
  rw [ENNReal.toReal_mul]
  simp [inv_mul_eq_div]

/-- A [finite measure](hyp:μ) with [positive total mass](hyp:hp) [concentrated
on a closed interval](hyp:hμ) has [a normalized probability law concentrated
on the same interval](goal). -/
lemma normalize_support_Icc (μ : FiniteMeasure ℝ)
    {a b : ℝ} (hp : 0 < (μ.mass : ℝ))
    (hμ : (μ : Measure ℝ) (Icc a b)ᶜ = 0) :
    (μ.normalize : Measure ℝ) (Icc a b)ᶜ = 0 := by
  /- Apply `FiniteMeasure.normalize_eq_of_nonzero` to the complement. -/
  have hne : μ ≠ 0 := by
    intro h
    simp [h] at hp
  rw [μ.toMeasure_normalize_eq_of_nonzero hne, Measure.smul_apply]
  simp [hμ]

/-- [Two finite measures](hyp:μ,ν) have [an integrable raw cumulative-mass
difference on the given finite interval](goal). -/
lemma intervalIntegrable_abs_raw_cdf_sub (μ ν : FiniteMeasure ℝ)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => |((μ : Measure ℝ) (Iic t)).toReal -
        ((ν : Measure ℝ) (Iic t)).toReal|) volume a b := by
  /- Each raw cumulative mass is monotone and bounded by the finite total
     mass; monotone real functions are measurable and bounded on `Icc a b`. -/
  have hμ : Monotone (fun t : ℝ => ((μ : Measure ℝ) (Iic t)).toReal) := by
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hst))
  have hν : Monotone (fun t : ℝ => ((ν : Measure ℝ) (Iic t)).toReal) := by
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hst))
  exact (hμ.intervalIntegrable.sub hν.intervalIntegrable).abs

/-- [Two finite measures](hyp:μ,ν) with [an ordered common compact interval](hyp:hab),
[positive masses](hyp:hp,hq), and [concentration on that interval](hyp:hμ,hν)
have [smaller-mass-scaled normalized quantile cost bounded by raw CDF distance
plus interval length times their mass difference](goal). -/
theorem finite_mass_quantile_transport_le (μ ν : FiniteMeasure ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hp : 0 < (μ.mass : ℝ)) (hq : 0 < (ν.mass : ℝ))
    (hμ : (μ : Measure ℝ) (Icc a b)ᶜ = 0)
    (hν : (ν : Measure ℝ) (Icc a b)ᶜ = 0) :
    min (μ.mass : ℝ) (ν.mass : ℝ) *
      (∫ u in (0 : ℝ)..1,
        |quantile (μ.normalize : Measure ℝ) u -
          quantile (ν.normalize : Measure ℝ) u|) ≤
      (∫ t in a..b,
        |((μ : Measure ℝ) (Iic t)).toReal -
          ((ν : Measure ℝ) (Iic t)).toReal|) +
        (b - a) * |(μ.mass : ℝ) - (ν.mass : ℝ)| := by
  /- Apply `quantile_transport_eq_cdf_distance` to the two normalized
     probability measures. Their support follows from `hμ,hν` and
     `normalize_eq_of_nonzero`. Rewrite normalized CDFs with
     `cdf_normalize_eq_div`, then apply the integrated algebra bound.
     For each raw CDF, `measure_mono (Set.subset_univ _)` followed by
     `ENNReal.toReal_mono` gives the upper mass bound; the lower bound is
     `ENNReal.toReal_nonneg`. Use `intervalIntegrable_abs_cdf_sub` for the
     normalized difference and `intervalIntegrable_abs_raw_cdf_sub` for
     the raw difference. -/
  have hμ' := normalize_support_Icc μ hp hμ
  have hν' := normalize_support_Icc ν hq hν
  have htransport := quantile_transport_eq_cdf_distance
    (μ.normalize : Measure ℝ) (ν.normalize : Measure ℝ) hab hμ' hν'
  have hμbound (t : ℝ) :
      0 ≤ ((μ : Measure ℝ) (Iic t)).toReal ∧
        ((μ : Measure ℝ) (Iic t)).toReal ≤ (μ.mass : ℝ) := by
    exact ⟨ENNReal.toReal_nonneg,
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))⟩
  have hνbound (t : ℝ) :
      0 ≤ ((ν : Measure ℝ) (Iic t)).toReal ∧
        ((ν : Measure ℝ) (Iic t)).toReal ≤ (ν.mass : ℝ) := by
    exact ⟨ENNReal.toReal_nonneg,
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))⟩
  have hnorm := intervalIntegrable_abs_cdf_sub
    (μ.normalize : Measure ℝ) (ν.normalize : Measure ℝ) a b
  have hraw := intervalIntegrable_abs_raw_cdf_sub μ ν a b
  have hnorm' : IntervalIntegrable
      (fun t => |((μ : Measure ℝ) (Iic t)).toReal / (μ.mass : ℝ) -
        ((ν : Measure ℝ) (Iic t)).toReal / (ν.mass : ℝ)|) volume a b := by
    simpa only [cdf_normalize_eq_div μ hp, cdf_normalize_eq_div ν hq] using hnorm
  rw [htransport]
  have hrewrite :
      (∫ t in a..b,
        |cdf (μ.normalize : Measure ℝ) t - cdf (ν.normalize : Measure ℝ) t|) =
      ∫ t in a..b,
        |((μ : Measure ℝ) (Iic t)).toReal / (μ.mass : ℝ) -
          ((ν : Measure ℝ) (Iic t)).toReal / (ν.mass : ℝ)| := by
    apply intervalIntegral.integral_congr
    intro t _
    change |cdf (μ.normalize : Measure ℝ) t -
      cdf (ν.normalize : Measure ℝ) t| = _
    rw [cdf_normalize_eq_div μ hp, cdf_normalize_eq_div ν hq]
  rw [hrewrite]
  exact min_mul_integral_abs_div_sub_div_le hab hp hq
    (fun t _ => hμbound t) (fun t _ => hνbound t) hnorm' hraw

/-- [Two finite measures](hyp:μ,ν) with [an ordered common compact interval](hyp:hab),
[equal positive mass](hyp:hm,hp), and [concentration on that interval](hyp:hμ,hν)
have [a mass-scaled normalized quantile cost equal to their raw CDF distance](goal). -/
theorem finite_mass_quantile_transport_eq_of_mass_eq (μ ν : FiniteMeasure ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hm : μ.mass = ν.mass) (hp : 0 < (μ.mass : ℝ))
    (hμ : (μ : Measure ℝ) (Icc a b)ᶜ = 0)
    (hν : (ν : Measure ℝ) (Icc a b)ᶜ = 0) :
    (μ.mass : ℝ) *
      (∫ u in (0 : ℝ)..1,
        |quantile (μ.normalize : Measure ℝ) u -
          quantile (ν.normalize : Measure ℝ) u|) =
      ∫ t in a..b,
        |((μ : Measure ℝ) (Iic t)).toReal -
          ((ν : Measure ℝ) (Iic t)).toReal| := by
  /- Normalize support, apply `quantile_transport_eq_cdf_distance`,
     rewrite both CDFs with `cdf_normalize_eq_div`, then pull out the
     common positive mass through absolute value and interval integration.
     `hm` identifies the denominators. Pointwise, positive `p` gives
     `p * |x / p - y / p| = |x - y|`; use this inside
     `intervalIntegral.integral_congr` after `integral_const_mul`. -/
  have hq : 0 < (ν.mass : ℝ) := by simpa [hm] using hp
  have hμ' := normalize_support_Icc μ hp hμ
  have hν' := normalize_support_Icc ν hq hν
  have htransport := quantile_transport_eq_cdf_distance
    (μ.normalize : Measure ℝ) (ν.normalize : Measure ℝ) hab hμ' hν'
  rw [htransport]
  have hrewrite :
      (∫ t in a..b,
        |cdf (μ.normalize : Measure ℝ) t - cdf (ν.normalize : Measure ℝ) t|) =
      ∫ t in a..b,
        |((μ : Measure ℝ) (Iic t)).toReal / (μ.mass : ℝ) -
          ((ν : Measure ℝ) (Iic t)).toReal / (ν.mass : ℝ)| := by
    apply intervalIntegral.integral_congr
    intro t _
    change |cdf (μ.normalize : Measure ℝ) t -
      cdf (ν.normalize : Measure ℝ) t| = _
    rw [cdf_normalize_eq_div μ hp, cdf_normalize_eq_div ν hq]
  rw [hrewrite]
  rw [hm]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change (ν.mass : ℝ) *
    |((μ : Measure ℝ) (Iic t)).toReal / (ν.mass : ℝ) -
      ((ν : Measure ℝ) (Iic t)).toReal / (ν.mass : ℝ)| =
    |((μ : Measure ℝ) (Iic t)).toReal -
      ((ν : Measure ℝ) (Iic t)).toReal|
  rw [← sub_div, abs_div, abs_of_pos hq]
  exact mul_div_cancel₀ _ (ne_of_gt hq)

end Causalean.Stat.Quantile.FiniteMassTransport
