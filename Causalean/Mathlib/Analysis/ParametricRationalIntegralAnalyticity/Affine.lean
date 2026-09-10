import Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Definitions
import Mathlib.Analysis.Analytic.Constructions

/-!
# Uniform control and geometric expansion of affine reciprocals

This file proves the elementary uniform-neighborhood and geometric-series facts used to control an
affine denominator. These results contain no measure theory.
-/

open Set

namespace Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity

/-- If [the separation margin is positive](hyp:hε), [the slope bound is nonnegative](hyp:hL), [the affine denominator is separated from zero at the reference parameter](hyp:hden), and [its slope is uniformly bounded on the integration set](hyp:hslope), then [it remains separated from zero by half that margin on an explicit parameter neighborhood](goal). -/
theorem affineDenominator_uniformly_nonzero_near
    {α : Type*} {K : Set α} {a b : α → ℝ} {t₀ ε L : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hden : ∀ x ∈ K, ε ≤ |affineDenominator a b t₀ x|)
    (hslope : ∀ x ∈ K, |b x - a x| ≤ L) :
    ∃ r > 0, ∀ t, |t - t₀| < r → ∀ x ∈ K,
      ε / 2 ≤ |affineDenominator a b t x| := by
  refine ⟨ε / (2 * (L + 1)), ?_, ?_⟩
  · positivity
  · intro t ht x hx
    have hL1 : 0 < L + 1 := by linarith
    have hpert :
        |(t - t₀) * (b x - a x)| < ε / 2 := by
      rw [abs_mul]
      calc
        |t - t₀| * |b x - a x| ≤ |t - t₀| * L :=
          mul_le_mul_of_nonneg_left (hslope x hx) (abs_nonneg _)
        _ ≤ |t - t₀| * (L + 1) := by
          gcongr
          linarith
        _ < (ε / (2 * (L + 1))) * (L + 1) :=
          mul_lt_mul_of_pos_right ht hL1
        _ = ε / 2 := by field_simp
    have haff :
        affineDenominator a b t x =
          affineDenominator a b t₀ x + (t - t₀) * (b x - a x) := by
      simp only [affineDenominator]
      ring
    have htri :
        |affineDenominator a b t₀ x| ≤
          |affineDenominator a b t x| + |(t - t₀) * (b x - a x)| := by
      calc
        |affineDenominator a b t₀ x| =
            |affineDenominator a b t x - (t - t₀) * (b x - a x)| := by
              congr 1
              rw [haff]
              ring
        _ ≤ _ := abs_sub _ _
    linarith [hden x hx]

/-- If [the parameter set is open](hyp:hO), [the separation margin is positive](hyp:hε), [the affine denominator is uniformly separated from zero throughout that set and the integration set](hyp:hden), and [the reference parameter lies in the open set](hyp:ht₀), then [some positive ball around it stays in the parameter set and retains the same uniform separation](goal). -/
theorem affineDenominator_uniformly_nonzero_on_open_near
    {α : Type*} {K : Set α} {a b : α → ℝ} {O : Set ℝ} {ε : ℝ}
    (hO : IsOpen O) (hε : 0 < ε)
    (hden : ∀ t ∈ O, ∀ x ∈ K, ε ≤ |affineDenominator a b t x|)
    {t₀ : ℝ} (ht₀ : t₀ ∈ O) :
    ∃ r > 0, Metric.ball t₀ r ⊆ O ∧
      ∀ t ∈ Metric.ball t₀ r, ∀ x ∈ K,
        ε ≤ |affineDenominator a b t x| := by
  rcases Metric.mem_nhds_iff.mp (hO.mem_nhds ht₀) with ⟨r, hr, hball⟩
  exact ⟨r, hr, hball, fun t ht x hx => hden t (hball ht) x hx⟩

/-- If [the parameter-ball radius and separation margin are positive](hyp:hr,hε) and [the affine denominator is uniformly separated from zero throughout that ball and the integration set](hyp:hden), then [the affine slope divided by its central denominator is bounded by the reciprocal radius](goal). -/
theorem affineDenominator_slope_div_le_inv_radius
    {α : Type*} {K : Set α} {a b : α → ℝ} {t₀ ε r : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hden : ∀ t, |t - t₀| < r → ∀ x ∈ K,
      ε ≤ |affineDenominator a b t x|) :
    ∀ x ∈ K,
      |(b x - a x) / affineDenominator a b t₀ x| ≤ r⁻¹ := by
  intro x hx
  let d₀ := affineDenominator a b t₀ x
  let s := b x - a x
  have hd₀_lower : ε ≤ |d₀| := by
    simpa [d₀] using hden t₀ (by simp [hr]) x hx
  have hd₀ : d₀ ≠ 0 := by
    intro hd₀_zero
    rw [hd₀_zero, abs_zero] at hd₀_lower
    linarith
  by_contra hle
  have hgt : r⁻¹ < |s / d₀| := by
    simpa [s, d₀] using lt_of_not_ge hle
  have hs : s ≠ 0 := by
    intro hs_zero
    simp [hs_zero] at hgt
    linarith
  have hd₀_abs_pos : 0 < |d₀| := abs_pos.mpr hd₀
  have hs_abs_pos : 0 < |s| := abs_pos.mpr hs
  have hcross : |d₀| < r * |s| := by
    rw [inv_eq_one_div, abs_div] at hgt
    have h := (div_lt_div_iff₀ hr hd₀_abs_pos).mp hgt
    nlinarith
  let t := t₀ - d₀ / s
  have ht : |t - t₀| < r := by
    dsimp [t]
    rw [sub_sub_cancel_left, abs_neg, abs_div]
    exact (div_lt_iff₀ hs_abs_pos).2 hcross
  have haff :
      affineDenominator a b t x = d₀ + (t - t₀) * s := by
    dsimp [d₀, s]
    simp only [affineDenominator]
    ring
  have hzero : affineDenominator a b t x = 0 := by
    rw [haff]
    dsimp [t]
    field_simp [hs]
    ring
  have hpositive := hden t ht x hx
  rw [hzero, abs_zero] at hpositive
  linarith

/-- If [the separation margin is positive](hyp:hε), [the relative-slope bound is nonnegative](hyp:hQ), [the central affine denominator is uniformly separated from zero](hyp:hden), and [the slope-to-denominator ratio is uniformly bounded](hyp:hratio), then [the denominator remains separated by half the margin on an explicit parameter neighborhood](goal). -/
theorem affineDenominator_uniformly_nonzero_near_of_slope_div_bound
    {α : Type*} {K : Set α} {a b : α → ℝ} {t₀ ε Q : ℝ}
    (hε : 0 < ε) (hQ : 0 ≤ Q)
    (hden : ∀ x ∈ K, ε ≤ |affineDenominator a b t₀ x|)
    (hratio : ∀ x ∈ K,
      |(b x - a x) / affineDenominator a b t₀ x| ≤ Q) :
    ∃ r > 0, ∀ t, |t - t₀| < r → ∀ x ∈ K,
      ε / 2 ≤ |affineDenominator a b t x| := by
  refine ⟨1 / (2 * (Q + 1)), by positivity, ?_⟩
  intro t ht x hx
  let d₀ := affineDenominator a b t₀ x
  let s := b x - a x
  have hd₀_lower : ε ≤ |d₀| := by
    simpa [d₀] using hden x hx
  have hd₀ : d₀ ≠ 0 := by
    intro hd₀_zero
    rw [hd₀_zero, abs_zero] at hd₀_lower
    linarith
  have hQ1 : 0 < Q + 1 := by linarith
  have hrel : |t - t₀| * |s / d₀| < 1 / 2 := by
    calc
      |t - t₀| * |s / d₀| ≤ |t - t₀| * Q :=
        mul_le_mul_of_nonneg_left
          (by simpa [s, d₀] using hratio x hx) (abs_nonneg _)
      _ ≤ |t - t₀| * (Q + 1) := by
        gcongr
        linarith
      _ < (1 / (2 * (Q + 1))) * (Q + 1) :=
        mul_lt_mul_of_pos_right ht hQ1
      _ = 1 / 2 := by field_simp
  have hs_factor : |s| = |s / d₀| * |d₀| := by
    calc
      |s| = |(s / d₀) * d₀| := by
        congr 1
        field_simp
      _ = |s / d₀| * |d₀| := abs_mul _ _
  have hpert : |(t - t₀) * s| < |d₀| / 2 := by
    calc
      |(t - t₀) * s| = (|t - t₀| * |s / d₀|) * |d₀| := by
        rw [abs_mul, hs_factor]
        ring
      _ < (1 / 2) * |d₀| :=
        mul_lt_mul_of_pos_right hrel (abs_pos.mpr hd₀)
      _ = |d₀| / 2 := by ring
  have haff :
      affineDenominator a b t x = d₀ + (t - t₀) * s := by
    dsimp [d₀, s]
    simp only [affineDenominator]
    ring
  have htri :
      |d₀| ≤ |affineDenominator a b t x| + |(t - t₀) * s| := by
    calc
      |d₀| = |affineDenominator a b t x - (t - t₀) * s| := by
        congr 1
        rw [haff]
        ring
      _ ≤ _ := abs_sub _ _
  linarith

/-- If [the affine denominator at the expansion center is nonzero](hyp:hden) and [the normalized affine perturbation has absolute value below one](hyp:hsmall), then [the reciprocal affine denominator equals its centered geometric power series](goal). -/
theorem affineDenominator_reciprocal_eq_tsum
    {α : Type*} {a b : α → ℝ} {t t₀ : ℝ} {x : α}
    (hden : affineDenominator a b t₀ x ≠ 0)
    (hsmall :
      |(t - t₀) * (b x - a x) / affineDenominator a b t₀ x| < 1) :
    (affineDenominator a b t x)⁻¹ =
      ∑' n : ℕ,
        ((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
          affineDenominator a b t₀ x) * (t - t₀) ^ n := by
  let d₀ := affineDenominator a b t₀ x
  let q := (-(b x - a x) / d₀) * (t - t₀)
  have hd₀ : d₀ ≠ 0 := hden
  have hq : |q| < 1 := by
    have hqeq : q = -((t - t₀) * (b x - a x) / d₀) := by
      dsimp [q]
      ring
    rw [hqeq, abs_neg]
    exact hsmall
  have hdiff :
      affineDenominator a b t x = d₀ + (t - t₀) * (b x - a x) := by
    dsimp [d₀]
    simp only [affineDenominator]
    ring
  have haff : affineDenominator a b t x = d₀ * (1 - q) := by
    rw [hdiff]
    dsimp [q]
    field_simp
    ring
  calc
    (affineDenominator a b t x)⁻¹ = (d₀ * (1 - q))⁻¹ := by rw [haff]
    _ = d₀⁻¹ * (1 - q)⁻¹ := by rw [mul_inv]
    _ = d₀⁻¹ * ∑' n : ℕ, q ^ n := by rw [tsum_geometric_of_abs_lt_one hq]
    _ = ∑' n : ℕ, d₀⁻¹ * q ^ n := by rw [tsum_mul_left]
    _ = ∑' n : ℕ,
        ((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
          affineDenominator a b t₀ x) * (t - t₀) ^ n := by
      apply tsum_congr
      intro n
      dsimp [d₀, q]
      rw [mul_pow]
      simp only [div_eq_mul_inv]
      ring

end Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity
