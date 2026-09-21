module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.Defs

/-!
# Linear finite-VC envelopes and critical radii

This file proves the deterministic arithmetic of the finite-VC linear
envelope: nonnegativity and positivity of its slope, star-shapedness, the
exact critical radius for a positive linear envelope, and the resulting
`d * log n / n` squared-radius bound.
-/

public section

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

universe u v

section ElementaryEnvelope

/-- The rate inside `vcLocalizedSlope` is nonnegative when `K ≥ 0`. -/
lemma vcLocalizedRate_nonneg {K : ℝ} {d n : ℕ} (hK : 0 ≤ K) :
    0 ≤ (K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hone_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith [le_of_lt hnR]
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hone_le
    have hterm : 0 ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by
      exact mul_nonneg (mul_nonneg hK (Nat.cast_nonneg d)) hlog
    have hnum : 0 ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1 := by
      linarith
    exact div_nonneg hnum (le_of_lt hnR)

/-- The finite-VC slope is nonnegative. -/
lemma vcLocalizedSlope_nonneg (K : ℝ) (d n : ℕ) :
    0 ≤ vcLocalizedSlope K d n := by
  unfold vcLocalizedSlope
  positivity

/-- If `K ≥ 0` and `n > 0`, the finite-VC slope is strictly positive. -/
lemma vcLocalizedSlope_pos {K : ℝ} {d n : ℕ} (hK : 0 ≤ K) (hn : 0 < n) :
    0 < vcLocalizedSlope K d n := by
  unfold vcLocalizedSlope
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hone_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [le_of_lt hnR]
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hone_le
  have hterm : 0 ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by
    exact mul_nonneg (mul_nonneg hK (Nat.cast_nonneg d)) hlog
  have hnum : 0 < K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1 := by
    linarith
  have hfrac :
      0 < (K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ) :=
    div_pos hnum hnR
  have hsqrt :
      0 < Real.sqrt
        ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) :=
    Real.sqrt_pos.mpr hfrac
  nlinarith

/-- The exact square of the finite-VC slope. -/
lemma vcLocalizedSlope_sq {K : ℝ} {d n : ℕ} (hK : 0 ≤ K) :
    vcLocalizedSlope K d n ^ 2 =
      36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
  unfold vcLocalizedSlope
  rw [mul_pow, Real.sq_sqrt (vcLocalizedRate_nonneg (K := K) (d := d) (n := n) hK)]
  ring

/-- If [a slope is nonnegative](hyp:hC), then [the corresponding linear function is a star-shaped envelope](goal). -/
lemma linear_isStarShapedEnvelope {C : ℝ} (hC : 0 ≤ C) :
    IsStarShapedEnvelope (fun r : ℝ => C * r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact mul_nonneg hC hr
  · intro r₁ r₂ _ hr₁₂
    exact mul_le_mul_of_nonneg_left hr₁₂ hC
  · intro r₁ r₂ hr₁ hr₁₂
    have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hr₁₂
    have h₁ : C * r₁ / r₁ = C := by field_simp [ne_of_gt hr₁]
    have h₂ : C * r₂ / r₂ = C := by field_simp [ne_of_gt hr₂]
    rw [h₁, h₂]

/-- [The finite-VC localized envelope is star-shaped](goal). -/
lemma vcLocalizedPsi_isStarShapedEnvelope (K : ℝ) (d n : ℕ) :
    IsStarShapedEnvelope (vcLocalizedPsi K d n) := by
  unfold vcLocalizedPsi
  exact linear_isStarShapedEnvelope (vcLocalizedSlope_nonneg K d n)

/-- The critical radius of a positive-slope linear envelope is at most its
slope. -/
lemma criticalRadius_linear_le {C : ℝ} (hC : 0 < C) :
    criticalRadius (fun r : ℝ => C * r) ≤ C := by
  apply criticalRadius_le hC
  rw [pow_two]

/-- The squared critical radius of a positive-slope linear envelope is at most
the squared slope. -/
lemma criticalRadius_linear_sq_le {C : ℝ} (hC : 0 < C) :
    (criticalRadius (fun r : ℝ => C * r)) ^ 2 ≤ C ^ 2 := by
  have hle : criticalRadius (fun r : ℝ => C * r) ≤ C :=
    criticalRadius_linear_le hC
  have hnonneg : 0 ≤ criticalRadius (fun r : ℝ => C * r) :=
    criticalRadius_nonneg _
  nlinarith

/-- The finite-VC critical radius is bounded by the finite-VC slope. -/
lemma criticalRadius_vcLocalizedPsi_le {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    criticalRadius (vcLocalizedPsi K d n) ≤ vcLocalizedSlope K d n := by
  unfold vcLocalizedPsi
  exact criticalRadius_linear_le (vcLocalizedSlope_pos hK hn)

/-- The finite-VC squared critical radius is bounded by the squared slope. -/
lemma criticalRadius_vcLocalizedPsi_sq_le {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    (criticalRadius (vcLocalizedPsi K d n)) ^ 2 ≤
      (vcLocalizedSlope K d n) ^ 2 := by
  unfold vcLocalizedPsi
  exact criticalRadius_linear_sq_le (vcLocalizedSlope_pos hK hn)

/-- **Rate bound for the finite-VC critical radius.** For [a nonnegative localization constant
K](hyp:hK) and [a positive sample size n](hyp:hn), [the squared critical radius of the finite-VC
localized envelope `vcLocalizedPsi K d n` is at most `36·(K·d·log(n+1)+1)/n` — the advertised
`(d·log n)/n`-order bound](goal). -/
lemma criticalRadius_vcLocalizedPsi_sq_le_rate {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    (criticalRadius (vcLocalizedPsi K d n)) ^ 2 ≤
      36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
  calc
    (criticalRadius (vcLocalizedPsi K d n)) ^ 2
        ≤ (vcLocalizedSlope K d n) ^ 2 :=
      criticalRadius_vcLocalizedPsi_sq_le hK hn
    _ = 36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) :=
      vcLocalizedSlope_sq hK

end ElementaryEnvelope


end Concentration
end Stat
end Causalean
