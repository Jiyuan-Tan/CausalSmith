module
public import Mathlib.Tactic

/-!
# A sharp two-point rational chord inequality

This module proves a sharp chord bound for a scalar rational function on a
symmetric interval. It is a reusable real-analysis inequality; the privacy
application lives in the statistical layer.
-/

public section

namespace Causalean.Mathlib.Analysis.Convex

/-- A [nonnegative interval radius below one](hyp:hk0,hk1), [a parameter of
absolute value below one](hyp:ht), and [a point in the symmetric interval](hyp:hd)
make [the quadratic-over-affine value no larger than its endpoint chord](goal), for
[the radius](hyp:k), [the parameter](hyp:t), and [the point](hyp:d). -/
theorem contrast_chord (k t d : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (ht : |t| < 1) (hd : |d| ≤ k) :
    d ^ 2 / (1 + t * d) ≤
      k ^ 2 / (1 - k ^ 2 * t ^ 2) * (1 - t * d) := by
  have hdk : |d| < 1 := lt_of_le_of_lt hd hk1
  have htd : |t * d| < 1 := by
    rw [abs_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt ht)) (abs_nonneg d)]
  have hkt : |k * t| < 1 := by
    rw [abs_mul, abs_of_nonneg hk0]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt ht)) hk0]
  have hden₁ : 0 < 1 + t * d := by
    have := (abs_lt.mp htd).1
    linarith
  have hden₂ : 0 < 1 - k ^ 2 * t ^ 2 := by
    have h₁ : 0 < 1 - k * t := by have := (abs_lt.mp hkt).2; linarith
    have h₂ : 0 < 1 + k * t := by have := (abs_lt.mp hkt).1; linarith
    nlinarith [mul_pos h₁ h₂]
  have hsq : d ^ 2 ≤ k ^ 2 := by
    have := (abs_le.mp hd)
    nlinarith
  have hpoly : d ^ 2 * (1 - k ^ 2 * t ^ 2) ≤
      k ^ 2 * (1 - t * d) * (1 + t * d) := by
    nlinarith [hsq]
  apply (div_le_iff₀ hden₁).2
  calc
    d ^ 2 ≤ (k ^ 2 * (1 - t * d) * (1 + t * d)) /
        (1 - k ^ 2 * t ^ 2) := (le_div_iff₀ hden₂).2 hpoly
    _ = _ := by ring

end Causalean.Mathlib.Analysis.Convex
