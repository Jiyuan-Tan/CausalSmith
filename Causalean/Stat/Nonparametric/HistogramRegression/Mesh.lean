module
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ceiling meshes and optimized regression bandwidth algebra

Use `max 1 (ceil (1/b))` bins along each axis. For `0<b≤1` its reciprocal
lies between `b/2` and `b`, and its d-dimensional cell count is at most
`(2/b)^d`. The optimized positive-sample bandwidth is `m^(-1/(2β+d))`.
All the real-power and ceiling comparisons needed by the statistical theorem
are isolated here and make no probabilistic assumptions.
-/

@[expose] public section

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

/-- The [number of bins per coordinate](goal) for [bandwidth](hyp:b) is the
ceiling of its reciprocal, with at least one bin for every real input. -/
def meshCount (b : ℝ) : ℕ := max 1 ⌈b⁻¹⌉₊

/-- The [ceiling mesh count is positive](goal) for [every bandwidth](hyp:b). -/
theorem meshCount_pos (b : ℝ) : 0 < meshCount b := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- [A bandwidth in `(0,1]`](hyp:hb,hb1) gives [the reciprocal mesh-width
comparison and ceiling cell-count bound](goal). -/
theorem mesh_bounds (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    b / 2 ≤ (meshCount b : ℝ)⁻¹ ∧ (meshCount b : ℝ)⁻¹ ≤ b ∧
      (meshCount b : ℝ) ≤ 2 / b := by
  have hi : 0 < b⁻¹ := inv_pos.mpr hb
  have hcount : meshCount b = ⌈b⁻¹⌉₊ :=
    max_eq_right (Nat.one_le_ceil_iff.mpr hi)
  have hpos : 0 < (meshCount b : ℝ) := by exact_mod_cast meshCount_pos b
  have hlo : b⁻¹ ≤ (meshCount b : ℝ) := by
    rw [hcount]
    exact Nat.le_ceil _
  have hup : (meshCount b : ℝ) ≤ 2 / b := by
    have hceil := (Nat.ceil_lt_add_one hi.le).le
    have hone : 1 ≤ b⁻¹ := (one_le_inv₀ hb).mpr hb1
    rw [hcount, div_eq_mul_inv]
    linarith
  refine ⟨?_, ?_, hup⟩
  · have h := (inv_le_inv₀ (by positivity : 0 < 2 / b) hpos).mpr hup
    simpa using h
  · have h := (inv_le_inv₀ hpos hi).mpr hlo
    simpa using h

/-- [A bandwidth in `(0,1]`](hyp:hb,hb1) gives [the dimension-dependent
ceiling cell-count bound](goal). -/
theorem mesh_count_pow_le (d : ℕ) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    (meshCount b : ℝ) ^ d ≤ (2 : ℝ) ^ d / b ^ d := by
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ (meshCount b : ℝ))
    (mesh_bounds b hb hb1).2.2 d
  simpa only [div_pow] using h

/-- The [optimized bandwidth](goal) for [dimension, smoothness exponent,
and sample size](hyp:d,β,m) is the sample size raised to `-1/(2β+d)`. -/
def optimizedBandwidth (d : ℕ) (β : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (-(1 / (2 * β + d)))

/-- [Positive smoothness and at least one observation](hyp:hβ,hm) imply
[the optimized bandwidth is in `(0,1]`](goal). -/
theorem optimizedBandwidth_mem (d : ℕ) (β : ℝ) (m : ℕ)
    (hβ : 0 < β) (hm : 1 ≤ m) :
    0 < optimizedBandwidth d β m ∧ optimizedBandwidth d β m ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hden : 0 < 2 * β + (d : ℝ) := by positivity
  unfold optimizedBandwidth
  exact ⟨Real.rpow_pos_of_pos hmpos _,
    Real.rpow_le_one_of_one_le_of_nonpos hm1
      (neg_nonpos.mpr (one_div_pos.mpr hden).le)⟩

/-- [Positive smoothness and sample size](hyp:hβ,hm) give [the exact balanced
bias and reciprocal effective-sample-size powers at the optimized bandwidth](goal). -/
theorem optimized_power_identities (d : ℕ) (β : ℝ) (m : ℕ)
    (hβ : 0 < β) (hm : 1 ≤ m) :
    (optimizedBandwidth d β m) ^ (2 * β) =
        (m : ℝ) ^ (-(2 * β / (2 * β + d))) ∧
      1 / ((m : ℝ) * (optimizedBandwidth d β m) ^ d) =
        (m : ℝ) ^ (-(2 * β / (2 * β + d))) := by
  -- Prove using rpow_mul, rpow_natCast, rpow_add, and positivity of m
  -- and 2β+d. The second exponent is -1+d/(2β+d)=-2β/(2β+d).
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hden : 2 * β + (d : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold optimizedBandwidth
  constructor
  · rw [← Real.rpow_mul hmpos.le]
    congr 1
    ring
  · have hprod : (m : ℝ) * (m : ℝ) ^ (-(1 / (2 * β + d)) * d) =
        (m : ℝ) ^ (1 + -(1 / (2 * β + d)) * d) := by
      rw [Real.rpow_add hmpos, Real.rpow_one]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le,
      hprod, one_div, ← Real.rpow_neg hmpos.le]
    congr 1
    field_simp [hden]
    ring

/-- [Positive smoothness and sample size](hyp:hβ,hm) give [the optimized
ceiling cell-count variance term at the exact minimax exponent](goal). -/
theorem optimized_mesh_variance_le (d : ℕ) (β : ℝ) (m : ℕ)
    (hβ : 0 < β) (hm : 1 ≤ m) :
    (meshCount (optimizedBandwidth d β m) : ℝ) ^ d / (m + 1 : ℝ) ≤
      (2 : ℝ) ^ d * (m : ℝ) ^ (-(2 * β / (2 * β + d))) := by
  obtain ⟨hb, hb1⟩ := optimizedBandwidth_mem d β m hβ hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hcount := mesh_count_pow_le d (optimizedBandwidth d β m) hb hb1
  calc
    (meshCount (optimizedBandwidth d β m) : ℝ) ^ d / (m + 1 : ℝ) ≤
        ((2 : ℝ) ^ d / (optimizedBandwidth d β m) ^ d) / (m + 1 : ℝ) :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ ≤ ((2 : ℝ) ^ d / (optimizedBandwidth d β m) ^ d) / (m : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hmpos (by linarith)
    _ = (2 : ℝ) ^ d * (1 / ((m : ℝ) * (optimizedBandwidth d β m) ^ d)) := by
      ring
    _ = _ := by rw [(optimized_power_identities d β m hβ hm).2]

end

end Causalean.Stat.Nonparametric.HistogramRegression
