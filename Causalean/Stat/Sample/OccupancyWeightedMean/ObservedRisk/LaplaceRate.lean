module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.OccupancyBridge

/-!
# Scalar consequences of a usable-occupancy Laplace bound

These inequalities convert a birthday-scale exponential bound into the
`1/n + d/n²` rate and control the guarded reciprocal at zero. They do not
depend on an observed law or on a choice of cell alphabet.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

/-- A birthday-scale exponential bound is at most a constant times
`1/n + d/n²`, uniformly over positive sample sizes and all finite
dimensions, including dimension zero.

Proof route: `Real.add_one_le_exp` gives `exp (-x) ≤ x⁻¹` for `x > 0`.
Use `max n d ≤ n + d`, divide by `n²`, and absorb the fixed constants. -/
theorem birthday_laplace_rate (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n d : ℕ), 0 < n →
      2 * Real.exp (-(c * (n : ℝ) ^ 2 /
        max (n : ℝ) (d : ℝ))) ≤
      B * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) := by
  refine ⟨2 / c, by positivity, ?_⟩
  intro n d hn
  let N : ℝ := n
  let D : ℝ := d
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hD : 0 ≤ D := Nat.cast_nonneg d
  have hM : 0 < max N D := lt_of_lt_of_le hN (le_max_left _ _)
  have hC : 0 < c * N ^ 2 := mul_pos hc (sq_pos_of_pos hN)
  have hq : 0 < c * N ^ 2 / max N D := div_pos hC hM
  have hexp := Real.add_one_le_exp (c * N ^ 2 / max N D)
  have hprod : (c * N ^ 2 / max N D) *
      Real.exp (-(c * N ^ 2 / max N D)) ≤ 1 := by
    have he := mul_le_mul_of_nonneg_right hexp
      (le_of_lt (Real.exp_pos (-(c * N ^ 2 / max N D))))
    rw [add_mul, ← Real.exp_add] at he
    simp only [add_neg_cancel, Real.exp_zero, one_mul] at he
    nlinarith [Real.exp_pos (-(c * N ^ 2 / max N D))]
  have hbound : Real.exp (-(c * N ^ 2 / max N D)) ≤
      max N D / (c * N ^ 2) := by
    apply (le_div_iff₀ hC).2
    have hh := (div_le_iff₀ hM).1 (show
      c * N ^ 2 * Real.exp (-(c * N ^ 2 / max N D)) / max N D ≤ 1 by
        simpa [div_mul_eq_mul_div] using hprod)
    nlinarith
  have hmax : max N D ≤ N + D := max_le (by linarith) (by linarith)
  change 2 * Real.exp (-(c * N ^ 2 / max N D)) ≤
    (2 / c) * (1 / N + D / N ^ 2)
  have hrhs : (2 / c) * (1 / N + D / N ^ 2) =
      2 * (N + D) / (c * N ^ 2) := by field_simp
  rw [hrhs]
  calc
    2 * Real.exp (-(c * N ^ 2 / max N D)) ≤
        2 * max N D / (c * N ^ 2) := by
      calc
        _ ≤ 2 * (max N D / (c * N ^ 2)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = _ := by ring
    _ ≤ 2 * (N + D) / (c * N ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (by norm_num)) hC.le

/-- The reciprocal of a positive integer, totalized to zero at zero, is
bounded by a reciprocal threshold plus an exponential tail at that threshold.

Proof route: split on `m = 0`, `t ≤ m`, and `m < t`. In the last case,
`exp (t-m) ≥ 1` and the guarded inverse is at most one. -/
theorem guarded_inverse_le_exp (t : ℝ) (ht : 0 < t) (m : ℕ) :
    (if 0 < m then (m : ℝ)⁻¹ else 0) ≤
      t⁻¹ + Real.exp t * Real.exp (-(m : ℝ)) := by
  by_cases hm : m = 0
  · simpa [hm] using (show (0 : ℝ) ≤ t⁻¹ + Real.exp t by positivity)
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  simp only [hm0, ↓reduceIte]
  by_cases htm : t ≤ (m : ℝ)
  · have hi : (m : ℝ)⁻¹ ≤ t⁻¹ := (inv_le_inv₀ hmR ht).2 htm
    nlinarith [Real.exp_pos t, Real.exp_pos (-(m : ℝ))]
  · have hmt : (m : ℝ) < t := lt_of_not_ge htm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hi : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hmR).2 hm1
    have he : 1 ≤ Real.exp t * Real.exp (-(m : ℝ)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    nlinarith [inv_nonneg.mpr ht.le]

/-- At zero occupancy, the indicator of the bad event is bounded by the
Laplace kernel; at positive occupancy its left side is zero. -/
theorem zero_indicator_le_exp (m : ℕ) :
    (if m = 0 then (1 : ℝ) else 0) ≤ Real.exp (-(m : ℝ)) := by
  by_cases hm : m = 0
  · simp [hm]
  · simp [hm, Real.exp_nonneg]

/-- A [positive birthday exponent](hyp:c,hc) gives [a guarded reciprocal
occupancy rate with the uniform `1/n + d/n²` form](goal) across positive sample
sizes and finite dimensions.

Proof route: apply `birthday_laplace_rate` with `c/2`, then use
`max n d ≤ n + d` to bound the explicit reciprocal term. -/
theorem birthday_reciprocal_rate (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n d : ℕ), 0 < n →
      2 * max (n : ℝ) (d : ℝ) / (c * (n : ℝ) ^ 2) +
        2 * Real.exp (-(c * (n : ℝ) ^ 2 /
          (2 * max (n : ℝ) (d : ℝ)))) ≤
      B * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) := by
  obtain ⟨B, hB, hrate⟩ := birthday_laplace_rate (c / 2) (by positivity)
  refine ⟨2 / c + B, by positivity, ?_⟩
  intro n d hn
  let N : ℝ := n
  let D : ℝ := d
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hD : 0 ≤ D := Nat.cast_nonneg d
  have hM : max N D ≤ N + D := max_le (by linarith) (by linarith)
  have hC : 0 < c * N ^ 2 := mul_pos hc (sq_pos_of_pos hN)
  have hrec : 2 * max N D / (c * N ^ 2) ≤
      (2 / c) * (1 / N + D / N ^ 2) := by
    have heq : (2 / c) * (1 / N + D / N ^ 2) =
        2 * (N + D) / (c * N ^ 2) := by field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) hC.le
  have htail := hrate n d hn
  have harg : -(c / 2 * N ^ 2 / max N D) =
      -(c * N ^ 2 / (2 * max N D)) := by ring
  change 2 * max N D / (c * N ^ 2) +
      2 * Real.exp (-(c * N ^ 2 / (2 * max N D))) ≤
      (2 / c + B) * (1 / N + D / N ^ 2)
  rw [← harg]
  have htail' : 2 * Real.exp (-(c / 2 * N ^ 2 / max N D)) ≤
      B * (1 / N + D / N ^ 2) := htail
  nlinarith [hrec, htail']

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
