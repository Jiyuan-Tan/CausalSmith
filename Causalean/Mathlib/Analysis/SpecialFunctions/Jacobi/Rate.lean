module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Moments

/-!
# Uniform power bounds for shifted Jacobi moments

At fixed `α > 0`, the normalized rising-factorial ratio has size
`(k+1)^(-α)`.  Squaring this gives the two-sided moment rate.
-/

public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open MeasureTheory intervalIntegral

/-- A [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), gives [positive uniform lower and upper power bounds for the factorial-to-rising-factorial ratio](goal).

At fixed positive `α`, the ratio `k!/(α+1)ₖ` is bounded above and below
by positive multiples of `(k+1)^(-α)`, uniformly in natural `k`. -/
theorem factorial_div_rising_power_bounds (α : ℝ) (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ k : ℕ,
        c * ((k + 1 : ℕ) : ℝ) ^ (-α) ≤
          ((Nat.factorial k : ℝ) / rising (α + 1) k) ∧
        ((Nat.factorial k : ℝ) / rising (α + 1) k) ≤
          C * ((k + 1 : ℕ) : ℝ) ^ (-α) := by
  have hprod (n : ℕ) :
      (∏ j ∈ Finset.range (n + 1), (α + (j : ℝ))) =
        α * rising (α + 1) n := by
    induction n with
    | zero => simp [rising]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      change α * rising (α + 1) n * (α + ↑(n + 1)) =
        α * (ascPochhammer ℝ (n + 1)).eval (α + 1)
      rw [ascPochhammer_succ_eval]
      change α * (ascPochhammer ℝ n).eval (α + 1) * (α + ↑(n + 1)) =
        α * ((ascPochhammer ℝ n).eval (α + 1) * (α + 1 + ↑n))
      push_cast
      ring
  let f : ℕ → ℝ := fun k => Real.GammaSeq α (k + 1)
  have hfpos (k : ℕ) : 0 < f k := by
    simp only [f, Real.GammaSeq]
    apply div_pos
    · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (by positivity)
    · exact Finset.prod_pos fun j hj => by
        have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
        positivity
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have hlim : Filter.Tendsto f Filter.atTop (nhds (Real.Gamma α)) := by
    exact (Real.GammaSeq_tendsto_Gamma α).comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  obtain ⟨D, hD⟩ := (hlim.inv₀ hΓ.ne').bddAbove_range
  have hBpos : 0 < B := (hfpos 0).trans_le (hB ⟨0, rfl⟩)
  have hDpos : 0 < D := (inv_pos.mpr (hfpos 0)).trans_le (hD ⟨0, rfl⟩)
  have hflo (k : ℕ) : 1 / D ≤ f k := by
    apply (div_le_iff₀ hDpos).2
    have hi : (f k)⁻¹ ≤ D := hD ⟨k, rfl⟩
    have hu := mul_le_mul_of_nonneg_right hi (le_of_lt (hfpos k))
    have he : (f k)⁻¹ * f k = 1 := inv_mul_cancel₀ (hfpos k).ne'
    nlinarith
  have hfhi (k : ℕ) : f k ≤ B := hB ⟨k, rfl⟩
  have hscaled (k : ℕ) :
      ((k + 1 : ℕ) : ℝ) ^ α *
          ((Nat.factorial k : ℝ) / rising (α + 1) k) =
        f k * (α * (α + (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ)) := by
    have hr : 0 < rising (α + 1) k := rising_pos _ _ (by linarith)
    have hr' : 0 < rising (α + 1) (k + 1) := rising_pos _ _ (by linarith)
    have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have ha : 0 < α + (k : ℝ) + 1 := by positivity
    simp only [f, Real.GammaSeq]
    rw [hprod (k + 1), Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [rising]
    rw [ascPochhammer_succ_eval]
    field_simp
    ring
  refine ⟨α / D, B * α * (α + 1), div_pos hα hDpos,
    mul_pos (mul_pos hBpos hα) (by linarith), ?_⟩
  intro k
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hratio : 0 < rising (α + 1) k := rising_pos _ _ (by linarith)
  have hfaclow : α ≤ α * (α + (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hk).2
    push_cast
    nlinarith [(mul_nonneg (sq_nonneg α) (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)))]
  have hfachi : α * (α + (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) ≤ α * (α + 1) := by
    apply (div_le_iff₀ hk).2
    push_cast
    nlinarith [(mul_nonneg (sq_nonneg α) (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)))]
  have hfacpos : 0 ≤ α * (α + (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) :=
    le_trans hα.le hfaclow
  have hlo : α / D ≤ ((k + 1 : ℕ) : ℝ) ^ α *
      ((Nat.factorial k : ℝ) / rising (α + 1) k) := by
    rw [hscaled]
    calc
      α / D = (1 / D) * α := by ring
      _ ≤ f k * α := mul_le_mul_of_nonneg_right (hflo k) hα.le
      _ ≤ f k * (α * (α + (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hfaclow (hfpos k).le
  have hhi : ((k + 1 : ℕ) : ℝ) ^ α *
      ((Nat.factorial k : ℝ) / rising (α + 1) k) ≤ B * α * (α + 1) := by
    rw [hscaled]
    calc
      _ ≤ B * (α * (α + (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (hfhi k) hfacpos
      _ ≤ B * (α * (α + 1)) := mul_le_mul_of_nonneg_left hfachi hBpos.le
      _ = B * α * (α + 1) := by ring
  have hp : 0 < ((k + 1 : ℕ) : ℝ) ^ α := Real.rpow_pos_of_pos hk _
  constructor
  · rw [Real.rpow_neg hk.le]
    change (α / D) / (((k + 1 : ℕ) : ℝ) ^ α) ≤ _
    exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using hlo)
  · rw [Real.rpow_neg hk.le]
    change _ ≤ (B * α * (α + 1)) / (((k + 1 : ℕ) : ℝ) ^ α)
    exact (le_div_iff₀ hp).2 (by simpa [mul_comm] using hhi)

/-- A [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), gives [positive constants c and C, depending only on α, such that for every degree k ≥ 1 the zeroth weighted moment, α times the integral over the unit interval of x^(α−1) times the shifted Jacobi perturbation of degree k, lies between c·(k+1)^(−2α) and C·(k+1)^(−2α)](goal).

The exact zeroth weighted moment has positive two-sided bounds of order
`(k+1)^(-2α)`, with constants depending only on `α`. -/
theorem h_zeroth_moment_power_bounds (α : ℝ) (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ k : ℕ, 1 ≤ k →
        c * ((k + 1 : ℕ) : ℝ) ^ (-(2 * α)) ≤
          α * (∫ x in (0 : ℝ)..1, x ^ (α - 1) * h k α x) ∧
        α * (∫ x in (0 : ℝ)..1, x ^ (α - 1) * h k α x) ≤
          C * ((k + 1 : ℕ) : ℝ) ^ (-(2 * α)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := factorial_div_rising_power_bounds α hα
  refine ⟨c ^ 2, C ^ 2, sq_pos_of_pos hc, sq_pos_of_pos hC, ?_⟩
  intro k _
  obtain ⟨hlo, hhi⟩ := hb k
  have hp : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (-α) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  have hr : 0 ≤ (Nat.factorial k : ℝ) / rising (α + 1) k :=
    (div_pos (by positivity) (rising_pos _ _ (by linarith))).le
  have hpow : ((k + 1 : ℕ) : ℝ) ^ (-(2 * α)) =
      (((k + 1 : ℕ) : ℝ) ^ (-α)) ^ 2 := by
    rw [show -(2 * α) = -α * (2 : ℝ) by ring,
      Real.rpow_mul (by positivity), Real.rpow_ofNat]
  rw [h_zeroth_moment_rising k α hα, hpow]
  constructor
  · simpa only [mul_pow] using
      (sq_le_sq₀ (mul_nonneg hc.le hp) hr).2 hlo
  · simpa only [mul_pow] using
      (sq_le_sq₀ hr (mul_nonneg hC.le hp)).2 hhi

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
