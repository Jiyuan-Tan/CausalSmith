module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveCells

/-!
# Dyadic scales for Hölder cube geometry

A positive interval gap is bracketed by consecutive dyadic time widths. The
lower width gives the quantitative power bound used by the cube curve.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- A positive gap of at most one lies between two consecutive time widths
of a `d`-dimensional dyadic traversal. -/
theorem exists_dyadicScale (d : ℕ) (hd : 0 < d) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ n : ℕ,
      (1 : ℝ) / (2 : ℝ) ^ (d * (n + 1)) ≤ δ ∧
      δ ≤ (1 : ℝ) / (2 : ℝ) ^ (d * n) := by
  have hypos : 0 < ((1 : ℝ) / 2 ^ d) := by positivity
  have hylt : ((1 : ℝ) / 2 ^ d) < 1 := by
    have h : 1 < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
    exact (div_lt_one (by positivity)).2 h
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hδ hδ1 hypos hylt
  have hw (k : ℕ) : ((1 : ℝ) / 2 ^ d) ^ k = 1 / (2 : ℝ) ^ (d * k) := by
    simp [one_div, inv_pow, ← pow_mul, mul_comm d k]
  exact ⟨n, (hw (n + 1)) ▸ hn.le, (hw n) ▸ hn'⟩

/-- Given [a dimension d and dyadic level n](hyp:d,n), [a positive dimension](hyp:hd), and [a gap δ at least as large as the next time width 1/2^(d(n+1))](hyp:δ,hδ),
[the squared spatial width (1/2^n)² is at most 4·δ^(2/d)](goal). -/
theorem dyadicScale_sq_bound (d n : ℕ) (hd : 0 < d) {δ : ℝ}
    (hδ : (1 : ℝ) / (2 : ℝ) ^ (d * (n + 1)) ≤ δ) :
    ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 ≤
      4 * δ ^ ((2 : ℝ) / d) := by
  have ha : 0 ≤ ((1 : ℝ) / 2 ^ (n + 1)) := by positivity
  have hw : (1 : ℝ) / 2 ^ (d * (n + 1)) =
      ((1 : ℝ) / 2 ^ (n + 1)) ^ d := by
    simp [one_div, inv_pow, ← pow_mul, mul_comm d (n + 1)]
  have hp : 0 ≤ (2 : ℝ) / d := by positivity
  have hr := Real.rpow_le_rpow
    (by positivity : 0 ≤ (1 : ℝ) / 2 ^ (d * (n + 1))) hδ hp
  rw [hw] at hr
  have hpow : (((1 : ℝ) / 2 ^ (n + 1)) ^ d) ^ ((2 : ℝ) / d) =
      ((1 : ℝ) / 2 ^ (n + 1)) ^ 2 := by
    rw [show (2 : ℝ) / d = (d : ℝ)⁻¹ * 2 by ring,
      Real.rpow_mul (pow_nonneg ha d),
      Real.pow_rpow_inv_natCast ha (Nat.ne_of_gt hd)]
    exact Real.rpow_natCast _ 2
  rw [hpow] at hr
  have halg : ((1 : ℝ) / 2 ^ n) ^ 2 =
      4 * ((1 : ℝ) / 2 ^ (n + 1)) ^ 2 := by
    rw [pow_succ]
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  rw [halg]
  exact mul_le_mul_of_nonneg_left hr (by norm_num)

end Causalean.Mathlib.Topology.SpaceFillingCurve
