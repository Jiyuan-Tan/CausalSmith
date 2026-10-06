module
public import Causalean.Mathlib.Analysis.SpecificLimits.PolynomialGeometric
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Calibrated series constants for the copula occupancy calculation. -/
public section

open Causalean.Mathlib.Analysis.SpecificLimits.PolynomialGeometric
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The public fine-rank condition puts both occupancy moments inside the geometric regime. This statement assumes [the hpos condition](hyp:hpos), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: occupancy_ratio_calibration
lemma occupancy_ratio_calibration (n K : ℕ) (hpos : 0 < K) (hK : 2 ^ 40 * n ≤ K) :
    0 ≤ 8 * Real.exp 1 * (n : ℝ) / K ∧
    8 * Real.exp 1 * (n : ℝ) / K ≤ 24 * (n : ℝ) / K ∧
    2 ^ 11 * (8 * Real.exp 1 * (n : ℝ) / K) ≤ 1 / 2 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hpos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hscale : (2 : ℝ) ^ 40 * n ≤ K := by exact_mod_cast hK
  have hratio : (n : ℝ) / K ≤ 1 / 2 ^ 40 := by
    apply (div_le_iff₀ hk).2
    nlinarith
  have hmajor : 8 * Real.exp 1 * (n : ℝ) / K ≤ 24 * (n : ℝ) / K := by
    apply div_le_div_of_nonneg_right _ hk.le
    nlinarith [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hn]
  refine ⟨by positivity, hmajor, ?_⟩
  have hmajor' : 8 * Real.exp 1 * (n : ℝ) / K ≤ 24 * ((n : ℝ) / K) := by
    simpa only [mul_div_assoc] using hmajor
  nlinarith

/-- Both all-orders moments have the explicit quadratic envelope from the occupancy roadmap. This statement assumes [the hpos condition](hyp:hpos), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: occupancy_collision_series_bounds
lemma occupancy_collision_series_bounds (n K : ℕ) (hpos : 0 < K)
    (hK : 2 ^ 40 * n ≤ K) :
    let z := 8 * Real.exp 1 * (n : ℝ) / K
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ 11 * z ^ (j + 2)) ∧
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ 6 * z ^ (j + 2)) ∧
    (∑' j : ℕ, (j + 2 : ℝ) ^ 11 * z ^ (j + 2)) ≤ 2 ^ 12 * (24 * (n : ℝ) / K) ^ 2 ∧
    (∑' j : ℕ, (j + 2 : ℝ) ^ 6 * z ^ (j + 2)) ≤ 2 ^ 7 * (24 * (n : ℝ) / K) ^ 2 := by
  dsimp only
  obtain ⟨hz, hmajor, h11⟩ := occupancy_ratio_calibration n K hpos hK
  have h6 : (2 : ℝ) ^ 6 * (8 * Real.exp 1 * (n : ℝ) / K) ≤ 1 / 2 := by
    nlinarith
  refine ⟨polynomial_geometric_series_summable 11 _ hz h11,
    polynomial_geometric_series_summable 6 _ hz h6, ?_, ?_⟩
  · exact (polynomial_geometric_series_bound 11 _ hz h11).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hmajor 2) (by positivity))
  · exact (polynomial_geometric_series_bound 6 _ hz h6).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hmajor 2) (by positivity))

/-- The two combinatorial overcount series fit the paper's activity-budget constants. This statement assumes [the hpos condition](hyp:hpos), [the hM condition](hyp:hM), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: occupancy_numeric_budget_bounds
lemma occupancy_numeric_budget_bounds (n K M : ℕ) (hpos : 0 < K)
    (hM : 0 < M) (hK : 2 ^ 40 * n ≤ K) (a u ε : ℝ) :
    let z := 8 * Real.exp 1 * (n : ℝ) / K
    2 ^ 14 * a ^ 4 * u ^ 4 * ε ^ 2 * K *
        (∑' j : ℕ, (j + 2 : ℝ) ^ 11 * z ^ (j + 2)) ≤
      2 ^ 38 * a ^ 4 * u ^ 4 * ε ^ 2 * (n : ℝ) ^ 2 / K ∧
    2 ^ 17 * a ^ 4 * u ^ 4 * ε ^ 2 * (K : ℝ) ^ 2 / M *
        (∑' j : ℕ, (j + 2 : ℝ) ^ 6 * z ^ (j + 2)) ^ 2 ≤
      2 ^ 56 * a ^ 4 * u ^ 4 * ε ^ 2 * (n : ℝ) ^ 4 / ((M : ℝ) * K ^ 2) := by
  dsimp only
  have hk : (0 : ℝ) < K := by exact_mod_cast hpos
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨_, _, h11, h6⟩ := occupancy_collision_series_bounds n K hpos hK
  have hs6 : 0 ≤ ∑' j : ℕ, (j + 2 : ℝ) ^ 6 *
      (8 * Real.exp 1 * (n : ℝ) / K) ^ (j + 2) := tsum_nonneg (fun _ => by positivity)
  constructor
  · calc
      _ ≤ 2 ^ 14 * a ^ 4 * u ^ 4 * ε ^ 2 * K *
          (2 ^ 12 * (24 * (n : ℝ) / K) ^ 2) :=
        mul_le_mul_of_nonneg_left h11 (by positivity)
      _ = (2 ^ 26 * 24 ^ 2) * (a ^ 4 * u ^ 4 * ε ^ 2 * (n : ℝ) ^ 2 / K) := by
        field_simp
      _ ≤ 2 ^ 38 * (a ^ 4 * u ^ 4 * ε ^ 2 * (n : ℝ) ^ 2 / K) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ 2 ^ 17 * a ^ 4 * u ^ 4 * ε ^ 2 * (K : ℝ) ^ 2 / M *
          (2 ^ 7 * (24 * (n : ℝ) / K) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs6 h6 2) (by positivity)
      _ = (2 ^ 31 * 24 ^ 4) *
          (a ^ 4 * u ^ 4 * ε ^ 2 * (n : ℝ) ^ 4 / ((M : ℝ) * K ^ 2)) := by
        field_simp
      _ ≤ 2 ^ 56 * (a ^ 4 * u ^ 4 * ε ^ 2 * (n : ℝ) ^ 4 / ((M : ℝ) * K ^ 2)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
