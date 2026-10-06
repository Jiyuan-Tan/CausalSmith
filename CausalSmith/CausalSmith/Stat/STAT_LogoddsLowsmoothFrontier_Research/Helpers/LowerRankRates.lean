module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Ceiling ranks for the mixed and fair lower rates

One rank estimate applies with s = α + β to the mixed priors and s = 2β
to the fair priors. It controls occupancy and the Hellinger budget and
retains a uniform lower bound on the amplitude separation.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Ceiling selection has the roadmap's two-sided rank bounds.](goal) Under [the stated assumptions](hyp:hL,hs,hn). -/
-- @node: lower_rank_ceiling_bounds
lemma lower_rank_ceiling_bounds (L s : ℝ) (hL : 1 ≤ L) (hs : 0 < s)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ L*(n : ℝ)^(2/(2*s+1)) ≤ k ∧
      (k : ℝ) ≤ (L+1)*(n : ℝ)^(2/(2*s+1)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hp : 0 < (n : ℝ)^(2/(2*s+1)) := Real.rpow_pos_of_pos hn0 _
  have hp1 : 1 ≤ (n : ℝ)^(2/(2*s+1)) :=
    Real.one_le_rpow hn1 (by positivity)
  let k := ⌈L*(n : ℝ)^(2/(2*s+1))⌉₊
  refine ⟨k, (Nat.one_le_ceil_iff).2 (mul_pos (by linarith) hp), Nat.le_ceil _, ?_⟩
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ L*(n : ℝ)^(2/(2*s+1)) by positivity)
  dsimp only [k]
  nlinarith

/-- [A rank above L times the target controls both occupancy and the
balanced power budget. [the documented result](goal) Under [the stated assumptions](hyp:hn,hk,hkl). Under [the stated assumptions](hyp:hL,hs,hsu). -/
-- @node: lower_rank_budget
lemma lower_rank_budget (L s : ℝ) (hL : 1 ≤ L) (hs : 0 < s) (hsu : s ≤ 1/2)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkl : L*(n : ℝ)^(2/(2*s+1)) ≤ k) :
    (n : ℝ)/(k : ℝ) ≤ 1/L ∧
      (n : ℝ)^2*(k : ℝ)^(-(2*s+1)) ≤ 1/L := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hL0 : 0 < L := by linarith
  have hd : 0 < 2*s+1 := by linarith
  have hp : 1 ≤ 2/(2*s+1) := (le_div_iff₀ hd).2 (by linarith)
  have hnp : (n : ℝ) ≤ (n : ℝ)^(2/(2*s+1)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hp
  have hLn : L*(n : ℝ) ≤ k :=
    (mul_le_mul_of_nonneg_left hnp hL0.le).trans hkl
  constructor
  · apply (div_le_iff₀ hk0).2
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ hL0).2
    simpa only [mul_comm] using hLn
  · have hLpow : L ≤ L^(2*s+1) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
        (by linarith : (1 : ℝ) ≤ 2*s+1)
    have hpower : (L*(n : ℝ)^(2/(2*s+1)))^(2*s+1) =
        L^(2*s+1)*(n : ℝ)^2 := by
      rw [Real.mul_rpow hL0.le (by positivity), ← Real.rpow_mul hn0.le]
      have he : 2/(2*s+1)*(2*s+1) = 2 := by field_simp
      rw [he, Real.rpow_two]
    have hden : L*(n : ℝ)^2 ≤ (k : ℝ)^(2*s+1) := by
      calc
        _ ≤ L^(2*s+1)*(n : ℝ)^2 :=
          mul_le_mul_of_nonneg_right hLpow (sq_nonneg _)
        _ = _ := hpower.symm
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hkl hd.le
    rw [Real.rpow_neg hk0.le, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hk0 _)).2
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ hL0).2
    simpa only [mul_comm] using hden

/-- [The ceiling costs a fixed square-root factor, uniformly over the entire
rough numerator regime and over the fair exponent s = 2β. [the documented result](goal) Under [the stated assumptions](hyp:hn,hk,hku). Under [the stated assumptions](hyp:hL,hs,hsu). -/
-- @node: lower_rank_separation
lemma lower_rank_separation (L s : ℝ) (hL : 1 ≤ L) (hs : 0 < s) (hsu : s ≤ 1/2)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hku : (k : ℝ) ≤ (L+1)*(n : ℝ)^(2/(2*s+1))) :
    (L+1)^(-(1/2 : ℝ))*(n : ℝ)^(-(2*s/(2*s+1))) ≤ (k : ℝ)^(-s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hL0 : 0 < L+1 := by linarith
  have hcoef : (L+1)^(-(1/2 : ℝ)) ≤ (L+1)^(-s) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have he : ((L+1)*(n : ℝ)^(2/(2*s+1)))^(-s) =
      (L+1)^(-s)*(n : ℝ)^(-(2*s/(2*s+1))) := by
    rw [Real.mul_rpow hL0.le (by positivity), ← Real.rpow_mul hn0.le]
    congr 2
    ring
  calc
    _ ≤ (L+1)^(-s)*(n : ℝ)^(-(2*s/(2*s+1))) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := he.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hk0 hku (by linarith)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
