module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureHellinger
public import Mathlib.Data.Nat.Choose.Bounds

/-! # The numerical spanning-tree occupancy sum

The factorial and binomial envelopes reduce the non-singleton tree sum to the
finite cubic geometric series. The resulting bound retains the paper's explicit
96 exp(2) B² coefficient and its occupancy threshold.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The exponential-series bound supplies the factorial envelope needed for
rooted parent arrays of a positive number of vertices. [the documented result](goal) Under [the stated assumptions](hyp:hm). -/
-- @node: mixture_parent_array_factorial_bound
lemma mixture_parent_array_factorial_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ (m-1) / (m.factorial : ℝ) ≤ Real.exp 1 ^ m / (m : ℝ) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h := Real.pow_div_factorial_le_exp (m : ℝ) hmp.le m
  have he : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa using Real.exp_nat_mul 1 m
  rw [he] at h
  apply (le_div_iff₀ hmp).mpr
  have hp : (m : ℝ) ^ (m-1) * m = (m : ℝ) ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  simpa only [div_mul_eq_mul_div, hp] using h

/-- [Each non-singleton tree-count term is controlled by a cubic geometric term
with occupancy parameter 3 exp(1) B n/k. [the documented result](goal) Under [the stated assumptions](hyp:hk,hB). -/
-- @node: mixture_tree_sum_term_bound
lemma mixture_tree_sum_term_bound (n k j : ℕ) (hk : 1 ≤ k) (B : ℝ) (hB : 0 ≤ B) :
    ((j+2 : ℕ) : ℝ)^4 * B^(j+2) * (n.choose (j+2) : ℝ) *
        ((j+2 : ℕ) : ℝ)^(j+1) * (3/(k : ℝ))^(j+1) ≤
      Real.exp 1 * B * n * (((j : ℝ)+2)^3 *
        (3*Real.exp 1*B*n/(k : ℝ))^(j+1)) := by
  let m := j+2
  have hm : 1 ≤ m := by omega
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : (n.choose m : ℝ) ≤ (n : ℝ)^m / (m.factorial : ℝ) :=
    Nat.choose_le_pow_div m n
  have hp := mixture_parent_array_factorial_bound m hm
  have h1 := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ (m : ℝ)^4 * B^m * (m : ℝ)^(m-1) * (3/(k : ℝ))^(m-1) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (m : ℝ)^4 * B^m * (n : ℝ)^m * (3/(k : ℝ))^(m-1) by positivity)
  have hfirst :
      (m : ℝ)^4 * B^m * (n.choose m : ℝ) * (m : ℝ)^(m-1) * (3/(k : ℝ))^(m-1) ≤
      (m : ℝ)^4 * B^m * (n : ℝ)^m * (Real.exp 1^m/(m : ℝ)) *
        (3/(k : ℝ))^(m-1) := by
    calc
      _ ≤ (m : ℝ)^4 * B^m * ((n : ℝ)^m / (m.factorial : ℝ)) *
          (m : ℝ)^(m-1) * (3/(k : ℝ))^(m-1) := by nlinarith [h1]
      _ = ((m : ℝ)^4 * B^m * (n : ℝ)^m * (3/(k : ℝ))^(m-1)) *
          ((m : ℝ)^(m-1)/(m.factorial : ℝ)) := by ring
      _ ≤ _ := by simpa only [mul_assoc, mul_left_comm, mul_comm] using h2
  have hms : m-1 = j+1 := by simp [m]
  rw [hms] at hfirst
  convert hfirst using 1
  · dsimp [m]
    simp only [Nat.cast_add, Nat.cast_ofNat, pow_add, pow_succ, pow_one,
      mul_pow, div_pow]
    field_simp
    <;> ring

/-- [The complete finite spanning-tree envelope has the paper's quadratic
occupancy bound, with no singleton term. [the documented result](goal) Under [the stated assumptions](hyp:hq). Under [the stated assumptions](hyp:hk,hB). -/
-- @node: mixture_tree_sum_bound
lemma mixture_tree_sum_bound (n k N : ℕ) (hk : 1 ≤ k) (B : ℝ) (hB : 0 ≤ B)
    (hq : 3*Real.exp 1*B*n/(k : ℝ) ≤ 1/4) :
    (∑ j ∈ Finset.range N,
      ((j+2 : ℕ) : ℝ)^4 * B^(j+2) * (n.choose (j+2) : ℝ) *
        ((j+2 : ℕ) : ℝ)^(j+1) * (3/(k : ℝ))^(j+1)) ≤
      96*Real.exp 2*B^2*(n : ℝ)^2/(k : ℝ) := by
  have hq0 : 0 ≤ 3*Real.exp 1*B*n/(k : ℝ) := by positivity
  calc
    _ ≤ ∑ j ∈ Finset.range N, Real.exp 1 * B * n *
        (((j : ℝ)+2)^3 * (3*Real.exp 1*B*n/(k : ℝ))^(j+1)) := by
      exact Finset.sum_le_sum (fun j _ => mixture_tree_sum_term_bound n k j hk B hB)
    _ = Real.exp 1 * B * n * (∑ j ∈ Finset.range N,
        ((j : ℝ)+2)^3 * (3*Real.exp 1*B*n/(k : ℝ))^(j+1)) :=
      (Finset.mul_sum ..).symm
    _ ≤ Real.exp 1 * B * n * (32*(3*Real.exp 1*B*n/(k : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mixture_cubic_geometric_bound _ hq0 hq N) (by positivity)
    _ = _ := by
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [he]
      ring

/-- [The prescribed occupancy threshold controls the tree sum with B = 8,
exactly the base of the component Hellinger envelope. [the documented result](goal) Under [the stated assumptions](hyp:hnk). Under [the stated assumptions](hyp:hk). -/
-- @node: mixture_tree_sum_eight_bound
lemma mixture_tree_sum_eight_bound (n k N : ℕ) (hk : 1 ≤ k)
    (hnk : (n : ℝ)/(k : ℝ) ≤ 1/(96*Real.exp 1)) :
    (∑ j ∈ Finset.range N,
      ((j+2 : ℕ) : ℝ)^4 * (8 : ℝ)^(j+2) * (n.choose (j+2) : ℝ) *
        ((j+2 : ℕ) : ℝ)^(j+1) * (3/(k : ℝ))^(j+1)) ≤
      96*Real.exp 2*8^2*(n : ℝ)^2/(k : ℝ) := by
  apply mixture_tree_sum_bound n k N hk 8 (by norm_num)
  have h := mul_le_mul_of_nonneg_left hnk
    (show 0 ≤ 24*Real.exp 1 by positivity)
  have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have hr : 24*Real.exp 1 * (1/(96*Real.exp 1)) = (1/4 : ℝ) := by
    field_simp
    <;> ring
  rw [hr] at h
  convert h using 2 <;> first | rfl | ring

/-- [Multiplying the tree envelope by the component Taylor coefficient gives
the explicit constant for either choice of the amplitude product. [the documented result](goal) Under [the stated assumptions](hyp:hnk). Under [the stated assumptions](hyp:hk). -/
-- @node: mixture_weighted_tree_sum_bound
lemma mixture_weighted_tree_sum_bound (n k N : ℕ) (hk : 1 ≤ k)
    (hnk : (n : ℝ)/(k : ℝ) ≤ 1/(96*Real.exp 1)) (M ω : ℝ) :
    M^4*ω^2 * (∑ j ∈ Finset.range N,
      ((j+2 : ℕ) : ℝ)^4 * (8 : ℝ)^(j+2) * (n.choose (j+2) : ℝ) *
        ((j+2 : ℕ) : ℝ)^(j+1) * (3/(k : ℝ))^(j+1)) ≤
      (96*Real.exp 2*8^2*M^4)*(n : ℝ)^2/(k : ℝ)*ω^2 := by
  apply (mul_le_mul_of_nonneg_left (mixture_tree_sum_eight_bound n k N hk hnk)
    (show 0 ≤ M^4*ω^2 by positivity)).trans_eq
  ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier
