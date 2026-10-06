module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Finite occupancy majorants

Binomial and factorial bounds absorb labelled subset counts into powers of
8 exp(1) n/K. These finite bounds hold at every positive density; the optional
geometric estimate uses the required small-density hypothesis explicitly.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- [The density parameter](goal) for [n uniform draws into K cells](hyp:n,K)
is eight times exp(1) times n/K. -/
noncomputable def occupancyZ (n K : ℕ) : ℝ := 8 * Real.exp 1 * n / K

/-- [The finite majorant](goal) of [order p](hyp:p) for [sample and cell
counts](hyp:n,K) sums sizes two through n. -/
noncomputable def occupancySeries (p n K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n - 1), (j + 2 : ℝ) ^ p * occupancyZ n K ^ (j + 2)

/-- With [positive cell count](hyp:hK) and [size at least two](hyp:hm),
[the binomial subset count times the connected-assignment and mark-size
weights is bounded by its exponential majorant term](goal), for [n,m,K](hyp:n,m,K).

Use Nat.choose_le_pow_div and Stirling.le_factorial_stirling, discarding the square
root factor (which is at least one). The extra power m is harmless slack.
-/
theorem labelled_weight_majorant (n m K : ℕ) (hK : 0 < K) (hm : 2 ≤ m)
    (p : ℕ) :
    (n.choose m : ℝ) * (m : ℝ) ^ p * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m ≤
      (m : ℝ) ^ (p + 1) * occupancyZ n K ^ m := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * m) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  have hst : ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
    calc
      _ ≤ Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ _ := Stirling.le_factorial_stirling m
  have hpow : (m : ℝ) ^ m ≤ (m.factorial : ℝ) * Real.exp 1 ^ m := by
    rw [div_pow, div_le_iff₀ (by positivity)] at hst
    exact hst
  have hc : (n.choose m : ℝ) * (m : ℝ) ^ m ≤ (n : ℝ) ^ m * Real.exp 1 ^ m := by
    calc
      _ ≤ ((n : ℝ) ^ m / (m.factorial : ℝ)) * (m : ℝ) ^ m := by
        gcongr
        exact Nat.choose_le_pow_div m n
      _ ≤ ((n : ℝ) ^ m / (m.factorial : ℝ)) *
          ((m.factorial : ℝ) * Real.exp 1 ^ m) := by gcongr
      _ = _ := by field_simp
  have hKpow : (0 : ℝ) < (K : ℝ) ^ m := by positivity
  calc
    _ = ((n.choose m : ℝ) * (m : ℝ) ^ m) * ((m : ℝ) ^ p * 8 ^ m) /
        (K : ℝ) ^ m := by ring
    _ ≤ ((n : ℝ) ^ m * Real.exp 1 ^ m) * ((m : ℝ) ^ p * 8 ^ m) /
        (K : ℝ) ^ m := by gcongr
    _ = (m : ℝ) ^ p * occupancyZ n K ^ m := by
      simp only [occupancyZ, div_pow, mul_pow]
      ring
    _ ≤ (m : ℝ) ^ (p + 1) * occupancyZ n K ^ m := by
      rw [pow_succ]
      apply mul_le_mul_of_nonneg_right
      · exact le_mul_of_one_le_right (by positivity) (by linarith)
      · unfold occupancyZ
        positivity


/-- With [at least two draws and positive cell count](hyp:hn,hK),
[the finite sum of labelled occupancy terms is bounded by the finite
exponential series](goal), for [order and counts](hyp:p,n,K). -/
theorem finite_labelled_weight_majorant (p n K : ℕ) (hn : 2 ≤ n) (hK : 0 < K) :
    (∑ m ∈ Finset.Icc 2 n,
      (n.choose m : ℝ) * (m : ℝ) ^ p * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m) ≤
      occupancySeries (p + 1) n K := by
  calc
    _ ≤ ∑ m ∈ Finset.Icc 2 n, (m : ℝ) ^ (p + 1) * occupancyZ n K ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      exact labelled_weight_majorant n m K hK (Finset.mem_Icc.mp hm).1 p
    _ = occupancySeries (p + 1) n K := by
      have hi : Finset.Icc 2 n = Finset.Ico 2 (n + 1) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hi, Finset.sum_Ico_eq_sum_range]
      have hl : n + 1 - 2 = n - 1 := by omega
      simp only [hl, occupancySeries, Nat.cast_add, Nat.cast_ofNat]
      congr 1
      ext j
      simp [add_comm]


/-- For [a sample size n and a cell count K](hyp:n,K) with [K positive](hyp:hK) and [density n / K
at most 2 to the power −40](hyp:hdensity), [the occupancy parameter lies between zero and 2 to the
power −35](goal). -/
theorem occupancyZ_small (n K : ℕ) (hK : 0 < K)
    (hdensity : (n : ℝ) / K ≤ (2 : ℝ) ^ (-40 : ℤ)) :
    0 ≤ occupancyZ n K ∧ occupancyZ n K ≤ (2 : ℝ) ^ (-35 : ℤ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  constructor
  · unfold occupancyZ
    positivity
  · have he : Real.exp 1 ≤ 4 := le_trans Real.exp_one_lt_three.le (by norm_num)
    have hnK : (0 : ℝ) ≤ (n : ℝ) / K := by positivity
    calc
      occupancyZ n K = (8 * Real.exp 1) * ((n : ℝ) / K) := by
        unfold occupancyZ
        ring
      _ ≤ (8 * 4) * (2 : ℝ) ^ (-40 : ℤ) := by gcongr
      _ = (2 : ℝ) ^ (-35 : ℤ) := by norm_num


/-- For [an order p, a sample size n, and a cell count K](hyp:p,n,K) with [p at most
eleven](hyp:hp), [K positive](hyp:hK), and [density n / K at most 2 to the power
−40](hyp:hdensity), [the finite occupancy series is at most twice its size-two term, namely 2 · 2^p
times the square of the occupancy parameter](goal).

The ratio of consecutive terms is at most (3/2)^p times z. Bound it by one
half, then dominate by an elementary finite geometric sum; no infinite sum is needed.
-/
theorem occupancySeries_geometric_le (p n K : ℕ) (hp : p ≤ 11) (hK : 0 < K)
    (hdensity : (n : ℝ) / K ≤ (2 : ℝ) ^ (-40 : ℤ)) :
    occupancySeries p n K ≤ 2 * (2 : ℝ) ^ p * occupancyZ n K ^ 2 := by
  obtain ⟨hz, hzsmall⟩ := occupancyZ_small n K hK hdensity
  have hratio : (2 : ℝ) ^ p * occupancyZ n K ≤ 1 / 2 := by
    calc
      _ ≤ (2 : ℝ) ^ 11 * (2 : ℝ) ^ (-35 : ℤ) := by
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp)
          hzsmall hz (by positivity)
      _ ≤ 1 / 2 := by norm_num
  let t : ℕ → ℝ := fun j => (j + 2 : ℝ) ^ p * occupancyZ n K ^ (j + 2)
  have ht : ∀ j, 0 ≤ t j := by
    intro j
    dsimp [t]
    positivity
  have hstep : ∀ j, t (j + 1) ≤ t j / 2 := by
    intro j
    have hbase : (j : ℝ) + 1 + 2 ≤ 2 * ((j : ℝ) + 2) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    calc
      t (j + 1) ≤ (2 * ((j : ℝ) + 2)) ^ p * occupancyZ n K ^ (j + 1 + 2) := by
        dsimp [t]
        push_cast
        gcongr
      _ = t j * ((2 : ℝ) ^ p * occupancyZ n K) := by
        dsimp [t]
        rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ, mul_pow]
        ring
      _ ≤ t j * (1 / 2) := mul_le_mul_of_nonneg_left hratio (ht j)
      _ = t j / 2 := by ring
  have hsum : ∀ N, (∑ j ∈ Finset.range N, t j) + 2 * t N ≤ 2 * t 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hstep N
      change (∑ j ∈ Finset.range N, t j) + t N + 2 * t (N + 1) ≤ 2 * t 0
      linarith
  have hb := hsum (n - 1)
  have hn := ht (n - 1)
  have : (∑ j ∈ Finset.range (n - 1), t j) ≤ 2 * t 0 := by linarith
  simpa [occupancySeries, t, mul_assoc] using this


end Causalean.Stat.RandomGraph.PathOccupancy
