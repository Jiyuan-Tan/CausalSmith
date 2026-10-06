module
public import Causalean.Mathlib.Probability.SubGaussian.SuffixBlock
public import Mathlib.Data.Nat.Log

/-!
# Finite dyadic partition of an ordered suffix

Every positive integer index at or above a starting index belongs to exactly
one dyadic block.  The finite sum identity here isolates the index bookkeeping
used by the Gaussian suffix estimate.
-/

public section

namespace Causalean.Mathlib.Probability.SubGaussian

/-- Given [a finite index range](hyp:N), [a starting index](hyp:m), [the
starting-index lower bound](hyp:hm), and [real weights on that range](hyp:f),
[the weighted suffix is exactly partitioned into dyadic blocks](goal).

Proof strategy: for an included index `n = k+1`, take
`j = Nat.log 2 (n / m)`.  Since `m ≥ 1`, the quotient is positive and
`2^j m ≤ n < 2^(j+1) m`.  The block number is below `N+1` because
`j ≤ n ≤ N`.  The dyadic intervals are disjoint, so swapping the two
finite sums counts each included index exactly once. -/
theorem dyadic_suffix_partition (N m : ℕ) (hm : 1 ≤ m)
    (f : Fin N → ℝ) :
    (∑ k : Fin N, if m ≤ k.val + 1 then f k else 0) =
      ∑ j ∈ Finset.range (N + 1),
        ∑ k : Fin N,
          if 2 ^ j * m ≤ k.val + 1 ∧ k.val + 1 < 2 * (2 ^ j * m)
          then f k else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  let n := k.val + 1
  let q := n / m
  have hm0 : 0 < m := hm
  by_cases hmn : m ≤ n
  · have hq : q ≠ 0 := (Nat.div_pos hmn hm0).ne'
    let j₀ := Nat.log 2 q
    have hj₀ : j₀ ∈ Finset.range (N + 1) := by
      apply Finset.mem_range.mpr
      have hle : j₀ ≤ n :=
        (Nat.log_le_self 2 q).trans (Nat.div_le_self n m)
      have hn : n ≤ N := by
        dsimp [n]
        exact k.isLt
      omega
    have hblock : ∀ j : ℕ,
        (2 ^ j * m ≤ n ∧ n < 2 * (2 ^ j * m)) ↔ j = j₀ := by
      intro j
      constructor
      · rintro ⟨hlo, hhi⟩
        have hlo' : 2 ^ j ≤ q :=
          (Nat.le_div_iff_mul_le hm0).2 hlo
        have hhi' : q < 2 ^ (j + 1) := by
          apply (Nat.div_lt_iff_lt_mul hm0).2
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hhi
        exact (Nat.log_eq_of_pow_le_of_lt_pow hlo' hhi').symm
      · intro hj
        subst j
        constructor
        · exact (Nat.le_div_iff_mul_le hm0).1 (Nat.pow_log_le_self 2 hq)
        · have hhi' := Nat.lt_pow_succ_log_self (by omega : 1 < 2) q
          have hhi'' := (Nat.div_lt_iff_lt_mul hm0).1 hhi'
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hhi''
    rw [Finset.sum_eq_single_of_mem j₀ hj₀]
    · change (if m ≤ n then f k else 0) =
          (if 2 ^ j₀ * m ≤ n ∧ n < 2 * (2 ^ j₀ * m) then f k else 0)
      simp [hmn, (hblock j₀).2 rfl]
    · intro j _ hj
      have : ¬ (2 ^ j * m ≤ n ∧ n < 2 * (2 ^ j * m)) := by
        simpa only [hblock] using hj
      change (if 2 ^ j * m ≤ n ∧ n < 2 * (2 ^ j * m) then f k else 0) = 0
      simp [this]
  · have hzero : ∀ j : ℕ,
        ¬ (2 ^ j * m ≤ n ∧ n < 2 * (2 ^ j * m)) := by
      intro j h
      have hpow : 0 < 2 ^ j := by positivity
      have : m ≤ 2 ^ j * m := by nlinarith
      omega
    change (if m ≤ n then f k else 0) =
      ∑ j ∈ Finset.range (N + 1),
        if 2 ^ j * m ≤ n ∧ n < 2 * (2 ^ j * m) then f k else 0
    rw [if_neg hmn]
    symm
    apply Finset.sum_eq_zero
    intro j _
    simp [hzero j]

end Causalean.Mathlib.Probability.SubGaussian
