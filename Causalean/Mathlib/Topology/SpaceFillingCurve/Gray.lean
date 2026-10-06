module
public import Mathlib

/-!
# Reflected Gray order on dyadic cube children

The binary reflected Gray code provides an order of the `2^d` children of a
dyadic cube in which successive children share a face.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- [The reflected Gray code](goal) of [a natural-number index k](hyp:k) is [the bitwise
exclusive-or of k with k shifted right by one bit](step:1). -/
def reflectedGray (k : ℕ) : ℕ := Nat.xor k (k / 2)

/-- [The reflected-Gray bit](goal) of [a natural-number index k](hyp:k) at [bit position i](hyp:i)
is [the i-th binary digit of the reflected Gray code of k](step:1). -/
def grayBit (k i : ℕ) : Bool := Nat.testBit (reflectedGray k) i

private theorem grayBit_formula (k i : ℕ) :
    grayBit k i = (k.testBit i ^^ k.testBit (i + 1)) := by
  simp only [grayBit, reflectedGray, Nat.xor_eq, Nat.testBit_xor,
    Nat.testBit_div_two]

private theorem grayBit_even_odd_zero (n : ℕ) :
    grayBit (2 * n) 0 ≠ grayBit (2 * n + 1) 0 := by
  have he : (2 * n).testBit 0 = false := by simp [Nat.testBit_zero]
  have ho : (2 * n + 1).testBit 0 = true := by simp [Nat.testBit_zero]
  have hs : ∀ j, (2 * n).testBit (j + 1) = n.testBit j := by
    intro j
    rw [Nat.testBit_add_one]
    congr 1
    omega
  have ht : ∀ j, (2 * n + 1).testBit (j + 1) = n.testBit j := by
    intro j
    rw [Nat.testBit_add_one]
    congr 1
    omega
  rw [grayBit_formula, grayBit_formula, he, ho, hs, ht]
  cases n.testBit 0 <;> decide

private theorem grayBit_even_odd_succ (n j : ℕ) :
    grayBit (2 * n) (j + 1) = grayBit (2 * n + 1) (j + 1) := by
  have hs : ∀ m, (2 * n).testBit (m + 1) = n.testBit m := by
    intro m
    rw [Nat.testBit_add_one]
    congr 1
    omega
  have ht : ∀ m, (2 * n + 1).testBit (m + 1) = n.testBit m := by
    intro m
    rw [Nat.testBit_add_one]
    congr 1
    omega
  simp only [grayBit_formula, hs, ht]

private theorem grayBit_odd_even_zero (n : ℕ) :
    grayBit (2 * n + 1) 0 = grayBit (2 * (n + 1)) 0 := by
  have he (m : ℕ) : (2 * m).testBit 0 = false := by simp [Nat.testBit_zero]
  have ho : (2 * n + 1).testBit 0 = true := by simp [Nat.testBit_zero]
  have hs : (2 * n + 1).testBit 1 = n.testBit 0 := by
    rw [show 1 = 0 + 1 by omega, Nat.testBit_add_one]
    congr 1
    omega
  have ht : (2 * (n + 1)).testBit 1 = (n + 1).testBit 0 := by
    rw [show 1 = 0 + 1 by omega, Nat.testBit_add_one]
    congr 1
    omega
  have hp : (n + 1).testBit 0 = !n.testBit 0 := by
    by_cases h : n % 2 = 0
    · have h2 : (n + 1) % 2 = 1 := by omega
      simp [Nat.testBit_zero, h, h2]
    · have h1 : n % 2 = 1 := by omega
      have h2 : (n + 1) % 2 = 0 := by omega
      simp [Nat.testBit_zero, h1, h2]
  rw [grayBit_formula, grayBit_formula, ho, he, hs, ht, hp]
  cases n.testBit 0 <;> decide

private theorem grayBit_odd_succ (n j : ℕ) :
    grayBit (2 * n + 1) (j + 1) = grayBit n j := by
  have hs : ∀ m, (2 * n + 1).testBit (m + 1) = n.testBit m := by
    intro m
    rw [Nat.testBit_add_one]
    congr 1
    omega
  simp only [grayBit_formula, hs]

private theorem grayBit_even_succ (n j : ℕ) :
    grayBit (2 * n) (j + 1) = grayBit n j := by
  have hs : ∀ m, (2 * n).testBit (m + 1) = n.testBit m := by
    intro m
    rw [Nat.testBit_add_one]
    congr 1
    omega
  simp only [grayBit_formula, hs]

/-- Given [a cube dimension and child index](hyp:d,k) whose [successor remains in the dyadic grid](hyp:hk),
[the two consecutive Gray-code words differ in exactly one coordinate](goal). -/
theorem grayBit_adjacent (d k : ℕ) (hk : k + 1 < 2 ^ d) :
    ∃ i : Fin d,
      grayBit k i.val ≠ grayBit (k + 1) i.val ∧
      ∀ j : Fin d, j ≠ i → grayBit k j.val = grayBit (k + 1) j.val := by
  have hall : ∀ k : ℕ, ∃ i : ℕ,
      grayBit k i ≠ grayBit (k + 1) i ∧
      ∀ j : ℕ, j ≠ i → grayBit k j = grayBit (k + 1) j := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · have hm : m = 2 * (m / 2) := by omega
        refine ⟨0, ?_, ?_⟩
        · simpa only [← hm] using grayBit_even_odd_zero (m / 2)
        · intro j hj
          obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
          simpa only [← hm, Nat.succ_eq_add_one] using
            grayBit_even_odd_succ (m / 2) a
      · have hm : m = 2 * (m / 2) + 1 := by omega
        let n := m / 2
        have hn : n < m := by dsimp [n]; omega
        obtain ⟨i, hi, hother⟩ := ih n hn
        refine ⟨i + 1, ?_, ?_⟩
        · rw [hm, show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
            grayBit_odd_succ, grayBit_even_succ]
          exact hi
        · intro j hj
          cases j with
          | zero =>
              rw [hm, show 2 * (m / 2) + 1 + 1 = 2 * (n + 1) by
                dsimp [n]
                omega]
              exact grayBit_odd_even_zero n
          | succ a =>
              have ha : a ≠ i := by omega
              rw [hm, show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
                grayBit_odd_succ, grayBit_even_succ]
              exact hother a ha
  obtain ⟨i, hi, hother⟩ := hall k
  have hbound : i < d := by
    by_contra h
    have hki : grayBit k i = false := by
      change (Nat.xor k (k / 2)).testBit i = false
      apply Nat.testBit_lt_two_pow
      rw [Nat.xor_eq]
      exact lt_of_lt_of_le (Nat.xor_lt_two_pow (Nat.lt_of_succ_lt hk)
        (Nat.lt_of_le_of_lt (Nat.div_le_self k 2) (Nat.lt_of_succ_lt hk)))
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_of_not_gt h))
    have hsi : grayBit (k + 1) i = false := by
      change (Nat.xor (k + 1) ((k + 1) / 2)).testBit i = false
      apply Nat.testBit_lt_two_pow
      rw [Nat.xor_eq]
      exact lt_of_lt_of_le (Nat.xor_lt_two_pow hk
        (Nat.lt_of_le_of_lt (Nat.div_le_self (k + 1) 2) hk))
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_of_not_gt h))
    exact hi (hki.trans hsi.symm)
  refine ⟨⟨i, hbound⟩, hi, ?_⟩
  intro j hj
  exact hother j.val (by intro heq; apply hj; exact Fin.ext heq)

end Causalean.Mathlib.Topology.SpaceFillingCurve
