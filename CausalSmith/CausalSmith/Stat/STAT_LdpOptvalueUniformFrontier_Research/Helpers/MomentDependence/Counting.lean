module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PrivateMoments
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Finite subset-overlap counting

Inclusion probabilities and a finite union bound control squared private moments.
-/

public section

open scoped BigOperators

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [positive block size](hyp:hm), [the stated hkm condition](hyp:hkm), and [the stated hv condition](hyp:hv). [The inclusion probability of a specified subset is bounded by the paper's sampling-without-replacement factor, including the empty subset](goal). -/
-- @node: choose_inclusion_le
lemma choose_inclusion_le (m k v : ℕ) (hm : 0 < m) (hkm : 2 * k ≤ m) (hv : v ≤ k) :
    (Nat.choose (m - v) (k - v) : ℝ) ≤ (Nat.choose m k : ℝ) * (2 * k/ (m : ℝ))^v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hvk : v < k := by omega
    have hvm : v < m := by omega
    have hrec := Nat.add_one_mul_choose_eq (m - v- 1) (k - v- 1)
    have hmshift : m - v- 1 + 1 = m - v := by omega
    have hkshift : k - v- 1 + 1 = k - v := by omega
    rw [hmshift, hkshift] at hrec
    have hrecR : ((m - v : ℕ) : ℝ) * (Nat.choose (m-(v + 1)) (k-(v + 1)) : ℝ) =
        (Nat.choose (m - v) (k - v) : ℝ) * ((k - v : ℕ) : ℝ) := by
      exact_mod_cast hrec
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmvR : (0 : ℝ) < (m - v : ℕ) := by exact_mod_cast (by omega : 0 < m - v)
    have hvR : (v : ℝ) ≤ k := by exact_mod_cast hvk.le
    have hkmR : 2 * (k : ℝ) ≤ m := by exact_mod_cast hkm
    have hfrac : ((k - v : ℕ) : ℝ) / ((m - v : ℕ) : ℝ) ≤ 2 * k/ (m : ℝ) := by
      rw [div_le_div_iff₀ hmvR hmR]
      rw [Nat.cast_sub hvk.le, Nat.cast_sub hvm.le]
      nlinarith
    have heq : (Nat.choose (m-(v + 1)) (k-(v + 1)) : ℝ) =
        (Nat.choose (m - v) (k - v) : ℝ) * (((k - v : ℕ) : ℝ) / ((m - v : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      apply (eq_div_iff hmvR.ne').mpr
      nlinarith [hrecR]
    rw [heq]
    calc
      _ ≤ ((Nat.choose m k : ℝ) * (2 * k/ (m : ℝ))^v) * (2 * k/ (m : ℝ)) :=
        mul_le_mul (ih (by omega)) hfrac (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- Assume [the stated hm condition](hyp:hm), [the stated hkm condition](hyp:hkm), [the stated hs condition](hyp:hHs), and [the stated hk condition](hyp:hHk). [A specified subset is contained in at most the inclusion-factor fraction of all uniformly weighted subsets of the required size](goal). -/
-- @node: sum_subset_indicator_le
lemma sum_subset_indicator_le {α : Type*} [DecidableEq α] (s H : Finset α)
    (k : ℕ) (hm : 0 < s.card) (hkm : 2 * k ≤ s.card)
    (hHs : H ⊆ s) (hHk : H.card ≤ k) :
    (∑ K ∈ s.powersetCard k, if H ⊆ K then (1 : ℝ) else 0) ≤
      (Nat.choose s.card k : ℝ) * (2 * k/ (s.card : ℝ))^H.card := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_filter_powersetCard_subset H s k hHs hHk]
  exact choose_inclusion_le s.card k H.card hm hkm hHk

/-- Assume [nonnegative amplitude](hyp:ha) and [a nonnegative bias bound](hyp:hB). [The term for an exact intersection is dominated by the sum of all included subsets; this is the finite union bound with nonnegative moment weights](goal). -/
-- @node: overlap_term_le_subset_sum
lemma overlap_term_le_subset_sum {α : Type*} [DecidableEq α] (J K : Finset α)
    (k : ℕ) (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    B^(J ∩ K).card * a^(k - (J ∩ K).card) ≤
      ∑ H ∈ J.powerset, if H ⊆ K then B^H.card * a^(k - H.card) else 0 := by
  have h := Finset.single_le_sum
    (s := J.powerset)
    (f := fun H => if H ⊆ K then B^H.card * a^(k - H.card) else 0)
    (a := J ∩ K) (by intro H _; split_ifs <;> positivity)
    (Finset.mem_powerset.mpr Finset.inter_subset_left)
  simpa only [if_pos Finset.inter_subset_right] using h

/-- Assume [the stated hm condition](hyp:hm), [the stated hkm condition](hyp:hkm), [the stated js condition](hyp:hJs), [the stated j condition](hyp:hJ), [nonnegative amplitude](hyp:ha), and [a nonnegative bias bound](hyp:hB). [Summing the union bound over a uniform subset and applying the binomial expansion gives the second-moment row bound](goal). -/
-- @node: overlap_row_sum_le
lemma overlap_row_sum_le {α : Type*} [DecidableEq α] (s J : Finset α)
    (k : ℕ) (hm : 0 < s.card) (hkm : 2 * k ≤ s.card) (hJs : J ⊆ s)
    (hJ : J.card = k) (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    (∑ K ∈ s.powersetCard k, B^(J ∩ K).card * a^(k - (J ∩ K).card)) ≤
      (Nat.choose s.card k : ℝ) * (a + 2 * k * B/ (s.card : ℝ))^k := by
  classical
  calc
    _ ≤ ∑ K ∈ s.powersetCard k,
        ∑ H ∈ J.powerset, if H ⊆ K then B^H.card * a^(k - H.card) else 0 :=
      Finset.sum_le_sum (fun K _ => overlap_term_le_subset_sum J K k a B ha hB)
    _ = ∑ H ∈ J.powerset, (B^H.card * a^(k - H.card)) *
        ∑ K ∈ s.powersetCard k, if H ⊆ K then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro H _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro K _
      split_ifs <;> simp
    _ ≤ ∑ H ∈ J.powerset, (B^H.card * a^(k - H.card)) *
        ((Nat.choose s.card k : ℝ) * (2 * k/ (s.card : ℝ))^H.card) := by
      apply Finset.sum_le_sum
      intro H hH
      have hHJ := Finset.mem_powerset.mp hH
      exact mul_le_mul_of_nonneg_left
        (sum_subset_indicator_le s H k hm hkm (hHJ.trans hJs)
          (hJ ▸ Finset.card_le_card hHJ)) (by positivity)
    _ = (Nat.choose s.card k : ℝ) * (a + 2 * k * B/ (s.card : ℝ))^k := by
      have hterm : ∀ H : Finset α,
          (B^H.card * a^(k - H.card)) *
            ((Nat.choose s.card k : ℝ) * (2 * k/ (s.card : ℝ))^H.card) =
          (Nat.choose s.card k : ℝ) *
            ((2 * k * B/ (s.card : ℝ))^H.card * a^(k - H.card)) := by
        intro H
        rw [show 2 * (k : ℝ) * B/ (s.card : ℝ) = B * (2 * k/ (s.card : ℝ)) by ring, mul_pow]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum, ← hJ, Finset.sum_pow_mul_eq_add_pow, add_comm]

/-- Assume [the stated hm condition](hyp:hm), [the stated hkm condition](hyp:hkm), [nonnegative amplitude](hyp:ha), and [a nonnegative bias bound](hyp:hB). [Averaging the row bound twice cancels both subset-count normalizers](goal). -/
-- @node: overlap_average_le
lemma overlap_average_le {α : Type*} [DecidableEq α] (s : Finset α)
    (k : ℕ) (hm : 0 < s.card) (hkm : 2 * k ≤ s.card)
    (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    ((Nat.choose s.card k : ℝ)⁻¹)^2 *
      (∑ J ∈ s.powersetCard k, ∑ K ∈ s.powersetCard k,
        B^(J ∩ K).card * a^(k - (J ∩ K).card)) ≤
      (a + 2 * k * B/ (s.card : ℝ))^k := by
  have hc : (Nat.choose s.card k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ s.card)).ne'
  calc
    _ ≤ ((Nat.choose s.card k : ℝ)⁻¹)^2 *
        ∑ J ∈ s.powersetCard k,
          (Nat.choose s.card k : ℝ) * (a + 2 * k * B/ (s.card : ℝ))^k := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro J hJ
      exact overlap_row_sum_le s J k hm hkm (Finset.mem_powersetCard.mp hJ).1
        (Finset.mem_powersetCard.mp hJ).2 a B ha hB
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
      field_simp

end CausalSmith.Stat.LdpOptvalueUniformFrontier
