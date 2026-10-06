module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleBinomial

/-!
# Centered inverse-risk coefficient bounds
-/

public section

open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

lemma binomial_shifted_inverse_sum_le (m : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j * ((j : ℝ) + 1)⁻¹) ≤
      1 / (((m + 1 : ℕ) : ℝ) * p) := by
  let d : ℝ := ((m + 1 : ℕ) : ℝ) * p
  let S : ℝ := ∑ j ∈ Finset.range (m + 1),
    binomialWeight m p j * ((j : ℝ) + 1)⁻¹
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hd : 0 < d := by dsimp [d]; positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      d * (binomialWeight m p j * ((j : ℝ) + 1)⁻¹) =
        (Nat.choose (m + 1) (j + 1) : ℝ) * p ^ (j + 1) *
          (1 - p) ^ ((m + 1) - (j + 1)) := by
    have hsub : (m + 1) - (j + 1) = m - j := by omega
    have hc : (((m + 1 : ℕ) : ℝ) * (Nat.choose m j : ℝ)) =
        (Nat.choose (m + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    dsimp [d]
    rw [binomialWeight, hsub, pow_succ]
    field_simp
    rw [hc]
    push_cast
    ring
  have hid : d * S = 1 - (1 - p) ^ (m + 1) := by
    dsimp [S]
    rw [Finset.mul_sum]
    calc
      _ = ∑ j ∈ Finset.range (m + 1),
          p ^ (j + 1) * (1 - p) ^ ((m + 1) - (j + 1)) *
            (Nat.choose (m + 1) (j + 1) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hterm j hj]
        ring
      _ = (p + (1 - p)) ^ (m + 1) - (1 - p) ^ (m + 1) := by
        rw [add_pow]
        rw [Finset.sum_range_succ' (fun k =>
          p ^ k * (1 - p) ^ ((m + 1) - k) *
            (Nat.choose (m + 1) k : ℝ)) (m + 1)]
        simp
      _ = 1 - (1 - p) ^ (m + 1) := by ring
  apply (le_div_iff₀ hd).2
  rw [mul_comm, hid]
  nlinarith [pow_nonneg hq (m + 1)]

lemma binomial_shifted_two_inverse_sum_le (m : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) ≤
      1 / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * p ^ 2) := by
  let d : ℝ := ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * p ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      d * (binomialWeight m p j *
        (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) =
      binomialWeight (m + 2) p (j + 2) := by
    have hsub : (m + 2) - (j + 2) = m - j := by omega
    have hc1 := Nat.add_one_mul_choose_eq m j
    have hc2 : (m + 2) * Nat.choose (m + 1) (j + 1) =
        Nat.choose (m + 2) (j + 2) * (j + 2) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_one_mul_choose_eq (m + 1) (j + 1)
    have hc : ((m + 1) * (m + 2) * Nat.choose m j : ℕ) =
        Nat.choose (m + 2) (j + 2) * ((j + 1) * (j + 2)) := by
      calc
        _ = (m + 2) * ((m + 1) * Nat.choose m j) := by ring
        _ = (m + 2) * (Nat.choose (m + 1) (j + 1) * (j + 1)) := by rw [hc1]
        _ = ((m + 2) * Nat.choose (m + 1) (j + 1)) * (j + 1) := by ring
        _ = _ := by rw [hc2]; ring
    have hcR : (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        (Nat.choose m j : ℝ)) =
        (Nat.choose (m + 2) (j + 2) : ℝ) *
          (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by exact_mod_cast hc
    dsimp [d]
    rw [binomialWeight, binomialWeight, hsub, pow_add]
    field_simp
    rw [hcR]
    ring
  apply (le_div_iff₀ hd).2
  rw [mul_comm]
  rw [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range (m + 1), binomialWeight (m + 2) p (j + 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j hj
    _ ≤ ∑ j ∈ Finset.range (m + 3), binomialWeight (m + 2) p j := by
      rw [← Finset.sum_image (s := Finset.range (m + 1))
        (g := fun j : ℕ => j + 2) (f := binomialWeight (m + 2) p) (by
          intro i hi j hj hij
          exact Nat.add_right_cancel hij)]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
        obtain ⟨i, hi, rfl⟩ := hj
        omega
      · intro j hj hnot
        unfold binomialWeight
        positivity
    _ = 1 := by
      rw [show ∑ j ∈ Finset.range (m + 3), binomialWeight (m + 2) p j =
          (p + (1 - p)) ^ (m + 2) by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro j hj
        unfold binomialWeight
        ring]
      simp

lemma binomial_first_moment (m : ℕ) (p : ℝ) :
    (∑ t ∈ Finset.range (m + 1), binomialWeight m p t * (t : ℝ)) =
      (m : ℝ) * p := by
  by_cases hm : m = 0
  · subst m
    simp [binomialWeight]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    calc
      _ = ∑ j ∈ Finset.range m,
          (m : ℝ) * p * ((Nat.choose (m - 1) j : ℝ) *
            p ^ j * (1 - p) ^ ((m - 1) - j)) := by
        rw [Finset.sum_range_succ' (f := fun t =>
          binomialWeight m p t * (t : ℝ))]
        simp only [Nat.cast_zero, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hchoose : (Nat.choose m (j + 1) : ℝ) * (j + 1 : ℕ) =
            (m : ℝ) * (Nat.choose (m - 1) j : ℝ) := by
          rw [show m = (m - 1) + 1 by omega]
          exact_mod_cast (Nat.add_one_mul_choose_eq (m - 1) j).symm
        have hsub : m - (j + 1) = (m - 1) - j := by omega
        rw [binomialWeight, hsub, pow_succ]
        push_cast
        rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by norm_num]
        calc
          _ = ((Nat.choose m (j + 1) : ℝ) * (j + 1 : ℕ)) * p *
                (p ^ j * (1 - p) ^ (m - 1 - j)) := by ring
          _ = _ := by rw [hchoose]; ring
      _ = (m : ℝ) * p * ∑ j ∈ Finset.range m,
          (Nat.choose (m - 1) j : ℝ) * p ^ j *
            (1 - p) ^ ((m - 1) - j) := by rw [Finset.mul_sum]
      _ = (m : ℝ) * p := by
        rw [show ∑ j ∈ Finset.range m, (Nat.choose (m - 1) j : ℝ) *
            p ^ j * (1 - p) ^ ((m - 1) - j) =
            (p + (1 - p)) ^ (m - 1) by
          rw [show m = (m - 1) + 1 by omega, add_pow]
          apply Finset.sum_congr rfl
          intro j hj
          ring]
        ring

lemma binomial_empty_probability_le (m : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (1 - p) ^ m ≤ 1 / (((m + 1 : ℕ) : ℝ) * p) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsum : ((m + 1 : ℕ) : ℝ) * (1 - p) ^ m ≤
      ∑ k ∈ Finset.range (m + 1), (1 - p) ^ k := by
    calc
      _ = ∑ k ∈ Finset.range (m + 1), (1 - p) ^ m := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_of_le_one hq (by linarith)
          (by simpa using Finset.mem_range.mp hk)
  have hid := geom_sum_mul_neg (1 - p) (m + 1)
  have hbound : ((m + 1 : ℕ) : ℝ) * (1 - p) ^ m * p ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hsum hp.le
    nlinarith [pow_nonneg hq (m + 1)]
  exact (le_div_iff₀ (mul_pos (by positivity) hp)).2 (by nlinarith)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP


open scoped BigOperators
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

lemma binomial_weight_sum_eq_one (m : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (m + 1), binomialWeight m p k) = 1 := by
  rw [show ∑ k ∈ Finset.range (m + 1), binomialWeight m p k =
      (p + (1 - p)) ^ m by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    unfold binomialWeight
    ring]
  simp

lemma binomial_positive_probability_sum (m : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (m + 1), binomialWeight m p k *
      (if 0 < k then (1 : ℝ) else 0)) = 1 - (1 - p) ^ m := by
  have hzero : (∑ k ∈ Finset.range (m + 1), binomialWeight m p k *
      (if k = 0 then (1 : ℝ) else 0)) = (1 - p) ^ m := by
    simp [binomialWeight]
  have hsplit : (∑ k ∈ Finset.range (m + 1), binomialWeight m p k) =
      (∑ k ∈ Finset.range (m + 1), binomialWeight m p k *
        (if k = 0 then (1 : ℝ) else 0)) +
      ∑ k ∈ Finset.range (m + 1), binomialWeight m p k *
        (if 0 < k then (1 : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp [hk0, Nat.pos_of_ne_zero hk0]
  rw [binomial_weight_sum_eq_one m p, hzero] at hsplit
  linarith

lemma binomial_totalized_inverse_refined_le (m : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ k ∈ Finset.range (m + 1), binomialWeight m p k *
      (if 0 < k then (k : ℝ)⁻¹ else 0)) ≤
      1 / (((m + 1 : ℕ) : ℝ) * p) +
        3 / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * p ^ 2) := by
  have hweight (k : ℕ) : 0 ≤ binomialWeight m p k := by
    unfold binomialWeight
    positivity
  calc
    _ ≤ ∑ k ∈ Finset.range (m + 1), binomialWeight m p k *
        (((k : ℝ) + 1)⁻¹ +
          3 * (((k : ℝ) + 1) * ((k : ℝ) + 2))⁻¹) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (totalized_inverse_count_le_shifted k)
        (hweight k)
    _ = (∑ k ∈ Finset.range (m + 1),
          binomialWeight m p k * ((k : ℝ) + 1)⁻¹) +
        3 * ∑ k ∈ Finset.range (m + 1),
          binomialWeight m p k *
            (((k : ℝ) + 1) * ((k : ℝ) + 2))⁻¹ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 1 / (((m + 1 : ℕ) : ℝ) * p) +
        3 * (1 / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * p ^ 2)) :=
      add_le_add (binomial_shifted_inverse_sum_le m p hp hp1)
        (mul_le_mul_of_nonneg_left
          (binomial_shifted_two_inverse_sum_le m p hp hp1) (by norm_num))
    _ = _ := by ring

/-- The risk-weighted centered zero-safe inverse-count coefficient has the
`1/n` binomial envelope needed for fixed-horizon oracle replacement. -/
lemma binomial_weighted_scaledInverse_center_sq_le (n : ℕ) (p : ℝ)
    (hn : 0 < n) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
      ((k : ℝ) / n) *
        ((if 0 < k then (n : ℝ) / k else 0) - 1 / p) ^ 2) ≤
      5 / (((n + 1 : ℕ) : ℝ) * p ^ 2) := by
  let EInv := ∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
    (if 0 < k then (k : ℝ)⁻¹ else 0)
  let Ppos := ∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
    (if 0 < k then (1 : ℝ) else 0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hEInv : EInv ≤ 1 / (((n + 1 : ℕ) : ℝ) * p) +
      3 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * p ^ 2) :=
    binomial_totalized_inverse_refined_le n p hp hp1
  have hPpos : Ppos = 1 - (1 - p) ^ n :=
    binomial_positive_probability_sum n p
  have hP0 : (1 - p) ^ n ≤ 1 / (((n + 1 : ℕ) : ℝ) * p) :=
    binomial_empty_probability_le n p hp hp1
  have hExpand : (∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
      ((k : ℝ) / n) *
        ((if 0 < k then (n : ℝ) / k else 0) - 1 / p) ^ 2) =
      (n : ℝ) * EInv - (2 / p) * Ppos + 1 / p := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
          ((if 0 < k then (n : ℝ) / k else 0) -
            (2 / p) * (if 0 < k then 1 else 0) +
            (k : ℝ) / ((n : ℝ) * p ^ 2)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show binomialWeight n p k * ((k : ℝ) / n) *
            ((if 0 < k then (n : ℝ) / k else 0) - 1 / p) ^ 2 =
            binomialWeight n p k * (((k : ℝ) / n) *
              ((if 0 < k then (n : ℝ) / k else 0) - 1 / p) ^ 2) by ring,
          weighted_scaledInverse_center_sq_eq n k p hn hp]
      _ = _ := by
        simp_rw [mul_add, mul_sub]
        rw [Finset.sum_add_distrib]
        have h1 : (∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
            (if 0 < k then (n : ℝ) / k else 0)) = (n : ℝ) * EInv := by
          dsimp [EInv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkpos : 0 < k <;> simp [hkpos, div_eq_mul_inv]
          ring
        have h2 : (∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
            ((2 / p) * (if 0 < k then (1 : ℝ) else 0))) =
            (2 / p) * Ppos := by
          dsimp [Ppos]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        have h3 : (∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
            ((k : ℝ) / ((n : ℝ) * p ^ 2))) = 1 / p := by
          rw [show (∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
              ((k : ℝ) / ((n : ℝ) * p ^ 2))) =
              (1 / ((n : ℝ) * p ^ 2)) *
                ∑ k ∈ Finset.range (n + 1),
                  binomialWeight n p k * (k : ℝ) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring,
            binomial_first_moment n p]
          field_simp
        rw [Finset.sum_sub_distrib, h1, h2, h3]
  rw [hExpand, hPpos]
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  calc
    (n : ℝ) * EInv - 2 / p * (1 - (1 - p) ^ n) + 1 / p ≤
        (n : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * p) +
          3 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * p ^ 2)) -
          2 / p * (1 - (1 - p) ^ n) + 1 / p := by
      nlinarith [mul_le_mul_of_nonneg_left hEInv hnR.le]
    _ ≤ 5 / (((n + 1 : ℕ) : ℝ) * p ^ 2) := by
      have hp0 : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp1) n
      have hnp : 0 < (((n + 1 : ℕ) : ℝ) * p) := mul_pos hn1 hp
      have hden : 0 < (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * p ^ 2) :=
        mul_pos (mul_pos hn1 hn2) hp2
      have hcancel : (n : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * p)) - 1 / p =
          -1 / (((n + 1 : ℕ) : ℝ) * p) := by
        norm_num [Nat.cast_add]
        field_simp
        ring
      have hthree : (n : ℝ) *
          (3 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * p ^ 2)) ≤
          3 / (((n + 1 : ℕ) : ℝ) * p ^ 2) := by
        have hnratio : (n : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ 1 := by
          apply (div_le_one hn2).2
          norm_num [Nat.cast_add]
        calc
          _ = ((n : ℝ) / ((n + 2 : ℕ) : ℝ)) *
              (3 / (((n + 1 : ℕ) : ℝ) * p ^ 2)) := by field_simp
          _ ≤ 1 * (3 / (((n + 1 : ℕ) : ℝ) * p ^ 2)) :=
            mul_le_mul_of_nonneg_right hnratio
              (div_nonneg (by norm_num) (mul_nonneg hn1.le hp2.le))
          _ = _ := one_mul _
      have hzero : (2 / p) * (1 - p) ^ n ≤
          2 / (((n + 1 : ℕ) : ℝ) * p ^ 2) := by
        calc
          _ ≤ (2 / p) * (1 / (((n + 1 : ℕ) : ℝ) * p)) :=
            mul_le_mul_of_nonneg_left hP0 (div_nonneg (by norm_num) hp.le)
          _ = _ := by field_simp
      have hrearr :
          (n : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * p) +
            3 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * p ^ 2)) -
            2 / p * (1 - (1 - p) ^ n) + 1 / p =
          ((n : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * p)) - 1 / p) +
            (n : ℝ) * (3 / (((n + 1 : ℕ) : ℝ) *
              ((n + 2 : ℕ) : ℝ) * p ^ 2)) +
            (2 / p) * (1 - p) ^ n := by ring
      rw [hrearr, hcancel]
      have hneg : -1 / (((n + 1 : ℕ) : ℝ) * p) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hnp.le
      calc
        -1 / (((n + 1 : ℕ) : ℝ) * p) +
            (n : ℝ) * (3 / (((n + 1 : ℕ) : ℝ) *
              ((n + 2 : ℕ) : ℝ) * p ^ 2)) +
            (2 / p) * (1 - p) ^ n ≤
            0 + 3 / (((n + 1 : ℕ) : ℝ) * p ^ 2) +
              2 / (((n + 1 : ℕ) : ℝ) * p ^ 2) :=
          add_le_add (add_le_add hneg hthree) hzero
        _ = 5 / (((n + 1 : ℕ) : ℝ) * p ^ 2) := by ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP


open MeasureTheory Set
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
