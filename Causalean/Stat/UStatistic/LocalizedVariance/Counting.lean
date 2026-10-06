module
public import Causalean.Stat.UStatistic.LocalizedVariance.Basic

/-!
# Counting unordered pair overlaps

This module counts unordered index pairs and the ordered pairs of such pairs that are
identical, share exactly one index, or are disjoint. The counts are purely finite and
independent of the observation space.
-/

public section

namespace Causalean.Stat.UStatistic.LocalizedVariance

/-- A [sample size](hyp:n) has [exactly its binomial number of unordered pairs](goal). -/
theorem card_pairIndices (n : ℕ) : (pairIndices n).card = n.choose 2 := by
  simpa [pairIndices] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

/-- A [sample size](hyp:n) has [one ordered identical-pair configuration for each unordered
pair](goal). -/
theorem card_identical_pair_configurations (n : ℕ) :
    ((pairIndices n).product (pairIndices n) |>.filter fun pq => pq.1 = pq.2).card =
      n.choose 2 := by
  change ((pairIndices n ×ˢ pairIndices n).filter (fun pq => pq.1 = pq.2)).card = _
  rw [← Finset.diag_eq_filter, Finset.diag_card, card_pairIndices]

/-- Given [at least two observations](hyp:hn) and [an unordered pair](hyp:hp), [exactly twice
the number of remaining vertices gives a distinct pair sharing an endpoint](goal). -/
theorem card_pairs_sharing_fixed_pair {n : ℕ} (hn : 2 ≤ n)
    {p : Fin n × Fin n} (hp : p ∈ pairIndices n) :
    ((pairIndices n).filter fun q => p ≠ q ∧ SharesIndex p q).card =
      2 * (n - 2) := by
  -- Partition the filtered pairs by which endpoint of p they contain. The
  -- parts are disjoint because q ≠ p; each is indexed by the n - 2 remaining
  -- vertices. An order-free Finset erase of the two endpoints is convenient.
  have hcount (a b : Fin n) (hab : a ≠ b) :
      ((pairIndices n).filter (fun q => q ≠ (if a < b then (a,b) else (b,a)) ∧
        (q.1 = a ∨ q.2 = a))).card = n - 2 := by
    let t := ((Finset.univ : Finset (Fin n)).erase a).erase b
    let f : Fin n → Fin n × Fin n := fun x => if a < x then (a,x) else (x,a)
    have heq : (pairIndices n).filter (fun q =>
        q ≠ (if a < b then (a,b) else (b,a)) ∧ (q.1 = a ∨ q.2 = a)) =
        t.image f := by
      ext q
      simp only [Finset.mem_filter, pairIndices, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨hord, hne, hshare⟩
        rcases hshare with h | h
        · refine ⟨q.2, ?_, ?_⟩
          · grind
          · dsimp [f]; split_ifs <;> grind
        · refine ⟨q.1, ?_, ?_⟩
          · grind
          · dsimp [f]; split_ifs <;> grind
      · rintro ⟨x, hx, hqx⟩
        rw [← hqx]
        have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
        dsimp [f]
        split_ifs <;> grind
    have hinj : Set.InjOn f ↑t := by
      intro x hx y hy h
      have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hya : y ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
      dsimp [f] at h
      split_ifs at h <;> grind
    rw [heq, Finset.card_image_of_injOn hinj]
    have hb : b ∈ (Finset.univ : Finset (Fin n)).erase a := by simp [hab.symm]
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hpord : p.1 < p.2 := by simpa [pairIndices] using hp
  let A := (pairIndices n).filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.1)
  let B := (pairIndices n).filter fun q => q ≠ p ∧ (q.1 = p.2 ∨ q.2 = p.2)
  have hcover :
      ((pairIndices n).filter fun q => p ≠ q ∧ SharesIndex p q) = A ∪ B := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    dsimp [A, B]
    simp only [Finset.mem_filter]
    unfold SharesIndex
    grind
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro q hA hB
    have hqord : q.1 < q.2 := by
      have hq : q ∈ pairIndices n := (Finset.mem_filter.mp hA).1
      simpa [pairIndices] using hq
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    grind
  have hA : A.card = n - 2 := by
    simpa [A, hpord] using hcount p.1 p.2 (ne_of_lt hpord)
  have hB : B.card = n - 2 := by
    have hnot : ¬ p.2 < p.1 := not_lt_of_ge (le_of_lt hpord)
    simpa [B, hnot] using hcount p.2 p.1 (Ne.symm (ne_of_lt hpord))
  rw [hcover, Finset.card_union_of_disjoint hdisj, hA, hB]
  omega

/-- Given [an unordered pair](hyp:hp), [the pairs using neither endpoint have the binomial
remaining-vertex count](goal). -/
theorem card_pairs_disjoint_fixed_pair {n : ℕ}
    {p : Fin n × Fin n} (hp : p ∈ pairIndices n) :
    ((pairIndices n).filter fun q => ¬ SharesIndex p q).card =
      (n - 2).choose 2 := by
  let s := ((Finset.univ : Finset (Fin n)).erase p.1).erase p.2
  have hset : (pairIndices n).filter (fun q => ¬ SharesIndex p q) =
      (s ×ˢ s).filter (fun q => q.1 < q.2) := by
    ext q
    simp [s, pairIndices, SharesIndex, Finset.mem_product, and_comm, and_assoc]
    grind
  have hpord : p.1 < p.2 := by simpa [pairIndices] using hp
  have hp2 : p.2 ∈ (Finset.univ : Finset (Fin n)).erase p.1 := by
    simp [ne_of_gt hpord]
  have hs : s.card = n - 2 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hp2, Finset.card_erase_of_mem (Finset.mem_univ p.1)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  rw [hset, Finset.card_product_filter_lt, hs]

/-- A [sample size](hyp:n) satisfies [the pair-then-disjoint-pair counting identity](goal),
which counts every four-element subset through its six ordered pairings. -/
theorem choose_two_mul_choose_sub_two (n : ℕ) :
    n.choose 2 * (n - 2).choose 2 = 6 * n.choose 4 := by
  have h := Nat.choose_mul (n := n) (k := 4) (s := 2) (by omega)
  have hchoose : Nat.choose 4 2 = 6 := by decide
  rw [hchoose] at h
  simpa [Nat.mul_comm] using h.symm

/-- Given [at least two observations](hyp:hn), [the ordered count of distinct pair pairs
sharing one index has the stated binomial form](goal). -/
theorem card_shared_pair_configurations {n : ℕ} (hn : 2 ≤ n) :
    ((pairIndices n).product (pairIndices n) |>.filter fun
        (pq : (Fin n × Fin n) × (Fin n × Fin n)) =>
      pq.1 ≠ pq.2 ∧ SharesIndex pq.1 pq.2).card =
        2 * (n.choose 2) * (n - 2) := by
  -- Sum the fixed-pair fiber count `card_pairs_sharing_fixed_pair` over
  -- `pairIndices`; then use `card_pairIndices`.
  classical
  let s := pairIndices n
  have hfiber (p : Fin n × Fin n) (hp : p ∈ s) :
      (((s ×ˢ s).filter (fun pq => pq.1 ≠ pq.2 ∧ SharesIndex pq.1 pq.2)).filter
        (fun pq => pq.1 = p)).card = 2 * (n - 2) := by
    have heq :
        ((s ×ˢ s).filter (fun pq => pq.1 ≠ pq.2 ∧ SharesIndex pq.1 pq.2)).filter
          (fun pq => pq.1 = p) =
        {p} ×ˢ (s.filter fun q => p ≠ q ∧ SharesIndex p q) := by
      ext pq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hpq, hqq⟩, hne, hshare⟩, hfst⟩
        subst p
        exact ⟨rfl, hqq, hne, hshare⟩
      · rintro ⟨hfst, hqq, hne, hshare⟩
        subst p
        exact ⟨⟨⟨hp, hqq⟩, hne, hshare⟩, rfl⟩
    rw [heq, Finset.card_product]
    simpa [s] using card_pairs_sharing_fixed_pair hn hp
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (s ×ˢ s).filter (fun pq => pq.1 ≠ pq.2 ∧ SharesIndex pq.1 pq.2))
    (t := s) (f := Prod.fst) (by
      intro pq hpq
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1)
  rw [Finset.sum_const_nat hfiber] at hsum
  simpa [s, card_pairIndices, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- A [sample size](hyp:n) has [six ordered disjoint-pair configurations per four-element
subset](goal). -/
theorem card_disjoint_pair_configurations (n : ℕ) :
    ((pairIndices n).product (pairIndices n) |>.filter fun
        (pq : (Fin n × Fin n) × (Fin n × Fin n)) =>
      ¬ SharesIndex pq.1 pq.2).card = 6 * n.choose 4 := by
  -- Sum `card_pairs_disjoint_fixed_pair` over first pairs, rewrite with
  -- `card_pairIndices`, then use `choose_two_mul_choose_sub_two`.
  classical
  let s := pairIndices n
  have hfiber (p : Fin n × Fin n) (hp : p ∈ s) :
      (((s ×ˢ s).filter (fun pq => ¬ SharesIndex pq.1 pq.2)).filter
        (fun pq => pq.1 = p)).card = (n - 2).choose 2 := by
    have heq :
        ((s ×ˢ s).filter (fun pq => ¬ SharesIndex pq.1 pq.2)).filter
          (fun pq => pq.1 = p) =
        {p} ×ˢ (s.filter fun q => ¬ SharesIndex p q) := by
      ext pq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hpq, hqq⟩, hdis⟩, hfst⟩
        subst p
        exact ⟨rfl, hqq, hdis⟩
      · rintro ⟨hfst, hqq, hdis⟩
        subst p
        exact ⟨⟨⟨hp, hqq⟩, hdis⟩, rfl⟩
    rw [heq, Finset.card_product]
    simpa [s] using card_pairs_disjoint_fixed_pair hp
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (s ×ˢ s).filter (fun pq => ¬ SharesIndex pq.1 pq.2))
    (t := s) (f := Prod.fst) (by
      intro pq hpq
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1)
  rw [Finset.sum_const_nat hfiber] at hsum
  have hcard :
      ((pairIndices n ×ˢ pairIndices n).filter
        (fun pq => ¬ SharesIndex pq.1 pq.2)).card =
        n.choose 2 * (n - 2).choose 2 := by
    simpa [s, card_pairIndices] using hsum
  exact hcard.trans (choose_two_mul_choose_sub_two n)

/-- Given [at least two observations](hyp:hn) and [nonnegative identical, pair, and row
scales](hyp:ha,hp,hr), [the normalized identical and shared pair counts are bounded by the
two-scale constant-sixteen expression](goal). -/
theorem normalized_pair_counts_le {n : ℕ} (hn : 2 ≤ n)
    {a p r : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    ((n.choose 2 : ℝ)⁻¹) ^ 2 *
        ((n.choose 2 : ℝ) * (a * p) +
          ((2 * (n.choose 2) * (n - 2) : ℕ) : ℝ) * (2 * a * r)) ≤
      16 * a * (r / (n : ℝ) + p / (n : ℝ) ^ 2) := by
  -- Rewrite `n.choose 2` with `Nat.choose_two_right`; `hn` makes its
  -- denominator positive. Separate the coefficients of `p` and `r`, then
  -- use `n - 1 ≥ n / 2` and `n - 2 ≤ n`.
  let q : ℝ := n.choose 2
  let N : ℝ := n
  let t : ℝ := n - 2
  have hN : 0 < N := by
    change 0 < (n : ℝ)
    exact_mod_cast (by omega : 0 < n)
  have hNtwo : 2 ≤ N := by
    change 2 ≤ (n : ℝ)
    exact_mod_cast hn
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Nat.choose_pos hn)
  have hchoose : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
  have hqeq : q = N * (N - 1) / 2 := by
    have hcast := Nat.cast_choose_two ℝ n
    rw [hchoose] at hcast
    dsimp [q, N]
    rw [hchoose]
    exact hcast
  have hqbound : N ^ 2 ≤ 4 * q := by nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hNtwo)]
  have ht : t ≤ N := by
    dsimp [t, N]
    exact_mod_cast (Nat.sub_le n 2)
  have hpcoef : 1 / q ≤ 16 / N ^ 2 := by
    apply (div_le_div_iff₀ hq (sq_pos_of_pos hN)).2
    nlinarith
  have hrcoef : 4 * t / q ≤ 16 / N := by
    apply (div_le_div_iff₀ hq hN).2
    nlinarith [mul_le_mul_of_nonneg_right ht hN.le]
  have hap : 0 ≤ a * p := mul_nonneg ha hp
  have har : 0 ≤ a * r := mul_nonneg ha hr
  have hbound := add_le_add
    (mul_le_mul_of_nonneg_right hpcoef hap)
    (mul_le_mul_of_nonneg_right hrcoef har)
  dsimp [q, N, t] at hbound
  have hqne : (n.choose 2 : ℝ) ≠ 0 := ne_of_gt hq
  calc
    _ = 1 / (n.choose 2 : ℝ) * (a * p) +
        4 * ((n - 2 : ℕ) : ℝ) / (n.choose 2 : ℝ) * (a * r) := by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          field_simp [hqne]
          ring
    _ ≤ 16 / (n : ℝ) ^ 2 * (a * p) +
        16 / (n : ℝ) * (a * r) := by
          simpa [Nat.cast_sub hn] using hbound
    _ = _ := by ring

end Causalean.Stat.UStatistic.LocalizedVariance
