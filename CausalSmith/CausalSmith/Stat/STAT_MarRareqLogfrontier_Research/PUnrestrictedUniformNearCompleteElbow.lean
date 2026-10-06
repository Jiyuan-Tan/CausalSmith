module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.PUnrestrictedNearCompletePhaseBoundary
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedLargeAlphabetDeficitLower
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.IsBounded

/-! The near-complete elbow is necessary and sufficient for parametric point risk
uniformly over every alphabet size. Supremum bounds use an upper bound and witnesses
above every strictly smaller threshold. -/

public section
open Filter Set
namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: prop:unrestricted-uniform-near-complete-elbow
/-- Given [the specified inputs and assumptions](hyp:q,hq), [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_uniform_near_complete_elbow
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n ∧ q n ≤ 1) :
    (∀ n : ℕ, 1 ≤ n →
      (∀ d : ℕ, 1 ≤ d →
        (n : ℝ) * unrestrictedMinimaxRisk n d (q n) ≤ 4 + n * (1 - q n) ^ 2) ∧
      (∀ b : ℝ, b < (1 / 2048 : ℝ) * (1 + n * (1 - q n) ^ 2) →
        ∃ d : ℕ, 1 ≤ d ∧
          b < (n : ℝ) * unrestrictedMinimaxRisk n d (q n))) ∧
    ((∃ (M : ℝ) (n₀ : ℕ), 0 ≤ M ∧ ∀ n, n₀ ≤ n →
        1 - q n ≤ M / Real.sqrt (n : ℝ)) ↔
      (∃ (D : ℝ) (n₀ : ℕ), ∀ n, n₀ ≤ n → ∀ d, 1 ≤ d →
        unrestrictedMinimaxRisk n d (q n) ≤ D / n)) ∧
    (∀ n d : ℕ, 1 ≤ n → 1 ≤ d →
      1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n d (q n)) ∧
    (¬ BddAbove (Set.range (fun n : ℕ => Real.sqrt (n : ℝ) * (1 - q n))) →
      ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
        C < (n : ℝ) * unrestrictedMinimaxRisk n (1024 * n ^ 2) (q n)) := by
  obtain ⟨C₀, hC₀, hmix, henv⟩ := unrestricted_near_complete_arrival_envelope
  have upper (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
      unrestrictedMinimaxRisk n d (q n) ≤ 4 / (n : ℝ) + (1 - q n) ^ 2 := by
    exact (henv n d (q n) hn hd (hq n).1 (hq n).2).2.1.trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have large (n : ℕ) (hn : 1 ≤ n) :
      (1 / 2048 : ℝ) * (1 + n * (1 - q n) ^ 2) ≤
        (n : ℝ) * unrestrictedMinimaxRisk n (1024 * n ^ 2) (q n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hl := (unrestricted_large_alphabet_deficit_lower n (1024 * n ^ 2)
      (q n) hn le_rfl (hq n).1 (hq n).2).2.2.1
    have hm := mul_le_mul_of_nonneg_left hl hnR.le
    have heq : (n : ℝ) * ((1 / 2048 : ℝ) * ((n : ℝ)⁻¹ + (1 - q n) ^ 2)) =
        (1 / 2048 : ℝ) * (1 + n * (1 - q n) ^ 2) := by
      field_simp
    rwa [heq] at hm
  have alphabet (n : ℕ) (hn : 1 ≤ n) : 1 ≤ 1024 * n ^ 2 := by
    have : 1 ≤ n ^ 2 := one_le_pow₀ hn
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · intro d hd
      have h := mul_le_mul_of_nonneg_left (upper n d hn hd) hnR.le
      have heq : (n : ℝ) * (4 / (n : ℝ) + (1 - q n) ^ 2) =
          4 + n * (1 - q n) ^ 2 := by
        field_simp
      rwa [heq] at h
    · intro b hb
      exact ⟨1024 * n ^ 2, alphabet n hn, hb.trans_le (large n hn)⟩
  · constructor
    · rintro ⟨M, n₀, hM, hdef⟩
      refine ⟨4 + M ^ 2, max n₀ 1, ?_⟩
      intro n hn d hd
      have hn1 : 1 ≤ n := (le_max_right n₀ 1).trans hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
      have hscaled := (le_div_iff₀ hsqrt).1
        (hdef n ((le_max_left n₀ 1).trans hn))
      have hnon : 0 ≤ (1 - q n) * Real.sqrt (n : ℝ) :=
        mul_nonneg (sub_nonneg.2 (hq n).2) hsqrt.le
      have hsquare : ((1 - q n) * Real.sqrt (n : ℝ)) ^ 2 ≤ M ^ 2 := by
        nlinarith
      have hbudget : (1 - q n) ^ 2 ≤ M ^ 2 / (n : ℝ) := by
        apply (le_div_iff₀ hnR).2
        simpa only [mul_pow, Real.sq_sqrt hnR.le] using hsquare
      calc
        unrestrictedMinimaxRisk n d (q n) ≤ 4 / (n : ℝ) + (1 - q n) ^ 2 :=
          upper n d hn1 hd
        _ ≤ 4 / (n : ℝ) + M ^ 2 / (n : ℝ) := add_le_add_right hbudget _
        _ = (4 + M ^ 2) / (n : ℝ) := by rw [add_div]
    · rintro ⟨D, n₀, hD⟩
      refine ⟨Real.sqrt (max (2048 * D) 0), max n₀ 1, Real.sqrt_nonneg _, ?_⟩
      intro n hn
      have hn1 : 1 ≤ n := (le_max_right n₀ 1).trans hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
      have hbound := mul_le_mul_of_nonneg_left
        (hD n ((le_max_left n₀ 1).trans hn) _ (alphabet n hn1)) hnR.le
      have hcancel : (n : ℝ) * (D / (n : ℝ)) = D := by
        field_simp
      rw [hcancel] at hbound
      have hl := (large n hn1).trans hbound
      have hsq : (Real.sqrt (n : ℝ) * (1 - q n)) ^ 2 = n * (1 - q n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnR.le]
      have hM : (Real.sqrt (max (2048 * D) 0)) ^ 2 = max (2048 * D) 0 :=
        Real.sq_sqrt (le_max_right _ _)
      have hscaled : (1 - q n) * Real.sqrt (n : ℝ) ≤
          Real.sqrt (max (2048 * D) 0) := by
        have := le_max_left (2048 * D) (0 : ℝ)
        have := Real.sqrt_nonneg (max (2048 * D) 0)
        nlinarith [sq_nonneg (Real.sqrt (n : ℝ) * (1 - q n) -
          Real.sqrt (max (2048 * D) 0))]
      exact (le_div_iff₀ hsqrt).2 hscaled
  · intro n d hn hd
    exact (henv n d (q n) hn hd (hq n).1 (hq n).2).1
  · intro hunbounded C
    by_contra hnot
    have hevent : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * unrestrictedMinimaxRisk n (1024 * n ^ 2) (q n) ≤ C := by
      simpa only [Filter.Frequently, not_not, not_lt] using hnot
    apply hunbounded
    apply Filter.IsBoundedUnder.bddAbove_range
    apply Filter.isBoundedUnder_of_eventually_le
      (a := Real.sqrt (max (2048 * C) 0))
    filter_upwards [hevent, eventually_ge_atTop (1 : ℕ)] with n hbound hn
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hl := (large n hn).trans hbound
    have hsq : (Real.sqrt (n : ℝ) * (1 - q n)) ^ 2 = n * (1 - q n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnR]
    have hM : (Real.sqrt (max (2048 * C) 0)) ^ 2 = max (2048 * C) 0 :=
      Real.sq_sqrt (le_max_right _ _)
    have := le_max_left (2048 * C) (0 : ℝ)
    have := Real.sqrt_nonneg (max (2048 * C) 0)
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) * (1 - q n) -
      Real.sqrt (max (2048 * C) 0))]

end CausalSmith.Stat.MarRareqLogfrontier
