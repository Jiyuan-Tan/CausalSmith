module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.TwoSampleL1
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.LargeSample

/-! Sparse and finite-alphabet completion of the two-sample L1 lower bound. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

/-- At large alphabets the cited dense result also controls samples below
`k / log k`, by comparing with the first dense sample size. With [the specified inputs and conditions](hyp:of_gate), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_lower_large_sparse
lemma twoSampleL1_lower_large_sparse (of_gate : JHWKnownQL1LowerRegime) :
    ∃ c : ℝ, 0 < c ∧ ∃ k0 : ℕ,
      ∀ k n : ℕ, max k0 3 ≤ k → 1 ≤ n →
        (n : ℝ) < (k : ℝ) / Real.log k →
        c ≤ twoSampleL1MinimaxRisk n k := by
  obtain ⟨c, hc, k0, hbound⟩ := twoSampleL1_lower_dense_logAlphabet of_gate
  refine ⟨c / 4, by positivity, k0, ?_⟩
  intro k n hk hn hsparse
  have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hk
  have hk0 : k0 ≤ k := le_trans (le_max_left _ _) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlogpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogone : (1 : ℝ) ≤ Real.log k := by
    apply (Real.le_log_iff_exp_le hkpos).2
    have hk3r : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    exact (le_of_lt Real.exp_one_lt_three).trans hk3r
  have hlogle : Real.log k ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
  let x : ℝ := (k : ℝ) / Real.log k
  let m : ℕ := Nat.ceil x
  have hxpos : 0 < x := div_pos hkpos hlogpos
  have hxone : 1 < x := by
    dsimp [x]
    apply (lt_div_iff₀ hlogpos).2
    linarith
  have hxm : x ≤ m := Nat.le_ceil x
  have hmlt : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
  have hm2 : 2 ≤ m := by
    have : (1 : ℝ) < m := lt_of_lt_of_le hxone hxm
    exact_mod_cast this
  have hmx : (m : ℝ) ≤ 2 * x := by linarith
  have hxk : x ≤ k := by
    dsimp [x]
    apply (div_le_iff₀ hlogpos).2
    nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hlogone)]
  have hmksq : m ≤ k ^ 2 := by
    have hmr : (m : ℝ) ≤ (k : ℝ) ^ 2 := by
      nlinarith [show (3 : ℝ) ≤ k by exact_mod_cast hk3]
    exact_mod_cast hmr
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hLpos : 0 < logAlphabet k := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkpos)]
    simp
    linarith
  have hL : logAlphabet k ≤ 2 * Real.log k := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkpos)]
    simp
    linarith
  have hmlog : (m : ℝ) * Real.log k ≤ 2 * k := by
    have h := mul_le_mul_of_nonneg_right hmx hlogpos.le
    dsimp [x] at h
    field_simp at h
    nlinarith
  have hden : (m : ℝ) * logAlphabet k ≤ 4 * k := by
    nlinarith [mul_nonneg (by exact_mod_cast (by omega : 0 ≤ m) : (0 : ℝ) ≤ m)
      (sub_nonneg.mpr hL)]
  have hlogm : Real.log m ≤ 2 * Real.log k := by
    have hmr : (m : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hmksq
    calc
      Real.log m ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log hmpos hmr
      _ = 2 * Real.log k := by rw [Real.log_pow]; ring
  have hbase := hbound k m hk0 (by omega) hm2 hxm hlogm
  have hcomp : c / 4 ≤ c * k / (m * logAlphabet k) := by
    apply (le_div_iff₀ (mul_pos hmpos hLpos)).2
    nlinarith [mul_le_mul_of_nonneg_left hden (le_of_lt hc)]
  have hnm : n ≤ m := by
    have hnr : (n : ℝ) ≤ m := (le_of_lt hsparse).trans hxm
    exact_mod_cast hnr
  haveI : NeZero k := ⟨by omega⟩
  exact (hcomp.trans hbase).trans (twoSampleL1_minimax_antitone hnm)


-- @node: lem:two-sample-l1-lower
/-- The two sample l1 lower result. It proves [the stated conclusion](goal). -/
lemma two_sample_l1_lower (_of_gate : JHWKnownQL1LowerRegime) :
    ∃ c : ℝ, 0 < c ∧ ∀ k n : ℕ,
      2 ≤ k → 1 ≤ n → n ≤ k ^ 2 →
      c * min 1 ((k : ℝ) / (n * logAlphabet k)) ≤
        twoSampleL1MinimaxRisk n k := by
  obtain ⟨cD, hcD, kD, hD⟩ := twoSampleL1_lower_large_dense _of_gate
  obtain ⟨cS, hcS, kS, hS⟩ := twoSampleL1_lower_large_sparse _of_gate
  let K := max (max kD kS) 3
  let p : ℝ := (1 / 2 : ℝ) ^ (K ^ 2) / 4
  have hp : 0 < p := by dsimp [p]; positivity
  let c := min cD (min cS p)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro k n hk hn hnk
  have hrate : min 1 ((k : ℝ) / (n * logAlphabet k)) ≤ 1 := min_le_left _ _
  have hcD' : c ≤ cD := by dsimp [c]; exact min_le_left _ _
  have hcS' : c ≤ cS := by dsimp [c]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hcp : c ≤ p := by dsimp [c]; exact (min_le_right _ _).trans (min_le_right _ _)
  by_cases hlarge : K ≤ k
  · have hkD : kD ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hlarge)
    have hkS : max kS 3 ≤ k := by
      exact max_le (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hlarge))
        (le_trans (le_max_right _ _) hlarge)
    have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hlarge
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hlogpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hratio : 1 < (k : ℝ) / Real.log k := by
      apply (lt_div_iff₀ hlogpos).2
      linarith [Real.log_le_sub_one_of_pos hkpos]
    by_cases hsparse : (n : ℝ) < (k : ℝ) / Real.log k
    · have hbase := hS k n hkS hn hsparse
      calc
        c * min 1 ((k : ℝ) / (n * logAlphabet k)) ≤ c := by
          nlinarith [hrate]
        _ ≤ cS := hcS'
        _ ≤ twoSampleL1MinimaxRisk n k := hbase
    · have hsample : (k : ℝ) / Real.log k ≤ n := le_of_not_gt hsparse
      have hn2 : 2 ≤ n := by
        have : (1 : ℝ) < n := lt_of_lt_of_le hratio hsample
        exact_mod_cast this
      have hbase := hD k n hkD hk hn2 hnk hsample
      have hrate0 : 0 ≤ min 1 ((k : ℝ) / (n * logAlphabet k)) := by
        apply le_min (by norm_num)
        have hLpos : 0 < logAlphabet k := by
          unfold logAlphabet
          rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkpos)]
          simp
          linarith
        positivity
      exact (mul_le_mul_of_nonneg_right hcD' hrate0).trans hbase
  · have hkK : k ≤ K := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hnK : n ≤ K ^ 2 := le_trans hnk (Nat.pow_le_pow_left hkK 2)
    haveI : NeZero k := ⟨by omega⟩
    have hbase := twoSampleL1_finiteAlphabetLower k (K ^ 2) hk
    have hrisk := twoSampleL1_minimax_antitone (k := k) hnK
    calc
      c * min 1 ((k : ℝ) / (n * logAlphabet k)) ≤ c := by
        nlinarith [hrate]
      _ ≤ p := hcp
      _ ≤ twoSampleL1MinimaxRisk (K ^ 2) k := hbase
      _ ≤ twoSampleL1MinimaxRisk n k := hrisk

/-- The paper's small-sample bound and the generic large-sample theorem give
the matched two-sample lower bound for every positive sample size. With [the specified inputs and conditions](hyp:of_gate), [the stated relationship holds](goal). -/
-- @node: two_sample_l1_lower_all_samples
lemma two_sample_l1_lower_all_samples (of_gate : JHWKnownQL1LowerRegime) :
    ∃ c : ℝ, 0 < c ∧ ∀ k n : ℕ,
      2 ≤ k → 1 ≤ n →
      c * min 1 ((k : ℝ) / (n * logAlphabet k)) ≤
        twoSampleL1MinimaxRisk n k := by
  obtain ⟨cS, hcS, hS⟩ := two_sample_l1_lower of_gate
  obtain ⟨cL, hcL, hL⟩ :=
    Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1MinimaxRisk_largeSample_lower
  refine ⟨min cS cL, by positivity, ?_⟩
  intro k n hk hn
  by_cases hsmall : n ≤ k ^ 2
  · have h := hS k n hk hn hsmall
    have hr : 0 ≤ min 1 ((k : ℝ) / (n * logAlphabet k)) := by
      apply le_min (by norm_num)
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hlog : 0 < logAlphabet k := by
        unfold logAlphabet
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkpos)]
        simp
        positivity
      positivity
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hr).trans h
  · have hlarge : k ^ 2 < n := Nat.lt_of_not_ge hsmall
    have h := hL k n hk hlarge
    have hratio : (k : ℝ) / (n * logAlphabet k) ≤ 1 := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlog : 1 ≤ logAlphabet k := by
        unfold logAlphabet
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkpos)]
        simp
        exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
      apply (div_le_iff₀ (mul_pos hnpos (lt_of_lt_of_le zero_lt_one hlog))).2
      have hlargeR : (k : ℝ) ^ 2 < n := by exact_mod_cast hlarge
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    rw [min_eq_right hratio]
    have hratio0 : 0 ≤ (k : ℝ) / (n * logAlphabet k) := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlog : 0 < logAlphabet k := by
        unfold logAlphabet
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkpos)]
        simp
        positivity
      positivity
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hratio0).trans h
end CausalSmith.Stat.DiscreteBudgetvalueCurve
