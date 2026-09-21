import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.AggregatePoisson.Basic

/-!
# Geometric exponential-series tails

This module supplies the analytic geometric-tail estimate used by aggregate Poisson mixture bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

private lemma geometric_quarter_tail (L : ℕ) :
    (∑' n : ℕ, if L < n then (1 / 4 : ℝ) ^ n else 0) ≤ (1 / 4 : ℝ) ^ L := by
  have hq : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hf : Summable (fun n : ℕ => if L < n then (1 / 4 : ℝ) ^ n else 0) := by
    apply hq.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      split_ifs
      · rfl
      · positivity
  have hzero :
      ((Finset.range (L + 1)).sum
        fun n : ℕ => if L < n then (1 / 4 : ℝ) ^ n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnle : n ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [if_neg (Nat.not_lt_of_ge hnle)]
  rw [← hf.sum_add_tsum_nat_add (L + 1), hzero, zero_add]
  simp only [show ∀ n : ℕ, L < n + (L + 1) by omega, if_true, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num)]
  norm_num [pow_succ]
  have hp : 0 ≤ (1 / 4 : ℝ) ^ L := pow_nonneg (by norm_num) L
  nlinarith

private lemma exponential_term_le_quarter_pow
    (L n : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hzL : z ≤ (L : ℝ) / (16 * Real.exp 1)) (hLn : L < n) :
    z ^ n / (n.factorial : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le L) hLn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hbase : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hfac :
      ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n ≤
          Real.sqrt (2 * Real.pi * (n : ℝ)) *
            ((n : ℝ) / Real.exp 1) ^ n := by
              nlinarith
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hbasepos : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hratio_nonneg : 0 ≤ z * Real.exp 1 / (n : ℝ) := by positivity
  have hratio : z * Real.exp 1 / (n : ℝ) ≤ (1 / 16 : ℝ) := by
    calc
      z * Real.exp 1 / (n : ℝ) ≤
          ((L : ℝ) / (16 * Real.exp 1)) * Real.exp 1 / (n : ℝ) := by
            gcongr
      _ = (L : ℝ) / (16 * (n : ℝ)) := by field_simp
      _ ≤ 1 / 16 := by
        rw [div_le_iff₀ (by positivity)]
        calc
          (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLn.le
          _ = 1 / 16 * (16 * (n : ℝ)) := by ring
  calc
    z ^ n / (n.factorial : ℝ) ≤
        z ^ n / (((n : ℝ) / Real.exp 1) ^ n) :=
      div_le_div_of_nonneg_left (pow_nonneg hz n) hbasepos hfac
    _ = (z * Real.exp 1 / (n : ℝ)) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ (1 / 16 : ℝ) ^ n := pow_le_pow_left₀ hratio_nonneg hratio n
    _ ≤ (1 / 4 : ℝ) ^ n := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- The [stated conclusion](goal) follows from [the tail-scale constant](hyp:A), [positive tail-scale constant](hyp:hA), [the moment-matching degree](hyp:L), [the evaluation point](hyp:x).  A square root of an exponential-series tail is uniformly geometric in
the matching degree when its argument is at most a sufficiently small fixed
multiple of that degree. -/
theorem exists_geometric_sqrt_exponentialSeriesTail_bound
    (A : ℝ) (hA : 0 < A) :
    ∃ b D ρ : ℝ, 0 < b ∧ 0 < D ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (L : ℕ) (x : ℝ), 0 ≤ x → x ≤ b * L →
        Real.sqrt
            (Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L
              (A * x)) ≤
          D * ρ ^ L := by
  refine ⟨1 / (16 * A * Real.exp 1), 1, 1 / 2, by positivity, by norm_num,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  intro L x hx hband
  obtain rfl | hL := L.eq_zero_or_pos
  · have hxle : x ≤ 0 := by simpa using hband
    have hxeq : x = 0 := le_antisymm hxle hx
    subst x
    have htailzero :
        Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail 0 0 = 0 := by
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
      rw [show (fun n : ℕ =>
          if 0 < n then (0 : ℝ) ^ n / (n.factorial : ℝ) else 0) = 0 by
        funext n
        split_ifs with hn
        · simp [zero_pow (Nat.ne_of_gt hn)]
        · rfl]
      exact tsum_zero
    simp only [mul_zero]
    rw [htailzero, Real.sqrt_zero, pow_zero]
    norm_num
  have hz : 0 ≤ A * x := mul_nonneg hA.le hx
  have hzL : A * x ≤ (L : ℝ) / (16 * Real.exp 1) := by
    calc
      A * x ≤ A * ((1 / (16 * A * Real.exp 1)) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hband hA.le
      _ = (L : ℝ) / (16 * Real.exp 1) := by field_simp
  let f : ℕ → ℝ := fun n =>
    if L < n then (A * x) ^ n / (n.factorial : ℝ) else 0
  let g : ℕ → ℝ := fun n =>
    if L < n then (1 / 4 : ℝ) ^ n else 0
  have hq : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hg : Summable g := by
    apply hq.of_nonneg_of_le
    · intro n
      dsimp [g]
      positivity
    · intro n
      dsimp [g]
      split_ifs
      · rfl
      · positivity
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    dsimp [f, g]
    split_ifs with hn
    · exact exponential_term_le_quarter_pow L n (A * x) hz hzL hn
    · rfl
  have hf : Summable f := hg.of_nonneg_of_le hf_nonneg hfg
  have htail :
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L (A * x) ≤
        (1 / 4 : ℝ) ^ L := by
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
    change (∑' n, f n) ≤ _
    exact (hf.tsum_le_tsum hfg hg).trans (geometric_quarter_tail L)
  rw [one_mul, Real.sqrt_le_iff]
  refine ⟨by positivity, htail.trans_eq ?_⟩
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega


end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
