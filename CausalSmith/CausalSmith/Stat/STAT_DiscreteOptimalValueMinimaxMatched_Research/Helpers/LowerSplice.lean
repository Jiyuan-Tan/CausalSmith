import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.RegularLower
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseLowerAssembly
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.AlphabetPadding
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Numerical and statistical assembly for the lower-bound regime splice. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open Filter

/-- If [the alphabet size satisfies its stated restriction](hyp:hd), then [the logarithmic alphabet size is positive](goal). -/
lemma logAlphabet_pos (d : ℕ) (hd : 1 ≤ d) : 0 < logAlphabet d := by
  rw [logAlphabet]
  apply Real.log_pos
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)]

/-- If [the alphabet size satisfies its stated restriction](hyp:hd), then [the logarithmic alphabet size is at least one](goal). -/
lemma logAlphabet_one_le (d : ℕ) (hd : 1 ≤ d) : 1 ≤ logAlphabet d := by
  rw [logAlphabet]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (Real.exp 1 * d) := Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos 1) (mul_pos (Real.exp_pos 1) (by positivity))
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1))

/-- [for all sufficiently large alphabets, $log(ed)$ is at most $d/2$](goal). -/
lemma eventually_logAlphabet_le_half :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → logAlphabet d ≤ (d : ℝ) / 2 := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 6)
  have ht : Tendsto (fun d : ℕ => Real.exp 1 * (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1)
  have hev : ∀ᶠ d : ℕ in atTop, logAlphabet d ≤ (d : ℝ) / 2 := by
    filter_upwards [hsmall.filter_mono ht, eventually_ge_atTop (1 : ℕ)] with d hd hd1
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * (d : ℝ)) :=
      (logAlphabet_one_le d hd1).trans' (by norm_num)
    have hd0 : 0 ≤ (d : ℝ) := by positivity
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    change ‖Real.log (Real.exp 1 * (d : ℝ))‖ ≤
      (1 / 6 : ℝ) * ‖id (Real.exp 1 * (d : ℝ))‖ at hd
    rw [Real.norm_eq_abs, abs_of_nonneg hlog0, Real.norm_eq_abs] at hd
    have hd' : Real.log (Real.exp 1 * (d : ℝ)) ≤
        (1 / 6 : ℝ) * (Real.exp 1 * d) := by
      simpa only [id_eq, abs_of_nonneg (mul_nonneg (Real.exp_nonneg 1) hd0)] using hd
    unfold logAlphabet
    calc
      Real.log (Real.exp 1 * (d : ℝ)) ≤ (1 / 6) * (Real.exp 1 * d) := hd'
      _ ≤ d / 2 := by nlinarith [mul_le_mul_of_nonneg_right he.le hd0]
  simpa only [eventually_atTop] using hev

/-- If [the stated c condition holds](hyp:hc), then [beyond a finite sample-size cutoff, the paired Poisson tail is absorbed by the stated constant bounds](goal). -/
lemma pairedTail_cutoff (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤ c / (2 * n) ∧
      8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤ c / 2 := by
  have ha : 0 < 1 - Real.log 2 := by
    linarith [Real.log_two_lt_d9]
  have htReal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
    (1 - Real.log 2) ha
  have ht : Tendsto (fun n : ℕ => (n : ℝ) *
      Real.exp (-(n : ℝ) * (1 - Real.log 2))) atTop (nhds 0) := by
    convert htReal.comp tendsto_natCast_atTop_atTop using 1
    funext n
    simp only [Function.comp_apply, Real.rpow_one]
    congr 2 <;> ring
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N0, hN0⟩ := ht (c / 16) (by positivity)
  refine ⟨max 2 N0, Nat.le_max_left _ _, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnR : (0 : ℝ) < n := by positivity
  have hdist := hN0 n hn0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (by positivity)
    (Real.exp_nonneg _))] at hdist
  constructor
  · apply (le_div_iff₀ (mul_pos (by norm_num) hnR)).2
    nlinarith
  · have htail_nonneg : 0 ≤ 8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by positivity
    have hone : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hn2)
    nlinarith

/-- For [the specified sample size](hyp:n), the [saturated alphabet size is the ceiling of sample size times its logarithmic scale](goal). -/
noncomputable def saturatedAlphabet (n : ℕ) : ℕ :=
  ⌈(n : ℝ) * Real.log (Real.exp 1 * n)⌉₊

/-- If [the sample size satisfies its stated restriction](hyp:hn), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the stated sat condition holds](hyp:hsat), then [the saturated alphabet is at least two, fits inside the original alphabet, meets the L1 lower-bound gate, and has the stated logarithmic ratio bounds](goal). -/
lemma saturatedAlphabet_properties (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hsat : (n : ℝ) < (1 / 4 : ℝ) * d / logAlphabet d) :
    let s := saturatedAlphabet n
    2 ≤ s ∧ s ≤ d ∧
      (1 / 4 : ℝ) * s / Real.log (Real.exp 1 * s) ≤ n ∧
      Real.log (Real.exp 1 * n) ≤ 2 * Real.log (Real.exp 1 * s) ∧
      1 ≤ (s : ℝ) / (n * Real.log (Real.exp 1 * n)) := by
  let Ln := Real.log (Real.exp 1 * (n : ℝ))
  let Ld := logAlphabet d
  let s := saturatedAlphabet n
  have hnR : (0 : ℝ) < n := by positivity
  have hdR : (0 : ℝ) < d := by positivity
  have hLn1 : 1 ≤ Ln := by
    dsimp [Ln]
    exact logAlphabet_one_le n (by omega)
  have hLd : 0 < Ld := logAlphabet_pos d (by omega)
  have hLd1 : 1 ≤ Ld := logAlphabet_one_le d (by omega)
  have hnd : n < d := by
    have hfour : (n : ℝ) * Ld < d / 4 := by
      apply (lt_div_iff₀ hLd).mp at hsat
      nlinarith
    have : (n : ℝ) < d := by
      nlinarith [mul_le_mul_of_nonneg_left hLd1 hnR.le]
    exact_mod_cast this
  have hLnLd : Ln ≤ Ld := by
    dsimp [Ln, Ld]
    have hndR : (n : ℝ) ≤ d := by exact_mod_cast hnd.le
    exact Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.exp 1 * (n : ℝ) by positivity)
      (show 0 < Real.exp 1 * (d : ℝ) by positivity)
      (mul_le_mul_of_nonneg_left hndR (Real.exp_nonneg 1))
  have hprod_lt : (n : ℝ) * Ln < d := by
    have hfour : (n : ℝ) * Ld < d / 4 := by
      apply (lt_div_iff₀ hLd).mp at hsat
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hLnLd hnR.le]
  have hs_le : s ≤ d := by
    apply Nat.ceil_le.mpr
    exact hprod_lt.le
  have hprod_le_s : (n : ℝ) * Ln ≤ s := by
    exact Nat.le_ceil _
  have hn_le_s : n ≤ s := by
    exact_mod_cast (calc
      (n : ℝ) ≤ n * Ln := by nlinarith
      _ ≤ s := hprod_le_s)
  have hs2 : 2 ≤ s := le_trans hn hn_le_s
  have hLs : Ln ≤ Real.log (Real.exp 1 * (s : ℝ)) := by
    dsimp [Ln]
    have hnsR : (n : ℝ) ≤ s := by exact_mod_cast hn_le_s
    exact Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.exp 1 * (n : ℝ) by positivity)
      (show 0 < Real.exp 1 * (s : ℝ) by positivity)
      (mul_le_mul_of_nonneg_left hnsR (Real.exp_nonneg 1))
  have hs_upper : (s : ℝ) ≤ 2 * n * Ln := by
    have hceil := Nat.ceil_lt_add_one (mul_nonneg hnR.le (le_trans (by norm_num) hLn1))
    change (s : ℝ) < (n : ℝ) * Ln + 1 at hceil
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hprod_ge : 2 ≤ (n : ℝ) * Ln := by
      nlinarith [mul_le_mul_of_nonneg_left hLn1 hnR.le]
    nlinarith
  have hLspos : 0 < Real.log (Real.exp 1 * (s : ℝ)) :=
    lt_of_lt_of_le (by positivity : 0 < Ln) hLs
  refine ⟨hs2, hs_le, ?_, by nlinarith, ?_⟩
  · apply (div_le_iff₀ hLspos).2
    nlinarith [hs_upper, mul_le_mul_of_nonneg_left hLs (by positivity : (0 : ℝ) ≤ n)]
  · apply (le_div_iff₀ (mul_pos hnR (by positivity : 0 < Ln))).2
    simpa [mul_assoc] using hprod_le_s

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
