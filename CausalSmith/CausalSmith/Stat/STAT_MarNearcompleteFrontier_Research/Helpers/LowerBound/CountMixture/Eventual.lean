module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.AssembledTail
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Eventual for the paired count-mixture comparison -/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Exponential tilting bounds the unmatched factorial tail, without needing
an asymptotic approximation to the factorial. Given [the specified input `K`](hyp:K), [the specified input `z`](hyp:z), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). -/
-- @node: countMixture_exponential_tail_le
lemma countMixture_exponential_tail_le (K : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail K z ≤
      Real.exp (-(K : ℝ) + Real.exp 1 * z) := by
  let f : ℕ → ℝ := fun t => if K < t then z ^ t / (t.factorial : ℝ) else 0
  let g : ℕ → ℝ := fun t =>
    Real.exp (-(K : ℝ)) * ((Real.exp 1 * z) ^ t / (t.factorial : ℝ))
  have hg : Summable g := (Real.summable_pow_div_factorial (Real.exp 1 * z)).mul_left _
  have hle (t : ℕ) : f t ≤ g t := by
    dsimp [f, g]
    split_ifs with ht
    · have hKt : (K : ℝ) ≤ t := by exact_mod_cast ht.le
      have hscale : 1 ≤ Real.exp (-(K : ℝ)) * Real.exp 1 ^ t := by
        rw [← Real.exp_nat_mul, mul_one, ← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      have hterm : 0 ≤ z ^ t / (t.factorial : ℝ) := by positivity
      calc
        _ ≤ (Real.exp (-(K : ℝ)) * Real.exp 1 ^ t) *
            (z ^ t / (t.factorial : ℝ)) := le_mul_of_one_le_left hterm hscale
        _ = _ := by rw [mul_pow]; ring
    · positivity
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun t => by dsimp [f]; positivity) hle hg
  calc
    _ ≤ ∑' t, g t := hf.tsum_le_tsum hle hg
    _ = Real.exp (-(K : ℝ)) * Real.exp (Real.exp 1 * z) := by
      rw [show (∑' t, g t) = Real.exp (-(K : ℝ)) *
          ∑' t : ℕ, (Real.exp 1 * z) ^ t / (t.factorial : ℝ) by
            simp [g, tsum_mul_left]]
      congr 1
      simpa only [← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (Real.exp 1 * z)).tsum_eq
    _ = _ := (Real.exp_add _ _).symm

/-- The prior's logarithmic matched degree makes the whole pair-count tail
at most the reciprocal sample size, uniformly in the dimension. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). -/
-- @node: countMixture_factorial_tail_budget
lemma countMixture_factorial_tail_budget (n d : ℕ) (hn : 1 ≤ n) :
    (pairCount n d : ℝ) *
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        (priorK n) (16 * (n : ℝ) * priorB n) ≤ 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hK0 : 0 ≤ (priorK n : ℝ) := Nat.cast_nonneg _
  have hz : 16 * (n : ℝ) * priorB n = (priorK n : ℝ) / 64 := by
    unfold priorB
    field_simp
    <;> ring
  have ht := countMixture_exponential_tail_le (priorK n)
    ((priorK n : ℝ) / 64) (by positivity)
  have ht' : Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
      (priorK n) ((priorK n : ℝ) / 64) ≤ Real.exp (-4 * ell n) := by
    apply ht.trans
    apply Real.exp_le_exp.mpr
    have hK := priorK_lower_for_normalization n
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ (priorK n : ℝ) / 64 by positivity)
    linarith
  have hell : 0 ≤ ell n := (one_le_ell_scale n).trans' (by norm_num)
  have hM : (pairCount n d : ℝ) ≤ (n : ℝ) * ell n := by
    have hm : pairCount n d ≤ Nat.floor ((n : ℝ) * ell n) := by
      unfold pairCount
      exact min_le_right _ _
    exact (Nat.cast_le.mpr hm).trans (Nat.floor_le (by positivity))
  have hexp : Real.exp (ell n) = Real.exp 1 + n := by
    unfold ell
    rw [Real.exp_log (by positivity)]
  have hnexp : (n : ℝ) ≤ Real.exp (ell n) := by
    rw [hexp]
    linarith [Real.exp_pos 1]
  have hLexp : ell n ≤ Real.exp (ell n) := by
    linarith [Real.add_one_le_exp (ell n)]
  calc
    _ ≤ (n : ℝ) * ell n * Real.exp (-4 * ell n) := by
      rw [hz]
      exact (mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)
    _ ≤ (Real.exp (ell n) * Real.exp (ell n)) * Real.exp (-4 * ell n) := by
      gcongr
    _ = Real.exp (-2 * ell n) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-ell n) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / (n : ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hnpos hnexp

-- @node: mixedCountLaw_tv_eventual
/-- Count-mixture half of the large-sample comparison. Moment cancellation in
`latent_signed_power_moment_zero` removes degrees two through `priorK`; the
remaining Poisson likelihood tail must be summed over the independent pairs. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma mixedCountLaw_tv_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (n d : ℕ) (q : ℝ), N ≤ n → ∀ (hn : 1 ≤ n) (hd : 1 ≤ d)
        (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        Causalean.Stat.tvDist
          (mixedCountLaw n d q (-1) hn hd hq)
          (mixedCountLaw n d q 1 hn hd hq) ≤ β / 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / β)
  refine ⟨max N₀ 2, le_max_right _ _, ?_⟩
  intro n d q hnN hn hd hq _hreg
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hnN
  have hnR : 2 / β < (n : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hn0)
  calc
    _ ≤ _ := mixedCountLaw_tv_le_factorial_tail n d q hn hd hq
    _ ≤ 1 / (n : ℝ) := countMixture_factorial_tail_budget n d hn
    _ ≤ β / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
      have h := (div_lt_iff₀ hβ).mp hnR
      linarith


end CausalSmith.Stat.MarNearcompleteFrontier
