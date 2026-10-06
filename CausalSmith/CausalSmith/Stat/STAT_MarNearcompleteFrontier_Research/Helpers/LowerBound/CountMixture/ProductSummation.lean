module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.TaylorSummation
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Causalean.Mathlib.Analysis.Normed.Ring.InfiniteSum.ProductL1

/-! # Normalization and L1 telescoping for independent paired counts

The one-pair factorial tail is combined across independent blocks using
normalized nonnegative likelihoods, as in equation (14) of the converse.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Mathlib.Analysis.Normed.Ring.InfiniteSum
open Causalean.Stat.Concentration.Poisson


/-- For a [sample multiplier](hyp:n), [alphabet size](hyp:d), [arrival
parameter](hyp:q), [sign](hyp:σ), [latent orientation](hyp:z), [latent
mass](hyp:p), [positive-alphabet witness](hyp:hd), [admissible-arrival
witness](hyp:hq), [admissible-sign witness](hyp:hσ), [admissible-orientation
witness](hyp:hz), [nonnegative-mass witness](hyp:hp), [pair index](hyp:j),
[base orientation](hyp:base), and [observed count vector](hyp:counts), [the
marked component likelihood equals the product of its coordinatewise Poisson
masses](goal). -/
-- @node: pairMarked_component_eq_poisson
lemma pairMarked_component_eq_poisson (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base : Bool) (counts : Obs d → ℕ) :
    Real.exp (-8 * (n : ℝ) * p) *
        (∏ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
          (counts o).factorial) =
      ∏ o : Obs d, Real.exp (-(pairMarkedRate n d q σ z p hd j base o : ℝ)) *
        (pairMarkedRate n d q σ z p hd j base o : ℝ) ^ counts o /
          (counts o).factorial := by
  simp_rw [pairMarkedRate_coe n d q σ z p hd hq hσ hz hp j base]
  rw [show (∏ o : Obs d, Real.exp (-pairMarkedIntensity n d q σ z p hd j base o) *
      pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
        (counts o).factorial) =
      (∏ o : Obs d, Real.exp (-pairMarkedIntensity n d q σ z p hd j base o)) *
        ∏ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
          (counts o).factorial by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro o _
    ring]
  rw [← Real.exp_sum, Finset.sum_neg_distrib, pairMarkedIntensity_sum]
  congr 2
  ring

-- @node: pairMarkedMixtureFactor_nonneg
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMarkedMixtureFactor_nonneg (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    0 ≤ pairMarkedMixtureFactor n d q σ hd j counts := by
  unfold pairMarkedMixtureFactor
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg
  · exact mul_nonneg (latentWeight_nonneg_count n z) (Real.exp_pos _).le
  · apply Finset.sum_nonneg
    intro base _
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro o _
    exact div_nonneg (pow_nonneg
      (pairMarkedIntensity_nonneg n d q σ (latentZ n z) (latentP n z)
        hd hq hσ (latentZ_eq_neg_one_or_one n z) (latentP_nonneg n z) j base o) _)
      (by positivity)

/-- Averaging the normalized marked components preserves their total mass. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedMixtureFactor_hasSum_one
lemma pairMarkedMixtureFactor_hasSum_one (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (j : Fin (pairCount n d)) :
    HasSum (pairMarkedMixtureFactor n d q σ hd j) 1 := by
  classical
  have hc (z : Latent n) (base : Bool) :
      HasSum (fun counts : Obs d → ℕ => Real.exp (-8 * (n : ℝ) * latentP n z) *
        ∏ o : Obs d,
          pairMarkedIntensity n d q σ (latentZ n z) (latentP n z) hd j base o ^
            counts o / (counts o).factorial) 1 := by
    simp_rw [pairMarked_component_eq_poisson n d q σ (latentZ n z) (latentP n z)
      hd hq hσ (latentZ_eq_neg_one_or_one n z) (latentP_nonneg n z) j base]
    exact (summable_poissonFactorial_countVector _).hasSum_iff.mpr
      (poissonFactorial_countVector_tsum_one _)
  have havg (z : Latent n) :=
    hasSum_sum (s := (Finset.univ : Finset Bool)) (fun base _ =>
      (hc z base).mul_left (1 / 2 : ℝ))
  have hall := hasSum_sum (s := (Finset.univ : Finset (Latent n)))
    (fun z _ => (havg z).mul_left (latentWeight n z))
  have hfn : (fun counts => ∑ z : Latent n, latentWeight n z *
      ∑ base : Bool, (1 / 2 : ℝ) * (Real.exp (-8 * (n : ℝ) * latentP n z) *
        ∏ o : Obs d, pairMarkedIntensity n d q σ (latentZ n z) (latentP n z)
          hd j base o ^ counts o / (counts o).factorial)) =
      pairMarkedMixtureFactor n d q σ hd j := by
    funext counts
    unfold pairMarkedMixtureFactor
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro base _
    ring
  rw [hfn] at hall
  simpa only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    Nat.cast_ofNat, nsmul_eq_mul, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    latentWeight_sum_real_count n d q hn hd hq] using hall

/-- Two summable nonnegative likelihoods have a summable absolute gap. Given [the specified input `A`](hyp:A), [the specified input `a`](hyp:a), [the specified input `b`](hyp:b), [the specified input `ha`](hyp:ha), [the specified input `hb`](hyp:hb), [the specified input `ha0`](hyp:ha0), [the specified input `hb0`](hyp:hb0), [the stated mathematical conclusion holds](goal). -/
-- @node: pairMarkedMixture_product_l1_le_factorial_tail
lemma pairMarkedMixture_product_l1_le_factorial_tail (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑' counts : Fin (pairCount n d) → (Obs d → ℕ),
      |(∏ j : Fin (pairCount n d), pairMarkedMixtureFactor n d q (-1) hd j (counts j)) -
        ∏ j : Fin (pairCount n d), pairMarkedMixtureFactor n d q 1 hd j (counts j)|) ≤
      2 * (pairCount n d : ℝ) *
        Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
          (priorK n) (16 * (n : ℝ) * priorB n) := by
  calc
    _ ≤ ∑ j : Fin (pairCount n d), ∑' counts : Obs d → ℕ,
        |pairMarkedMixtureFactor n d q (-1) hd j counts -
          pairMarkedMixtureFactor n d q 1 hd j counts| :=
      normalized_likelihood_fin_product_l1_le (pairCount n d) _ _
        (fun j => pairMarkedMixtureFactor_hasSum_one n d q (-1) hn hd hq (Or.inl rfl) j)
        (fun j => pairMarkedMixtureFactor_hasSum_one n d q 1 hn hd hq (Or.inr rfl) j)
        (fun j counts => pairMarkedMixtureFactor_nonneg n d q (-1) hd hq (Or.inl rfl) j counts)
        (fun j counts => pairMarkedMixtureFactor_nonneg n d q 1 hd hq (Or.inr rfl) j counts)
    _ ≤ ∑ _j : Fin (pairCount n d),
        2 * Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
          (priorK n) (16 * (n : ℝ) * priorB n) := by
      apply Finset.sum_le_sum
      intro j _
      exact pairMarkedMixtureFactor_l1_le_factorial_tail n d q hn hd hq j
    _ = _ := by simp; ring

end CausalSmith.Stat.MarNearcompleteFrontier
