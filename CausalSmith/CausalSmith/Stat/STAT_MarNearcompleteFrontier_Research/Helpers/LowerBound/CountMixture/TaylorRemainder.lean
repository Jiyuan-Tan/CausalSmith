module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.CountDegree
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Convergent unmatched Taylor remainder for one paired count block

The exponential expansion is summed before taking absolute values. All matched
coefficients cancel by the latent signed moments and the low-degree mark identities.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

/-- The factorial-normalized signed coefficient of one paired count block. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairBlockTaylorCoefficient
noncomputable def pairBlockTaylorCoefficient (n d t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  (∑ z : Latent n, latentWeight n z *
    ((-8 * (n : ℝ) * latentP n z) ^ t *
      (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
      (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
        pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))) /
    (2 * (t.factorial : ℝ) * pairBlockFactorial n d hd j counts)

/-- The coefficient on the full marked alphabet agrees with the original
block coefficient whenever the count vector is supported on that pair. For [a positive covariate dimension](hyp:hd) and [a count vector supported on the selected pair](hyp:hsupport), [the marked Taylor coefficient equals the local block coefficient](goal). -/
-- @node: pairMarkedTaylorCoefficient_eq_local_of_supported
lemma pairMarkedTaylorCoefficient_eq_local_of_supported (n d t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hsupport : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0) :
    pairMarkedTaylorCoefficient n d t q hd j counts =
      pairBlockTaylorCoefficient n d t q hd j counts := by
  unfold pairMarkedTaylorCoefficient pairBlockTaylorCoefficient
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [pairMarkedDegreeGap_eq_local_of_supported n d q (latentZ n z)
    (latentP n z) hd j counts hsupport]
  ring

/-- For [a positive covariate dimension](hyp:hd), if [an observed atom lies outside the selected pair](hyp:ho) and [has positive count](hyp:hc), [its signed marked Taylor coefficient is zero](goal). -/
-- @node: pairMarkedTaylorCoefficient_eq_zero_of_unsupported
lemma pairMarkedTaylorCoefficient_eq_zero_of_unsupported (n d t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (o : Obs d) (ho : ∀ side : Bool, o.X ≠ pairLabel n d hd j side)
    (hc : counts o ≠ 0) :
    pairMarkedTaylorCoefficient n d t q hd j counts = 0 := by
  unfold pairMarkedTaylorCoefficient pairMarkedDegreeGap
  simp_rw [pairMarkedIntensity_prod_eq_zero_of_unsupported n d q _ _ _ hd j _ counts o ho hc]
  simp

/-- The signed pair likelihood has a convergent exponential Taylor expansion,
with the finite latent average interchanged with the series. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMixtureFactor_gap_hasSum
lemma pairMixtureFactor_gap_hasSum (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    HasSum (fun t => pairBlockTaylorCoefficient n d t q hd j counts)
      (pairMixtureFactor n d q (-1) hd j counts -
        pairMixtureFactor n d q 1 hd j counts) := by
  have hz (z : Latent n) :
      HasSum (fun t : ℕ =>
        ((-8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
          (latentWeight n z *
            (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
            (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
              pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts) /
            (2 * pairBlockFactorial n d hd j counts)))
        (Real.exp (-8 * (n : ℝ) * latentP n z) *
          (latentWeight n z *
            (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
            (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
              pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts) /
            (2 * pairBlockFactorial n d hd j counts))) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp
        (-8 * (n : ℝ) * latentP n z)).mul_right
        (latentWeight n z *
          (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
          (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts) /
          (2 * pairBlockFactorial n d hd j counts))
  have hs := hasSum_sum (s := (Finset.univ : Finset (Latent n))) (fun z _ => hz z)
  have hterm (t : ℕ) :
      pairBlockTaylorCoefficient n d t q hd j counts =
        ∑ z : Latent n,
          ((-8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
            (latentWeight n z *
              (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
              (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
                pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts) /
              (2 * pairBlockFactorial n d hd j counts)) := by
    unfold pairBlockTaylorCoefficient
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hsum :
      (∑ z : Latent n, Real.exp (-8 * (n : ℝ) * latentP n z) *
        (latentWeight n z *
          (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
          (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts) /
          (2 * pairBlockFactorial n d hd j counts))) =
        pairMixtureFactor n d q (-1) hd j counts -
          pairMixtureFactor n d q 1 hd j counts := by
    unfold pairMixtureFactor
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hsum] at hs
  exact hs.congr_fun hterm

/-- Every coefficient whose combined count and Taylor degree is matched is zero. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hmatch`](hyp:hmatch), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairBlockTaylorCoefficient_eq_zero_of_matched
lemma pairBlockTaylorCoefficient_eq_zero_of_matched (n d t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hmatch : pairBlockCount n d hd counts j + t ≤ priorK n) :
    pairBlockTaylorCoefficient n d t q hd j counts = 0 := by
  unfold pairBlockTaylorCoefficient
  rw [pairBlock_low_total_coefficient_cancel n d
    (pairBlockCount n d hd counts j) t q hd j counts rfl hmatch, zero_div]

/-- After including the zero-rate support constraint, every coefficient of
matched total observed and Taylor degree vanishes on the full alphabet. For [a positive covariate dimension](hyp:hd), if [the total count plus Taylor degree is within the matching range](hyp:hmatch), [the signed marked Taylor coefficient is zero](goal). -/
-- @node: pairMarkedTaylorCoefficient_eq_zero_of_matched
lemma pairMarkedTaylorCoefficient_eq_zero_of_matched (n d t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hmatch : (∑ o : Obs d, counts o) + t ≤ priorK n) :
    pairMarkedTaylorCoefficient n d t q hd j counts = 0 := by
  classical
  by_cases hs : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0
  · rw [pairMarkedTaylorCoefficient_eq_local_of_supported n d t q hd j counts hs]
    apply pairBlockTaylorCoefficient_eq_zero_of_matched
    rw [pairBlockCount_eq_total_of_supported n d hd j counts hs]
    exact hmatch
  · push Not at hs
    obtain ⟨o, ho, hc⟩ := hs
    exact pairMarkedTaylorCoefficient_eq_zero_of_unsupported n d t q hd j counts o ho hc

/-- The full signed pair likelihood is exactly its unmatched Taylor remainder;
no absolute-value relaxation is made until after the moment cancellations. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMixtureFactor_gap_eq_unmatched_tsum
lemma pairMixtureFactor_gap_eq_unmatched_tsum (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    pairMixtureFactor n d q (-1) hd j counts -
        pairMixtureFactor n d q 1 hd j counts =
      ∑' t : ℕ, if priorK n < pairBlockCount n d hd counts j + t then
        pairBlockTaylorCoefficient n d t q hd j counts else 0 := by
  rw [← (pairMixtureFactor_gap_hasSum n d q hd j counts).tsum_eq]
  apply tsum_congr
  intro t
  split_ifs with h
  · rfl
  · exact pairBlockTaylorCoefficient_eq_zero_of_matched n d t q hd j counts
      (Nat.le_of_not_gt h)

/-- The absolute pair likelihood gap is bounded by the absolutely convergent
unmatched coefficient series. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMixtureFactor_gap_abs_le_unmatched_tsum
lemma pairMixtureFactor_gap_abs_le_unmatched_tsum (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |pairMixtureFactor n d q (-1) hd j counts -
        pairMixtureFactor n d q 1 hd j counts| ≤
      ∑' t : ℕ, if priorK n < pairBlockCount n d hd counts j + t then
        |pairBlockTaylorCoefficient n d t q hd j counts| else 0 := by
  let E : Set ℕ := {t | priorK n < pairBlockCount n d hd counts j + t}
  have hs := (pairMixtureFactor_gap_hasSum n d q hd j counts).summable.indicator E
  rw [pairMixtureFactor_gap_eq_unmatched_tsum]
  have hn := norm_tsum_le_tsum_norm hs.norm
  simpa only [Real.norm_eq_abs, Set.indicator, E, Set.mem_ofPred_eq,
    apply_ite abs, abs_zero] using hn

/-- Each normalized coefficient has a factorial envelope, uniform over the
legal arrival floor and over all latent nodes. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairBlockTaylorCoefficient_abs_le_factorial
lemma pairBlockTaylorCoefficient_abs_le_factorial (n d t : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |pairBlockTaylorCoefficient n d t q hd j counts| ≤
      ((8 * (n : ℝ) * priorB n) ^ t / (t.factorial : ℝ)) *
        ((4 * (n : ℝ) * priorB n) ^ pairBlockCount n d hd counts j /
          pairBlockFactorial n d hd j counts) := by
  have hfac : 0 < pairBlockFactorial n d hd j counts := by
    unfold pairBlockFactorial pairLabelFactorial
    positivity
  have hden : 0 < 2 * (t.factorial : ℝ) *
      pairBlockFactorial n d hd j counts := by positivity
  unfold pairBlockTaylorCoefficient
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ (2 * (8 * (n : ℝ) * priorB n) ^ t *
        (4 * (n : ℝ) * priorB n) ^ pairBlockCount n d hd counts j) /
        (2 * (t.factorial : ℝ) * pairBlockFactorial n d hd j counts) :=
      div_le_div_of_nonneg_right
        (pairBlock_taylor_coefficient_abs_le n d
          (pairBlockCount n d hd counts j) t q hn hd hq j counts) hden.le
    _ = _ := by ring

/-- For a fixed observed block, only Taylor terms above the matched combined
degree contribute to the signed likelihood gap. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMixtureFactor_gap_abs_le_factorial_remainder
lemma pairMixtureFactor_gap_abs_le_factorial_remainder (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |pairMixtureFactor n d q (-1) hd j counts -
        pairMixtureFactor n d q 1 hd j counts| ≤
      ∑' t : ℕ, if priorK n < pairBlockCount n d hd counts j + t then
        ((8 * (n : ℝ) * priorB n) ^ t / (t.factorial : ℝ)) *
          ((4 * (n : ℝ) * priorB n) ^ pairBlockCount n d hd counts j /
            pairBlockFactorial n d hd j counts) else 0 := by
  let E : Set ℕ := {t | priorK n < pairBlockCount n d hd counts j + t}
  have hleft :=
    (pairMixtureFactor_gap_hasSum n d q hd j counts).summable.norm.indicator E
  have hright := ((Real.summable_pow_div_factorial
    (8 * (n : ℝ) * priorB n)).mul_right
      ((4 * (n : ℝ) * priorB n) ^ pairBlockCount n d hd counts j /
        pairBlockFactorial n d hd j counts)).indicator E
  refine (pairMixtureFactor_gap_abs_le_unmatched_tsum n d q hd j counts).trans ?_
  apply Summable.tsum_le_tsum
  · intro t
    split_ifs
    · exact pairBlockTaylorCoefficient_abs_le_factorial n d t q hn hd hq j counts
    · rfl
  · exact hleft.congr (fun t => by simp [Set.indicator, E, Real.norm_eq_abs])
  · exact hright.congr (fun t => by simp [Set.indicator, E])

/-- At each combined degree, the matched coefficients vanish and the
unmatched marked coefficients have the factorial envelope at twice the
maximal pair intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `s`](hyp:s), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedTaylorCoefficient_total_degree_l1
lemma pairMarkedTaylorCoefficient_total_degree_l1 (n d s : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    (∑ r ∈ Finset.range (s + 1),
      ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
        |pairMarkedTaylorCoefficient n d (s - r) q hd j counts|) ≤
      if priorK n < s then
        2 * (16 * (n : ℝ) * priorB n) ^ s / (s.factorial : ℝ) else 0 := by
  classical
  by_cases hs : priorK n < s
  · rw [if_pos hs]
    calc
      _ ≤ ∑ r ∈ Finset.range (s + 1),
          2 * ((8 * (n : ℝ) * priorB n) ^ (s - r) / ((s - r).factorial : ℝ)) *
            ((8 * (n : ℝ) * priorB n) ^ r / (r.factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro r _
        exact pairMarkedTaylorCoefficient_fixed_degree_l1 n d r (s - r) q hn hd hq j
      _ = 2 * ∑ r ∈ Finset.range (s + 1),
          ((8 * (n : ℝ) * priorB n) ^ r / (r.factorial : ℝ)) *
            ((8 * (n : ℝ) * priorB n) ^ (s - r) / ((s - r).factorial : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by
        rw [factorial_series_convolution]
        rw [show 8 * (n : ℝ) * priorB n + 8 * (n : ℝ) * priorB n =
          16 * (n : ℝ) * priorB n by ring]
        ring
  · rw [if_neg hs]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro r hr
    have hrs : r ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    apply Finset.sum_eq_zero
    intro counts hc
    have hcount : ∑ o : Obs d, counts o = r := (Finset.mem_piAntidiag.mp hc).1
    rw [pairMarkedTaylorCoefficient_eq_zero_of_matched, abs_zero]
    rw [hcount, Nat.add_sub_of_le hrs]
    exact Nat.le_of_not_gt hs

/-- The absolutely summed marked Taylor coefficients are bounded by twice
the unmatched exponential-series tail. Matched degrees have been removed
using the signed latent moments before this summation. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedTaylorCoefficient_degree_tsum_le_factorial_tail
lemma pairMarkedTaylorCoefficient_degree_tsum_le_factorial_tail (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    (∑' s : ℕ, ∑ r ∈ Finset.range (s + 1),
      ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
        |pairMarkedTaylorCoefficient n d (s - r) q hd j counts|) ≤
      2 * Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        (priorK n) (16 * (n : ℝ) * priorB n) := by
  classical
  let f : ℕ → ℝ := fun s => ∑ r ∈ Finset.range (s + 1),
    ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
      |pairMarkedTaylorCoefficient n d (s - r) q hd j counts|
  let g : ℕ → ℝ := fun s => if priorK n < s then
    2 * (16 * (n : ℝ) * priorB n) ^ s / (s.factorial : ℝ) else 0
  have hle (s : ℕ) : f s ≤ g s :=
    pairMarkedTaylorCoefficient_total_degree_l1 n d s q hn hd hq j
  have hg : Summable g := by
    have h := ((Real.summable_pow_div_factorial
      (16 * (n : ℝ) * priorB n)).mul_left 2).indicator {s : ℕ | priorK n < s}
    exact h.congr (fun s => by simp [g, Set.indicator, mul_div_assoc])
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun s => Finset.sum_nonneg (fun r _ =>
      Finset.sum_nonneg (fun counts _ => abs_nonneg _))) hle hg
  calc
    _ ≤ ∑' s : ℕ, g s := hf.tsum_le_tsum hle hg
    _ = _ := by
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
      rw [← tsum_mul_left]
      apply tsum_congr
      intro s
      by_cases hs : priorK n < s <;> simp [g, hs, mul_div_assoc]

end CausalSmith.Stat.MarNearcompleteFrontier
