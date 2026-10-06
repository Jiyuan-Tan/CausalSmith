module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.Taylor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Causalean.Mathlib.Data.Nat.Choose.Multinomial

/-! # Summing marked likelihoods at a fixed count degree

The multinomial identity sums all observed marks before bounding the latent
mass. This preserves the pair's total intensity and avoids a factor depending
on the number of mark configurations in the unmatched Taylor tail.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Mathlib.Data.Nat.Choose


/-- For a [sample multiplier](hyp:n), [alphabet size](hyp:d), [total count
degree](hyp:r), [arrival parameter](hyp:q), [sign](hyp:σ), [latent
orientation](hyp:z), [latent mass](hyp:p), [positive-alphabet
witness](hyp:hd), [pair index](hyp:j), and [base orientation](hyp:base),
[summing the factorial-normalized products of the marked intensities over all
count vectors of that degree gives the corresponding Poisson-series
coefficient](goal). -/
-- @node: pairMarkedIntensity_fixed_degree_sum
lemma pairMarkedIntensity_fixed_degree_sum (n d r : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool) :
    (∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
      ∏ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
        (counts o).factorial) =
      (8 * (n : ℝ) * p) ^ r / (r.factorial : ℝ) := by
  rw [factorial_countVector_fixed_degree_sum, pairMarkedIntensity_sum]

/-- Fairly averaging the orientations leaves the same fixed-degree mass. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedIntensity_average_fixed_degree_sum
lemma pairMarkedIntensity_average_fixed_degree_sum (n d r : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) :
    (∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
      ∑ base : Bool, (1 / 2 : ℝ) *
        ∏ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
          (counts o).factorial) =
      (8 * (n : ℝ) * p) ^ r / (r.factorial : ℝ) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, pairMarkedIntensity_fixed_degree_sum]
  simp

/-- The fixed-degree signed orientation average is bounded in total absolute
mass by the sum of its two nonnegative marked likelihoods. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedIntensity_gap_fixed_degree_l1
lemma pairMarkedIntensity_gap_fixed_degree_l1 (n d r : ℕ) (q z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p) (j : Fin (pairCount n d)) :
    (∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
      |(∑ base : Bool, (1 / 2 : ℝ) *
          ∏ o : Obs d, pairMarkedIntensity n d q (-1) z p hd j base o ^ counts o /
            (counts o).factorial) -
        ∑ base : Bool, (1 / 2 : ℝ) *
          ∏ o : Obs d, pairMarkedIntensity n d q 1 z p hd j base o ^ counts o /
            (counts o).factorial|) ≤
      2 * (8 * (n : ℝ) * p) ^ r / (r.factorial : ℝ) := by
  have hnonneg (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) (counts : Obs d → ℕ) :
      0 ≤ ∑ base : Bool, (1 / 2 : ℝ) *
        ∏ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
          (counts o).factorial := by
    apply Finset.sum_nonneg
    intro base _
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro o _
    exact div_nonneg
      (pow_nonneg (pairMarkedIntensity_nonneg n d q σ z p hd hq hσ hz hp j base o) _)
      (by positivity)
  calc
    _ ≤ ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
        ((∑ base : Bool, (1 / 2 : ℝ) *
          ∏ o : Obs d, pairMarkedIntensity n d q (-1) z p hd j base o ^ counts o /
            (counts o).factorial) +
        ∑ base : Bool, (1 / 2 : ℝ) *
          ∏ o : Obs d, pairMarkedIntensity n d q 1 z p hd j base o ^ counts o /
            (counts o).factorial) := by
      apply Finset.sum_le_sum
      intro counts _
      exact abs_le.mpr ⟨by linarith [hnonneg (-1) (Or.inl rfl) counts],
        by linarith [hnonneg 1 (Or.inr rfl) counts]⟩
    _ = _ := by
      rw [Finset.sum_add_distrib,
        pairMarkedIntensity_average_fixed_degree_sum,
        pairMarkedIntensity_average_fixed_degree_sum]
      ring

/-- For [a positive covariate dimension](hyp:hd) and [a count vector supported on the selected pair](hyp:hsupport), [the full marked factorial likelihood equals the label-restricted local likelihood](goal). -/
-- @node: pairMarkedIntensity_prod_eq_local_of_supported
lemma pairMarkedIntensity_prod_eq_local_of_supported (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool) (counts : Obs d → ℕ)
    (hsupport : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0) :
    (∏ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
      (counts o).factorial) = pairMarkedLocalFactor n d q σ z p hd j base counts := by
  classical
  unfold pairMarkedLocalFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro o _
  by_cases hlabel : ∃ side : Bool, o.X = pairLabel n d hd j side
  · obtain ⟨side, ho⟩ := hlabel
    rw [Finset.prod_eq_single side]
    · rw [if_pos ho]
    · intro side' _ hne
      rw [if_neg]
      intro ho'
      exact hne (pairLabel_injective n d hd j j side' side (ho'.symm.trans ho)).2
    · simp
  · have ho : ∀ side : Bool, o.X ≠ pairLabel n d hd j side := by
      simpa using hlabel
    have hc := hsupport o ho
    simp [hc]

/-- A positive count outside both labels of the pair makes its full marked
likelihood zero. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `counts`](hyp:counts), [the specified input `o`](hyp:o), [the specified input `ho`](hyp:ho), [the specified input `hc`](hyp:hc), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedIntensity_prod_eq_zero_of_unsupported
lemma pairMarkedIntensity_prod_eq_zero_of_unsupported (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool) (counts : Obs d → ℕ)
    (o : Obs d) (ho : ∀ side : Bool, o.X ≠ pairLabel n d hd j side)
    (hc : counts o ≠ 0) :
    (∏ o' : Obs d, pairMarkedIntensity n d q σ z p hd j base o' ^ counts o' /
      (counts o').factorial) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ o)
  have hrate : pairMarkedIntensity n d q σ z p hd j base o = 0 := by
    simp [pairMarkedIntensity, ho]
  simp [hrate, hc]

/-- For [a positive covariate dimension](hyp:hd) and [a count vector supported on the selected pair](hyp:hsupport), [the pair block count equals the total observed count](goal). -/
-- @node: pairBlockCount_eq_total_of_supported
lemma pairBlockCount_eq_total_of_supported (n d : ℕ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hsupport : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0) :
    pairBlockCount n d hd counts j = ∑ o : Obs d, counts o := by
  classical
  unfold pairBlockCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hlabel : ∃ side : Bool, o.X = pairLabel n d hd j side
  · obtain ⟨side, ho⟩ := hlabel
    rw [Finset.sum_eq_single side]
    · simp [ho]
    · intro side' _ hne
      rw [if_neg]
      intro ho'
      exact hne (pairLabel_injective n d hd j j side' side (ho'.symm.trans ho)).2
    · simp
  · have ho : ∀ side : Bool, o.X ≠ pairLabel n d hd j side := by
      simpa using hlabel
    simp [ho, hsupport o ho]

/-- The signed fair-orientation likelihood on the full observed alphabet,
with zero rates enforcing zero counts outside the selected pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedDegreeGap
noncomputable def pairMarkedDegreeGap (n d : ℕ) (q z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  (∑ base : Bool, (1 / 2 : ℝ) *
    ∏ o : Obs d, pairMarkedIntensity n d q (-1) z p hd j base o ^ counts o /
      (counts o).factorial) -
  ∑ base : Bool, (1 / 2 : ℝ) *
    ∏ o : Obs d, pairMarkedIntensity n d q 1 z p hd j base o ^ counts o /
      (counts o).factorial

/-- For [a positive covariate dimension](hyp:hd) and [a count vector supported on the selected pair](hyp:hsupport), [the signed marked likelihood has its local scalar-power representation](goal). -/
-- @node: pairMarkedDegreeGap_eq_local_of_supported
lemma pairMarkedDegreeGap_eq_local_of_supported (n d : ℕ) (q z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hsupport : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0) :
    pairMarkedDegreeGap n d q z p hd j counts =
      (4 * (n : ℝ) * p) ^ pairBlockCount n d hd counts j /
        pairBlockFactorial n d hd j counts *
          ((1 / 2 : ℝ) * pairBlockMarkAverage n d q (-1) z hd j counts -
            (1 / 2 : ℝ) * pairBlockMarkAverage n d q 1 z hd j counts) := by
  unfold pairMarkedDegreeGap
  simp_rw [pairMarkedIntensity_prod_eq_local_of_supported n d q _ z p hd j _ counts hsupport]
  rw [← half_pairBlockMarkAverage_eq_average_localFactor,
    ← half_pairBlockMarkAverage_eq_average_localFactor]
  ring

/-- The latent-averaged signed Taylor coefficient on the full observed
alphabet, including the count-support constraint outside the selected pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedTaylorCoefficient
noncomputable def pairMarkedTaylorCoefficient (n d t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  ∑ z : Latent n, latentWeight n z *
    ((-8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
      pairMarkedDegreeGap n d q (latentZ n z) (latentP n z) hd j counts

/-- Summing the absolute signed Taylor coefficient over all marks of degree
r gives the two-factor factorial envelope at the maximal latent intensity.
This is the marked multinomial step in the one-pair tail comparison. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedTaylorCoefficient_fixed_degree_l1
lemma pairMarkedTaylorCoefficient_fixed_degree_l1 (n d r t : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    (∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
      |pairMarkedTaylorCoefficient n d t q hd j counts|) ≤
      2 * ((8 * (n : ℝ) * priorB n) ^ t / (t.factorial : ℝ)) *
        ((8 * (n : ℝ) * priorB n) ^ r / (r.factorial : ℝ)) := by
  classical
  have hB0 : 0 ≤ priorB n := by unfold priorB; positivity
  have hscalar (z : Latent n) :
      |(-8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)| =
        (8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ) := by
    have hp := latentP_nonneg n z
    rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < t.factorial)]
    rw [show -8 * (n : ℝ) * latentP n z = -(8 * (n : ℝ) * latentP n z) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
  have hpoint (counts : Obs d → ℕ) :
      |pairMarkedTaylorCoefficient n d t q hd j counts| ≤
        ∑ z : Latent n, latentWeight n z *
          ((8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
            |pairMarkedDegreeGap n d q (latentZ n z) (latentP n z) hd j counts| := by
    unfold pairMarkedTaylorCoefficient
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro z _
    rw [abs_mul, abs_mul, abs_of_nonneg (latentWeight_nonneg_count n z), hscalar]
  calc
    _ ≤ ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
        ∑ z : Latent n, latentWeight n z *
          ((8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
            |pairMarkedDegreeGap n d q (latentZ n z) (latentP n z) hd j counts| :=
      Finset.sum_le_sum (fun counts _ => hpoint counts)
    _ = ∑ z : Latent n, latentWeight n z *
          ((8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
            ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
              |pairMarkedDegreeGap n d q (latentZ n z) (latentP n z) hd j counts| := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ z : Latent n, latentWeight n z *
          ((8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
            (2 * (8 * (n : ℝ) * latentP n z) ^ r / (r.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left
        (pairMarkedIntensity_gap_fixed_degree_l1 n d r q (latentZ n z)
          (latentP n z) hd hq (latentZ_eq_neg_one_or_one n z)
          (latentP_nonneg n z) j)
      have hp := latentP_nonneg n z
      exact mul_nonneg (latentWeight_nonneg_count n z) (by positivity)
    _ ≤ ∑ z : Latent n, latentWeight n z *
          (((8 * (n : ℝ) * priorB n) ^ t / (t.factorial : ℝ)) *
            (2 * (8 * (n : ℝ) * priorB n) ^ r / (r.factorial : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      rw [mul_assoc]
      have hp := latentP_nonneg n z
      have hw := latentWeight_nonneg_count n z
      have hB := latentP_le_priorB_count n z
      gcongr
    _ = _ := by
      rw [← Finset.sum_mul, latentWeight_sum_real_count n d q hn hd hq]
      ring

end CausalSmith.Stat.MarNearcompleteFrontier
