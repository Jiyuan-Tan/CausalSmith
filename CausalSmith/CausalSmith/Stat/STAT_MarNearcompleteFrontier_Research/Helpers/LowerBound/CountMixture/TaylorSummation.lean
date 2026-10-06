module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.TaylorRemainder
public import Causalean.Mathlib.Algebra.BigOperators.NatAntidiagonal.CountVector

/-! # Absolute summation of the marked Taylor series

Reindex the Taylor degree and observed counts by their combined degree. This
turns the finite multinomial coefficient bounds into an absolutely convergent
series on the full count alphabet.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Mathlib.Algebra.BigOperators.NatAntidiagonal


/-- For a [sample size](hyp:n), [alphabet size](hyp:d), [arrival
parameter](hyp:q), [positive-sample witness](hyp:hn), [positive-alphabet
witness](hyp:hd), [admissible-arrival witness](hyp:hq), and [pair
index](hyp:j), [the sequence of absolute marked Taylor coefficients grouped
by combined Taylor and count degree is summable](goal). -/
-- @node: pairMarkedTaylorCoefficient_degree_summable
lemma pairMarkedTaylorCoefficient_degree_summable (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    Summable (fun s : ℕ => ∑ r ∈ Finset.range (s + 1),
      ∑ counts ∈ (Finset.univ : Finset (Obs d)).piAntidiag r,
        |pairMarkedTaylorCoefficient n d (s - r) q hd j counts|) := by
  classical
  let g : ℕ → ℝ := fun s => if priorK n < s then
    2 * (16 * (n : ℝ) * priorB n) ^ s / (s.factorial : ℝ) else 0
  have hg : Summable g := by
    have h := ((Real.summable_pow_div_factorial
      (16 * (n : ℝ) * priorB n)).mul_left 2).indicator {s : ℕ | priorK n < s}
    exact h.congr (fun s => by simp [g, Set.indicator, mul_div_assoc])
  exact Summable.of_nonneg_of_le
    (fun s => Finset.sum_nonneg (fun r _ =>
      Finset.sum_nonneg (fun counts _ => abs_nonneg _)))
    (fun s => pairMarkedTaylorCoefficient_total_degree_l1 n d s q hn hd hq j) hg

/-- The marked coefficients are absolutely summable jointly over Taylor degree
and all observed count vectors. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedTaylorCoefficient_joint_summable
lemma pairMarkedTaylorCoefficient_joint_summable (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    Summable (fun x : ℕ × (Obs d → ℕ) =>
      |pairMarkedTaylorCoefficient n d x.1 q hd j x.2|) := by
  classical
  exact summable_countTaylor_of_degree (I := Obs d)
    (fun t counts => |pairMarkedTaylorCoefficient n d t q hd j counts|)
    (fun _ _ => abs_nonneg _)
    (pairMarkedTaylorCoefficient_degree_summable n d q hn hd hq j)

/-- The full absolute Taylor/count sum obeys the same unmatched factorial tail
as the finite combined-degree sums. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedTaylorCoefficient_joint_tsum_le_factorial_tail
lemma pairMarkedTaylorCoefficient_joint_tsum_le_factorial_tail (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    (∑' x : ℕ × (Obs d → ℕ),
      |pairMarkedTaylorCoefficient n d x.1 q hd j x.2|) ≤
      2 * Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        (priorK n) (16 * (n : ℝ) * priorB n) := by
  classical
  rw [tsum_countTaylor_eq_degree (I := Obs d)
    (fun t counts => |pairMarkedTaylorCoefficient n d t q hd j counts|)
    (pairMarkedTaylorCoefficient_joint_summable n d q hn hd hq j)]
  exact pairMarkedTaylorCoefficient_degree_tsum_le_factorial_tail n d q hn hd hq j

/-- The one-pair mixture likelihood on the full observed count alphabet,
including the zero rates outside that pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedMixtureFactor
noncomputable def pairMarkedMixtureFactor (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  ∑ z : Latent n, latentWeight n z * Real.exp (-8 * (n : ℝ) * latentP n z) *
    ∑ base : Bool, (1 / 2 : ℝ) *
      ∏ o : Obs d, pairMarkedIntensity n d q σ (latentZ n z) (latentP n z)
        hd j base o ^ counts o / (counts o).factorial

/-- For [a positive covariate dimension](hyp:hd) and [a count vector supported on the selected pair](hyp:hs), [the full-alphabet pair mixture likelihood equals its local counterpart](goal). -/
-- @node: pairMarkedMixtureFactor_eq_local_of_supported
lemma pairMarkedMixtureFactor_eq_local_of_supported (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hs : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0) :
    pairMarkedMixtureFactor n d q σ hd j counts =
      pairMixtureFactor n d q σ hd j counts := by
  unfold pairMarkedMixtureFactor pairMixtureFactor
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [pairMarkedIntensity_prod_eq_local_of_supported n d q σ
    (latentZ n z) (latentP n z) hd j _ counts hs]
  rw [← half_pairBlockMarkAverage_eq_average_localFactor]
  ring

/-- A count at a zero-rate atom makes the full pair likelihood vanish. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `o`](hyp:o), [the specified input `ho`](hyp:ho), [the specified input `hc`](hyp:hc), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedMixtureFactor_eq_zero_of_unsupported
lemma pairMarkedMixtureFactor_eq_zero_of_unsupported (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (o : Obs d) (ho : ∀ side : Bool, o.X ≠ pairLabel n d hd j side)
    (hc : counts o ≠ 0) :
    pairMarkedMixtureFactor n d q σ hd j counts = 0 := by
  unfold pairMarkedMixtureFactor
  simp_rw [pairMarkedIntensity_prod_eq_zero_of_unsupported
    n d q σ _ _ hd j _ counts o ho hc]
  simp

/-- The full marked likelihood gap is the sum of its Taylor coefficients;
unsupported count vectors have both sides zero. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedMixtureFactor_gap_hasSum
lemma pairMarkedMixtureFactor_gap_hasSum (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    HasSum (fun t => pairMarkedTaylorCoefficient n d t q hd j counts)
      (pairMarkedMixtureFactor n d q (-1) hd j counts -
        pairMarkedMixtureFactor n d q 1 hd j counts) := by
  classical
  by_cases hs : ∀ o : Obs d, (∀ side : Bool, o.X ≠ pairLabel n d hd j side) →
      counts o = 0
  · simp_rw [pairMarkedTaylorCoefficient_eq_local_of_supported n d _ q hd j counts hs]
    rw [pairMarkedMixtureFactor_eq_local_of_supported n d q (-1) hd j counts hs,
      pairMarkedMixtureFactor_eq_local_of_supported n d q 1 hd j counts hs]
    exact pairMixtureFactor_gap_hasSum n d q hd j counts
  · push Not at hs
    obtain ⟨o, ho, hc⟩ := hs
    simp_rw [pairMarkedTaylorCoefficient_eq_zero_of_unsupported n d _ q hd j counts o ho hc]
    rw [pairMarkedMixtureFactor_eq_zero_of_unsupported n d q (-1) hd j counts o ho hc,
      pairMarkedMixtureFactor_eq_zero_of_unsupported n d q 1 hd j counts o ho hc, sub_self]
    exact hasSum_zero

/-- The one-pair likelihood gap is bounded by the absolute coefficient series. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
-- @node: pairMarkedMixtureFactor_gap_abs_le_tsum
lemma pairMarkedMixtureFactor_gap_abs_le_tsum (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |pairMarkedMixtureFactor n d q (-1) hd j counts -
        pairMarkedMixtureFactor n d q 1 hd j counts| ≤
      ∑' t : ℕ, |pairMarkedTaylorCoefficient n d t q hd j counts| := by
  have hs := pairMarkedMixtureFactor_gap_hasSum n d q hd j counts
  rw [← hs.tsum_eq]
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.summable.norm

/-- Summing every count vector yields the paper's one-pair L1 bound. The
matched moments have already canceled before any absolute summation. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
-- @node: pairMarkedMixtureFactor_l1_le_factorial_tail
lemma pairMarkedMixtureFactor_l1_le_factorial_tail (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) :
    (∑' counts : Obs d → ℕ,
      |pairMarkedMixtureFactor n d q (-1) hd j counts -
        pairMarkedMixtureFactor n d q 1 hd j counts|) ≤
      2 * Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        (priorK n) (16 * (n : ℝ) * priorB n) := by
  have hs := pairMarkedTaylorCoefficient_joint_summable n d q hn hd hq j
  have ht : Summable (fun x : (Obs d → ℕ) × ℕ =>
      |pairMarkedTaylorCoefficient n d x.2 q hd j x.1|) :=
    hs.prod_symm
  have he := ht.prod
  have hpoint := pairMarkedMixtureFactor_gap_abs_le_tsum n d q hd j
  have hg : Summable (fun counts : Obs d → ℕ =>
      |pairMarkedMixtureFactor n d q (-1) hd j counts -
        pairMarkedMixtureFactor n d q 1 hd j counts|) :=
    Summable.of_nonneg_of_le
      (fun counts => abs_nonneg (pairMarkedMixtureFactor n d q (-1) hd j counts -
        pairMarkedMixtureFactor n d q 1 hd j counts)) hpoint he
  calc
    _ ≤ ∑' counts : Obs d → ℕ,
        ∑' t : ℕ, |pairMarkedTaylorCoefficient n d t q hd j counts| :=
      hg.tsum_le_tsum hpoint he
    _ = ∑' x : ℕ × (Obs d → ℕ),
        |pairMarkedTaylorCoefficient n d x.1 q hd j x.2| := by
      rw [← ht.tsum_prod]
      exact (Equiv.prodComm (Obs d → ℕ) ℕ).tsum_eq
        (fun x : ℕ × (Obs d → ℕ) => |pairMarkedTaylorCoefficient n d x.1 q hd j x.2|)
    _ ≤ _ := pairMarkedTaylorCoefficient_joint_tsum_le_factorial_tail n d q hn hd hq j

end CausalSmith.Stat.MarNearcompleteFrontier
