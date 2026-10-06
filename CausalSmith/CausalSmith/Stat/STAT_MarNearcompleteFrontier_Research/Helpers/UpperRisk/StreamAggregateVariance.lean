module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCellIndependence

/-!
# Aggregate correction variance and nonfallback risk

Independence of distinct cells turns the selected cell variance sum into the
variance of the signed correction aggregate. This finishes the nonfallback risk budget.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Independence across cells identifies aggregate signed correction variance
with the sum of individual selected-product variances. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamCorrectionSum_variance_eq
lemma upper_streamCorrectionSum_variance_eq {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    variance (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * streamCellCorrection n d streams x a s) (fourStreamLaw n P) =
    ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      variance (fun streams => streamV n d streams x a s * streamG n d streams x a s)
        (fourStreamLaw n P) := by
  let X : (Fin d × Bool × Bool) → (Fin 4 → Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample (Obs d)) → ℝ :=
    fun j streams => treatmentSign j.2.1 *
      streamCellCorrection n d streams j.1 j.2.1 j.2.2
  have hm (j : Fin d × Bool × Bool) : MemLp (X j) 2 (fourStreamLaw n P) :=
    (upper_streamVG_memLp_two hn P j.1 j.2.1 j.2.2).const_mul _
  have hi : Set.Pairwise (↑(Finset.univ : Finset (Fin d × Bool × Bool)))
      (fun j k => IndepFun (X j) (X k) (fourStreamLaw n P)) := by
    intro j hj k hk hjk
    exact (upper_streamCellCorrection_indepFun P hjk).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hv := IndepFun.variance_sum (fun j _ => hm j) hi
  have hs (j : Fin d × Bool × Bool) : variance (X j) (fourStreamLaw n P) =
      variance (fun streams => streamV n d streams j.1 j.2.1 j.2.2 *
        streamG n d streams j.1 j.2.1 j.2.2) (fourStreamLaw n P) := by
    dsimp [X, streamCellCorrection]
    rw [variance_const_mul]
    have hsign : (treatmentSign j.2.1) ^ 2 = 1 := by
      cases j.2.1 <;> norm_num [treatmentSign]
    rw [hsign, one_mul]
  simp only [hs, Fintype.sum_prod_type] at hv
  simpa only [X, Finset.sum_fn, Finset.sum_apply] using hv

/-- The signed aggregate satisfies the universal selected-cell variance budget. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hd`](hyp:hd), [the specified input `hq`](hyp:hq). -/
-- @node: upper_streamCorrectionSum_variance_rate
lemma upper_streamCorrectionSum_variance_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (hd : (d : ℝ) < (n : ℝ) * ell n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    variance (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * streamCellCorrection n d streams x a s) (fourStreamLaw n P) ≤
      ((201719808 : ℝ) ^ 2 *
        ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) + 119) * rate n d q := by
  rw [upper_streamCorrectionSum_variance_eq hn P]
  have hv := upper_streamVG_variance_sum_rate hn hL P h hq
  rw [upper_nonfallback_rate_eq hn hL q hd]
  have hc : 0 ≤ (201719808 : ℝ) ^ 2 *
      ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) := by positivity
  have hi : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx := sq_nonneg (delta q * (d : ℝ) / ((n : ℝ) * ell n))
  simp only [div_eq_mul_inv, one_mul] at hv hc hi hx ⊢
  nlinarith only [hv, hx, hi, mul_nonneg hc hx]

/-- The nonfallback estimator has a universal risk constant after the
cross-cell variance, projection, capping, and averaging budgets are combined. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `hqne`](hyp:hqne), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hreg`](hyp:hreg). -/
-- @node: upper_nonfallback_risk_rate
lemma upper_nonfallback_risk_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hqne : q ≠ 1)
    (hreg : ¬(ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n)) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      (8 * ((201719808 : ℝ) ^ 2 *
        ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) + 119) +
        2 * (268435456 : ℝ) ^ 2 + 104) * rate n d q := by
  have hL : 128 ≤ ell n := le_of_not_gt (fun hh => hreg (Or.inl hh))
  have hd : (d : ℝ) < (n : ℝ) * ell n := lt_of_not_ge (fun hh => hreg (Or.inr hh))
  have ha := upper_nonfallback_risk_le_aggregate hn P h hq hqne hreg
  have hv := upper_streamCorrectionSum_variance_rate hn hL hd P h hq
  linarith

end CausalSmith.Stat.MarNearcompleteFrontier
