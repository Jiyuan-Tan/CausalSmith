module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.CompleteArrivalRisk
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRawMean
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamTransfer

/-!
# Squared-risk assembly for the four-stream estimator

Bias, projection, capping and averaging reduce the nonfallback upper bound to
one remaining quantity: the variance of the aggregate signed cell correction.
The aggregate is retained explicitly until cross-cell independence is proved.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The uncapped estimator's squared risk is its variance plus squared bias. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fourStreamRawEstimate_risk_eq
lemma upper_fourStreamRawEstimate_risk_eq {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    (∫ streams, (fourStreamRawEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) =
      variance (fourStreamRawEstimate n d) (fourStreamLaw n P) +
      ((∫ streams, fourStreamRawEstimate n d streams ∂fourStreamLaw n P) - tau P) ^ 2 := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hX := upper_fourStreamRawEstimate_memLp_two hn P
  have hshift := hX.sub (memLp_const (tau P))
  have hv := variance_eq_sub hshift
  change variance (fun streams => fourStreamRawEstimate n d streams - tau P)
    (fourStreamLaw n P) = (∫ streams, (fourStreamRawEstimate n d streams - tau P) ^ 2
      ∂fourStreamLaw n P) -
      (∫ streams, fourStreamRawEstimate n d streams - tau P ∂fourStreamLaw n P) ^ 2 at hv
  rw [variance_sub_const hX.aestronglyMeasurable] at hv
  rw [integral_sub (hX.integrable (by norm_num)) (integrable_const _), integral_const] at hv
  simpa only [Pi.pow_apply, probReal_univ, one_smul] using
    (eq_add_of_sub_eq hv.symm)

/-- Projection cannot increase squared risk, since the target is in the
projection interval and the raw estimator has a finite second moment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fourStreamEstimate_risk_le_raw
lemma upper_fourStreamEstimate_risk_le_raw {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    (∫ streams, (fourStreamEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) ≤
      (∫ streams, (fourStreamRawEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hraw := (upper_fourStreamRawEstimate_memLp_two hn P).sub (memLp_const (tau P))
  have hi := (memLp_two_iff_integrable_sq hraw.aestronglyMeasurable).mp hraw
  have hpoint (streams) : (fourStreamEstimate n d streams - tau P) ^ 2 ≤
      (fourStreamRawEstimate n d streams - tau P) ^ 2 := by
    have hc := clipUnit_contracts (fourStreamRawEstimate n d streams) (tau P) (tau_range P)
    change |fourStreamEstimate n d streams - tau P| ≤
      |fourStreamRawEstimate n d streams - tau P| at hc
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hc 2
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  · exact hi
  · exact Filter.Eventually.of_forall hpoint

/-- Below the dimension fallback threshold the rate has the untruncated
squared-bias scale used in equations (19)--(20). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `q`](hyp:q), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hd`](hyp:hd). -/
-- @node: upper_nonfallback_rate_eq
lemma upper_nonfallback_rate_eq {n d : ℕ} (hn : 0 < n) (hL : 128 ≤ ell n)
    (q : ℝ) (hd : (d : ℝ) < (n : ℝ) * ell n) :
    rate n d q = 1 / (n : ℝ) +
      (delta q * (d : ℝ) / ((n : ℝ) * ell n)) ^ 2 := by
  have hden : 0 < (n : ℝ) * ell n := mul_pos (by positivity) (by linarith)
  have hr : (d : ℝ) / ((n : ℝ) * ell n) ≤ 1 :=
    (div_le_one hden).mpr hd.le
  simp only [rate, gScale, min_eq_right hr, mul_div_assoc]

/-- The exponentially small pilot-bias remainder has a squared
inverse-sample-size budget. Given [the specified input `n`](hyp:n), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_pilot_bias_remainder_sq_le
lemma upper_pilot_bias_remainder_sq_le {n : ℕ} {q : ℝ} (hn : 0 < n)
    (hL : 128 ≤ ell n) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (4 * delta q * Real.exp (-16 * ell n)) ^ 2 ≤ 4 / (n : ℝ) := by
  have hδ : 0 ≤ delta q ∧ delta q ≤ 1 / 2 := by
    unfold delta
    constructor <;> linarith [hq.1, hq.2]
  have he : (Real.exp (-16 * ell n)) ^ 2 = Real.exp (-32 * ell n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ht : Real.exp (-32 * ell n) ≤ Real.exp (-ell n) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnR : 0 < (n : ℝ) := by positivity
  have ht' : Real.exp (-ell n) ≤ 1 / (n : ℝ) := by
    rw [Real.exp_neg, ell, Real.exp_log (by positivity)]
    simpa only [one_div] using inv_anti₀ hnR
      (le_add_of_nonneg_left (Real.exp_pos 1).le)
  calc
    _ = 16 * (delta q) ^ 2 * Real.exp (-32 * ell n) := by rw [← he]; ring
    _ ≤ 4 * Real.exp (-32 * ell n) := by
      have hs : (delta q) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hδ.1 hδ.2 2
      nlinarith [Real.exp_pos (-32 * ell n)]
    _ ≤ 4 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left (ht.trans ht') (by norm_num)
    _ = _ := by ring

/-- The raw estimator's squared bias has the claimed nonfallback rate,
using the established pilot-bias bound and its exponential remainder. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hd`](hyp:hd), [the specified input `hq`](hyp:hq). -/
-- @node: upper_fourStreamRawEstimate_bias_sq_rate
lemma upper_fourStreamRawEstimate_bias_sq_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (hd : (d : ℝ) < (n : ℝ) * ell n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ((∫ streams, fourStreamRawEstimate n d streams ∂fourStreamLaw n P) - tau P) ^ 2 ≤
      (2 * (268435456 : ℝ) ^ 2 + 8) * rate n d q := by
  let x := delta q * (d : ℝ) / ((n : ℝ) * ell n)
  let b := 4 * delta q * Real.exp (-16 * ell n)
  have hx : 0 ≤ x := by
    have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
    dsimp [x]
    positivity
  have hb : 0 ≤ b := by
    have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
    dsimp [b]
    positivity
  have hbound := upper_fourStreamRawEstimate_bias_le hn hL P h hq
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have hrem : b ^ 2 ≤ 4 / (n : ℝ) := upper_pilot_bias_remainder_sq_le hn hL hq
  rw [upper_nonfallback_rate_eq hn hL q hd]
  change _ ≤ (2 * (268435456 : ℝ) ^ 2 + 8) * (1 / (n : ℝ) + x ^ 2)
  change _ ≤ (268435456 * x + b) ^ 2 at hsq
  rw [sq_abs] at hsq
  have hrem' : b ^ 2 ≤ 4 * (1 / (n : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul] using hrem
  nlinarith only [hsq, hrem', sq_nonneg (268435456 * x - b), sq_nonneg x,
    (show 0 ≤ 1 / (n : ℝ) by positivity)]

/-- The aggregate signed correction is square integrable by the finite
sum of the already established cell product moments. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamCorrectionSum_memLp_two
lemma upper_streamCorrectionSum_memLp_two {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    MemLp (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * streamCellCorrection n d streams x a s)
      2 (fourStreamLaw n P) := by
  apply memLp_finsetSum
  intro x hx
  apply memLp_finsetSum
  intro a ha
  apply memLp_finsetSum
  intro s hs
  exact (upper_streamVG_memLp_two hn P x a s).const_mul (treatmentSign a)

/-- The raw estimator variance is controlled by the first stream and the
aggregate correction; this step does not require independence between them. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fourStreamRawEstimate_variance_le_aggregate
lemma upper_fourStreamRawEstimate_variance_le_aggregate {n d : ℕ}
    (hn : 0 < n) (P : FullLaw d) :
    variance (fourStreamRawEstimate n d) (fourStreamLaw n P) ≤
      64 / (n : ℝ) + 8 * variance
        (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          treatmentSign a * streamCellCorrection n d streams x a s)
        (fourStreamLaw n P) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hsum := upper_streamCorrectionSum_memLp_two hn P
  have heq : fourStreamRawEstimate n d = fun streams => upper_streamLinear n d streams +
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * streamCellCorrection n d streams x a s) := by
    ext streams
    exact upper_fourStreamRawEstimate_eq_linear_add streams
  rw [heq]
  have hv := upper_variance_add_le_twice (upper_streamLinear_memLp_two (n := n) P)
    (hsum.const_mul 2)
  simp only [variance_const_mul] at hv
  have hl := upper_streamLinear_variance_le hn P
  simp only [div_eq_mul_inv] at hl ⊢
  norm_num only at hv
  linarith

/-- In the nonfallback regime, projection and the proved bias and linear
variance budgets leave only the aggregate correction variance to control. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hd`](hyp:hd), [the specified input `hq`](hyp:hq). -/
-- @node: upper_fourStreamEstimate_risk_le_aggregate
lemma upper_fourStreamEstimate_risk_le_aggregate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (hd : (d : ℝ) < (n : ℝ) * ell n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∫ streams, (fourStreamEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) ≤
      8 * variance
        (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          treatmentSign a * streamCellCorrection n d streams x a s)
        (fourStreamLaw n P) + (2 * (268435456 : ℝ) ^ 2 + 72) * rate n d q := by
  have hp := upper_fourStreamEstimate_risk_le_raw hn P
  rw [upper_fourStreamRawEstimate_risk_eq hn P] at hp
  have hv := upper_fourStreamRawEstimate_variance_le_aggregate hn P
  have hb := upper_fourStreamRawEstimate_bias_sq_rate hn hL hd P h hq
  have hr : 1 / (n : ℝ) ≤ rate n d q := by
    exact le_add_of_nonneg_right (sq_nonneg (gScale n d q))
  have hr' : 64 / (n : ℝ) ≤ 64 * rate n d q := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 64)
  linarith

/-- Capping and averaging preserve the risk reduction to aggregate correction
variance, paying only the already proved inverse-sample-size cap penalty. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `hqne`](hyp:hqne), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hreg`](hyp:hreg). -/
-- @node: upper_nonfallback_risk_le_aggregate
lemma upper_nonfallback_risk_le_aggregate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hqne : q ≠ 1)
    (hreg : ¬(ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n)) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      8 * variance
        (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          treatmentSign a * streamCellCorrection n d streams x a s)
        (fourStreamLaw n P) + (2 * (268435456 : ℝ) ^ 2 + 104) * rate n d q := by
  have hL : 128 ≤ ell n := le_of_not_gt (fun hh => hreg (Or.inl hh))
  have hd : (d : ℝ) < (n : ℝ) * ell n := lt_of_not_ge (fun hh => hreg (Or.inr hh))
  have hc := upper_nonfallback_risk_le_ideal_add_rate hn q P hqne hreg
  have hi := upper_fourStreamEstimate_risk_le_aggregate hn hL hd P h hq
  have hr : 1 / (n : ℝ) ≤ rate n d q :=
    le_add_of_nonneg_right (sq_nonneg (gScale n d q))
  have hr' : 32 / (n : ℝ) ≤ 32 * rate n d q := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 32)
  linarith

end CausalSmith.Stat.MarNearcompleteFrontier
