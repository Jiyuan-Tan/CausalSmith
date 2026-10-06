module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.LightExponentialBounds
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamHeavyBias

/-!
# Large-cell pilot bias and the aggregate bias rate

The light mean identity and its second moment suppress the large-cell
Chebyshev remainder, completing equation (14) of the upper-risk proof.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The square of the light correction's mean is bounded by its second moment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_mean_sq_le
lemma upper_streamH_mean_sq_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, streamH n d streams x a s ∂fourStreamLaw n P) ^ 2 ≤
      ∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hLp := (memLp_two_iff_integrable_sq
    (upper_measurable_streamH x a s).aestronglyMeasurable).mpr
      (upper_streamH_sq_integrable (n := n) P x a s)
  have hv := variance_nonneg (fun streams => streamH n d streams x a s)
    (fourStreamLaw n P)
  rw [variance_eq_sub hLp] at hv
  exact sub_nonneg.mp hv

/-- In a large cell, the pilot lower tail decays at least as exp(-z/4). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_pilot_large_prob_le
lemma upper_stream_pilot_large_prob_le {n d : ℕ} (hL : 128 ≤ ell n)
    (P : FullLaw d) (x : Fin d) (a s : Bool)
    (hzB : polyThreshold n ≤ streamZ n P x a s) :
    streamPilotLightProb n P x a s ≤ Real.exp (-streamZ n P x a s / 4) := by
  apply (upper_stream_pilot_light_tail (n := n) P x a s).trans
  apply Real.exp_le_exp.mpr
  have hB : 0 ≤ polyThreshold n := by unfold polyThreshold; linarith
  have hh := mul_le_mul_of_nonneg_left upper_log_bases_le.2 hB
  linarith

/-- Pilot weighting makes the absolute light mean decay at exp(-z/16),
by the mean-square inequality and equation (11). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_pilot_large_mean_abs_le
lemma upper_streamH_pilot_large_mean_abs_le {n d : ℕ} (hL : 128 ≤ ell n)
    (P : FullLaw d) (x : Fin d) (a s : Bool)
    (hzB : polyThreshold n ≤ streamZ n P x a s) :
    streamPilotLightProb n P x a s *
      |∫ streams, streamH n d streams x a s ∂fourStreamLaw n P| ≤
      Real.exp (-streamZ n P x a s / 16) := by
  let p := streamPilotLightProb n P x a s
  let M := ∫ streams, streamH n d streams x a s ∂fourStreamLaw n P
  let E := ∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P
  have hp := upper_streamPilotLightProb_bounds (n := n) P x a s
  have hM : M ^ 2 ≤ E := upper_streamH_mean_sq_le P x a s
  have hE : p * E ≤ Real.exp (-streamZ n P x a s / 8) :=
    upper_streamH_pilot_large_second_moment_le hL P x a s hzB
  have hp2 : p ^ 2 ≤ p := by dsimp [p]; nlinarith [hp.1, hp.2]
  have hEn : 0 ≤ E := (sq_nonneg M).trans hM
  have hs : (p * |M|) ^ 2 ≤ Real.exp (-streamZ n P x a s / 8) := by
    calc
      (p * |M|) ^ 2 = p ^ 2 * M ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ p ^ 2 * E := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
      _ ≤ p * E := mul_le_mul_of_nonneg_right hp2 hEn
      _ ≤ _ := hE
  have hexp : Real.exp (-streamZ n P x a s / 16) ^ 2 =
      Real.exp (-streamZ n P x a s / 8) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change p * |M| ≤ _
  nlinarith [Real.exp_pos (-streamZ n P x a s / 16)]

/-- Equation (5) turns the light mean bound into a bound for the actual
centered Chebyshev remainder, without division by the centered regression. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_large_centered_qPoly_le
lemma upper_stream_large_centered_qPoly_le {n d : ℕ} {q : ℝ}
    (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (x : Fin d) (a s : Bool)
    (hzB : polyThreshold n ≤ streamZ n P x a s) :
    streamPilotLightProb n P x a s *
      |cellEta P x a s * (qPoly n).eval (streamZ n P x a s)| ≤
      (3 / 2 : ℝ) * Real.exp (-polyThreshold n / 16) := by
  let p := streamPilotLightProb n P x a s
  let M := ∫ streams, streamH n d streams x a s ∂fourStreamLaw n P
  have hrepr : cellEta P x a s * (qPoly n).eval (streamZ n P x a s) =
      cellEta P x a s - M := by
    dsimp [M]
    rw [upper_stream_light_mean P h x a s]
    ring
  have hp0 : 0 ≤ p := (upper_streamPilotLightProb_bounds P x a s).1
  have hz0 : 0 ≤ streamZ n P x a s := by
    have hB : 0 ≤ polyThreshold n := by unfold polyThreshold; linarith
    exact hB.trans hzB
  have hprob : p ≤ Real.exp (-polyThreshold n / 16) :=
    (upper_stream_pilot_large_prob_le hL P x a s hzB).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hmean : p * |M| ≤ Real.exp (-polyThreshold n / 16) :=
    (upper_streamH_pilot_large_mean_abs_le hL P x a s hzB).trans
      (Real.exp_le_exp.mpr (by linarith))
  rw [hrepr]
  change p * |cellEta P x a s - M| ≤ _
  calc
    _ ≤ p * (|cellEta P x a s| + |M|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hp0
    _ ≤ p * (1 / 2) + p * |M| := by
      have hh := mul_le_mul_of_nonneg_left (upper_cellEta_abs_le_half P x a s) hp0
      linarith
    _ ≤ _ := by linarith

/-- The absolute branch bias retains the centered regression in the
polynomial term, so the large-cell mean identity can be used directly. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_pilot_bias_centered_abs_le
lemma upper_stream_pilot_bias_centered_abs_le {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P) (x : Fin d) (a s : Bool) :
    |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
      cellEta P x a s| ≤
      streamPilotLightProb n P x a s *
        |cellEta P x a s * (qPoly n).eval (streamZ n P x a s)| +
      (1 / 2 : ℝ) * (1 - streamPilotLightProb n P x a s) *
        Real.exp (-streamZ n P x a s) := by
  let p := streamPilotLightProb n P x a s
  let Q := (qPoly n).eval (streamZ n P x a s)
  let e := Real.exp (-streamZ n P x a s)
  have hp := upper_streamPilotLightProb_bounds (n := n) P x a s
  change p ∈ Set.Icc 0 1 at hp
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hη := upper_cellEta_abs_le_half P x a s
  rw [upper_stream_pilot_bias P h x a s]
  change |-(cellEta P x a s) * (p * Q + (1 - p) * e)| ≤ _
  rw [show -(cellEta P x a s) * (p * Q + (1 - p) * e) =
    -(p * (cellEta P x a s * Q) + (1 - p) * e * cellEta P x a s) by ring,
    abs_neg]
  calc
    _ ≤ |p * (cellEta P x a s * Q)| + |(1 - p) * e * cellEta P x a s| :=
      abs_add_le _ _
    _ = p * |cellEta P x a s * Q| + (1 - p) * e * |cellEta P x a s| := by
      simp only [abs_mul, abs_of_nonneg hp.1,
        abs_of_nonneg (sub_nonneg.mpr hp.2), abs_of_nonneg he]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hη
        (mul_nonneg (sub_nonneg.mpr hp.2) he)
      dsimp only [p, Q, e] at *
      linarith

/-- Large-cell branch bias is exponentially small, including the
empty-count heavy remainder. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_pilot_large_bias_abs_le
lemma upper_stream_pilot_large_bias_abs_le {n d : ℕ} {q : ℝ}
    (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (x : Fin d) (a s : Bool)
    (hzB : polyThreshold n ≤ streamZ n P x a s) :
    |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
      cellEta P x a s| ≤ 2 * Real.exp (-polyThreshold n / 16) := by
  have hb := upper_stream_pilot_bias_centered_abs_le (n := n) P h x a s
  have hlight := upper_stream_large_centered_qPoly_le hL P h x a s hzB
  have hheavy := upper_stream_heavy_empty_remainder_le (n := n) P x a s
  linarith

/-- Each missing-mass-weighted bias has a small-cell polynomial budget and
an exponentially small residual, completing the cellwise split in (14). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_pilot_bias_split_weighted_le
lemma upper_stream_pilot_bias_split_weighted_le {n d : ℕ} {q : ℝ}
    (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (x : Fin d) (a s : Bool) :
    2 * (missingCellMass P x a s *
      |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
        cellEta P x a s|) ≤
      (if streamZ n P x a s ≤ polyThreshold n then
        missingCellMass P x a s * streamPilotLightProb n P x a s *
          |(qPoly n).eval (streamZ n P x a s)| else 0) +
      4 * missingCellMass P x a s * Real.exp (-polyThreshold n / 16) := by
  have hw := (missingCellMass_bounds P h hq x a s).1
  by_cases hz : streamZ n P x a s ≤ polyThreshold n
  · rw [if_pos hz]
    have hb := upper_missing_weight_half_bound hw
      (upper_stream_pilot_bias_cell_abs_le (n := n) P h x a s)
    have he := mul_le_mul_of_nonneg_left
      (upper_stream_heavy_empty_remainder_le (n := n) P x a s) hw
    have hn : 0 ≤ missingCellMass P x a s * Real.exp (-polyThreshold n / 16) :=
      mul_nonneg hw (Real.exp_pos _).le
    simp only [mul_assoc] at hb he ⊢
    linarith
  · rw [if_neg hz, zero_add]
    have hb := mul_le_mul_of_nonneg_left
      (upper_stream_pilot_large_bias_abs_le hL P h x a s (le_of_lt (lt_of_not_ge hz)))
      hw
    linarith

/-- Equation (14) for the actual pilot-selected correction: the signed
aggregate bias has the desired logarithmic rate plus exponential residual. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_pilot_bias_sum_rate
lemma upper_stream_pilot_bias_sum_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n)
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * missingCellMass P x a s *
        ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
          cellEta P x a s))| ≤
      268435456 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) +
      4 * delta q * Real.exp (-16 * ell n) := by
  classical
  have hb := upper_stream_pilot_bias_abs_sum_le (n := n) P h hq
  simp only [Finset.mul_sum] at hb
  have hs : (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      2 * (missingCellMass P x a s *
        |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
          cellEta P x a s|)) ≤
      ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        ((if streamZ n P x a s ≤ polyThreshold n then
          missingCellMass P x a s * streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| else 0) +
        4 * missingCellMass P x a s * Real.exp (-polyThreshold n / 16)) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro s hs
    exact upper_stream_pilot_bias_split_weighted_le hL P h hq x a s
  simp only [Finset.sum_add_distrib] at hs
  have hsmall := upper_small_cell_pilot_bias_sum_rate hn hL P h hq
  have hmass := sum_missingCellMass_le_delta P h hq
  have he : (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      4 * missingCellMass P x a s * Real.exp (-polyThreshold n / 16)) ≤
      4 * delta q * Real.exp (-16 * ell n) := by
    have hexp : -polyThreshold n / 16 = -16 * ell n := by
      unfold polyThreshold
      ring
    rw [hexp]
    calc
      _ = 4 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          missingCellMass P x a s) * Real.exp (-16 * ell n) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) (Real.exp_pos _).le
  simpa only [Finset.mul_sum] using hb.trans (hs.trans (add_le_add hsmall he))

end CausalSmith.Stat.MarNearcompleteFrontier
