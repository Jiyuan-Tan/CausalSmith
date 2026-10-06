module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.PilotTails
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamBiasRates

/-!
# Heavy-branch empty-count bias

The second remainder in equation (12) is exponentially small uniformly in
the arrived-cell rate. Summing against missing mass gives its contribution
to equation (14), without a factor depending on the alphabet size.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory
open scoped BigOperators

/-- The logarithmic tilt used for pilot selection is at least one. [the stated mathematical conclusion holds](goal). -/
-- @node: upper_log_four_ge_one
lemma upper_log_four_ge_one : 1 ≤ Real.log (4 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hp := Real.log_pow (2 : ℝ) 2
  norm_num at h hp
  linarith

/-- Splitting at one sixteenth of the threshold makes the heavy-branch
empty-count remainder uniformly exponentially small. Given [the specified input `B`](hyp:B), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hB`](hyp:hB), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). Given [the specified input `htail`](hyp:htail). -/
-- @node: upper_heavy_empty_remainder_le
lemma upper_heavy_empty_remainder_le {B z p : ℝ}
    (hB : 0 ≤ B) (hp : p ∈ Set.Icc 0 1)
    (htail : 1 - p ≤ Real.exp (3 * z - B * Real.log 4 / 4)) :
    (1 - p) * Real.exp (-z) ≤ Real.exp (-B / 16) := by
  by_cases hz : B / 16 ≤ z
  · calc
      (1 - p) * Real.exp (-z) ≤ 1 * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right (by linarith [hp.1]) (Real.exp_pos _).le
      _ ≤ Real.exp (-B / 16) := by
        rw [one_mul]
        exact Real.exp_le_exp.mpr (by linarith)
  · have hlog := mul_le_mul_of_nonneg_left upper_log_four_ge_one hB
    calc
      (1 - p) * Real.exp (-z) ≤
          Real.exp (3 * z - B * Real.log 4 / 4) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
      _ = Real.exp (2 * z - B * Real.log 4 / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-B / 16) := Real.exp_le_exp.mpr (by nlinarith)

/-- The heavy empty-count part of the selected correction bias is uniformly
bounded at every cell, including null cells. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_heavy_empty_remainder_le
lemma upper_stream_heavy_empty_remainder_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (1 - streamPilotLightProb n P x a s) *
      Real.exp (-streamZ n P x a s) ≤ Real.exp (-polyThreshold n / 16) := by
  have he : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
    have h := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hL : 0 < ell n := Real.log_pos (by simpa [ell] using he)
  have hB : 0 ≤ polyThreshold n := by unfold polyThreshold; positivity
  exact upper_heavy_empty_remainder_le hB
    (upper_streamPilotLightProb_bounds P x a s)
    (upper_stream_pilot_heavy_tail P x a s)

/-- Summing the heavy empty-count remainder against missing cell mass costs
at most delta times exp of minus sixteen logarithmic sample scales. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_heavy_empty_bias_sum_rate
lemma upper_stream_heavy_empty_bias_sum_rate {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      missingCellMass P x a s * (1 - streamPilotLightProb n P x a s) *
        Real.exp (-streamZ n P x a s)) ≤
      delta q * Real.exp (-16 * ell n) := by
  calc
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        missingCellMass P x a s * Real.exp (-polyThreshold n / 16) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (upper_stream_heavy_empty_remainder_le P x a s)
        ((missingCellMass_bounds P h hq x a s).1)
    _ = (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        missingCellMass P x a s) * Real.exp (-polyThreshold n / 16) := by
      simp only [Finset.sum_mul]
    _ ≤ delta q * Real.exp (-polyThreshold n / 16) :=
      mul_le_mul_of_nonneg_right (sum_missingCellMass_le_delta P h hq)
        (Real.exp_pos _).le
    _ = delta q * Real.exp (-16 * ell n) := by
      unfold polyThreshold
      congr 2
      ring

/-- Multiplying a half-sum cell bias bound by twice the nonnegative missing
mass removes the one-half factor. Given [the specified input `w`](hyp:w), [the specified input `b`](hyp:b), [the specified input `u`](hyp:u), [the specified input `v`](hyp:v), [the specified input `hw`](hyp:hw), [the stated mathematical conclusion holds](goal). Given [the specified input `hb`](hyp:hb). -/
-- @node: upper_missing_weight_half_bound
lemma upper_missing_weight_half_bound {w b u v : ℝ}
    (hw : 0 ≤ w) (hb : b ≤ (1 / 2 : ℝ) * (u + v)) :
    2 * (w * b) ≤ w * u + w * v := by
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * w by positivity)
  nlinarith only [hh]

/-- The signed correction bias is controlled by the pilot-weighted polynomial
remainder plus the now-bounded heavy empty-count remainder. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_pilot_bias_polynomial_sum_le
lemma upper_stream_pilot_bias_polynomial_sum_le {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * missingCellMass P x a s *
        ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
          cellEta P x a s))| ≤
      (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        missingCellMass P x a s * streamPilotLightProb n P x a s *
          |(qPoly n).eval (streamZ n P x a s)|) +
      delta q * Real.exp (-16 * ell n) := by
  have hcell : ∀ x : Fin d, ∀ a s : Bool,
      2 * (missingCellMass P x a s *
        |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
          cellEta P x a s|) ≤
      missingCellMass P x a s * streamPilotLightProb n P x a s *
          |(qPoly n).eval (streamZ n P x a s)| +
        missingCellMass P x a s * (1 - streamPilotLightProb n P x a s) *
          Real.exp (-streamZ n P x a s) := by
    intro x a s
    have hw := (missingCellMass_bounds P h hq x a s).1
    have hbound := upper_stream_pilot_bias_cell_abs_le (n := n) P h x a s
    have hh := upper_missing_weight_half_bound hw hbound
    simpa only [mul_assoc] using hh
  have hb := upper_stream_pilot_bias_abs_sum_le (n := n) P h hq
  simp only [Finset.mul_sum] at hb
  have hs : (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      2 * (missingCellMass P x a s *
        |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
          cellEta P x a s|)) ≤
      ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (missingCellMass P x a s * streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| +
          missingCellMass P x a s * (1 - streamPilotLightProb n P x a s) *
            Real.exp (-streamZ n P x a s)) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro s hs
    exact hcell x a s
  simp only [Finset.sum_add_distrib] at hs
  have he := upper_stream_heavy_empty_bias_sum_rate (n := n) P h hq
  simpa only [Finset.mul_sum] using hb.trans (hs.trans (add_le_add_right he _))

/-- In the nonfallback regime the only unbounded part of the signed bias
is the polynomial remainder on cells above the threshold. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_pilot_bias_large_cell_reduction
lemma upper_stream_pilot_bias_large_cell_reduction {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n)
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * missingCellMass P x a s *
        ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
          cellEta P x a s))| ≤
      268435456 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) +
      (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        if polyThreshold n < streamZ n P x a s then
          missingCellMass P x a s * streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| else 0) +
      delta q * Real.exp (-16 * ell n) := by
  classical
  have hsplit : (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      missingCellMass P x a s * streamPilotLightProb n P x a s *
        |(qPoly n).eval (streamZ n P x a s)|) =
      (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        if streamZ n P x a s ≤ polyThreshold n then
          missingCellMass P x a s * streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| else 0) +
      (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        if polyThreshold n < streamZ n P x a s then
          missingCellMass P x a s * streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hz : streamZ n P x a s ≤ polyThreshold n
    · simp only [hz, not_lt_of_ge hz, if_true, if_false, add_zero]
    · simp only [hz, lt_of_not_ge hz, if_true, if_false, zero_add]
  have hb := upper_stream_pilot_bias_polynomial_sum_le (n := n) P h hq
  rw [hsplit] at hb
  have hs := upper_small_cell_pilot_bias_sum_rate hn hL P h hq
  linarith only [hb, hs]

end CausalSmith.Stat.MarNearcompleteFrontier
