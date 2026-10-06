module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamVarianceRates

/-!
# Variance budget for the selected cell correction

The heavy product and pilot-selected remainder decomposition combines equation
(16) with equations (17)--(19), without assuming independence of the branches.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The variance of a sum is at most twice the sum of its variances, even
when the two square-integrable terms are dependent. Given [the specified input `X`](hyp:X), [the specified input `Y`](hyp:Y), [the specified input `hX`](hyp:hX), [the specified input `hY`](hyp:hY), [the stated mathematical conclusion holds](goal). Given [the specified input `Ω`](hyp:Ω), [the specified input `μ`](hyp:μ). -/
-- @node: upper_variance_add_le_twice
lemma upper_variance_add_le_twice {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω + Y ω) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  have hp := variance_fun_add hX hY
  have hm := variance_fun_sub hX hY
  have hn := variance_nonneg (X := fun ω => X ω - Y ω) (μ := μ)
  linarith

/-- The pilot-selected remainder is square integrable by the previously
proved product-square domination. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_sub_VD_memLp_two
lemma upper_streamVG_sub_VD_memLp_two {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    MemLp (fun streams => streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) 2 (fourStreamLaw n P) := by
  have hv := (upper_streamV_memLp_two (n := n) P x a s).aestronglyMeasurable
  have hg := (upper_measurable_streamG (n := n) x a s).aestronglyMeasurable
    (μ := fourStreamLaw n P)
  have hd := (upper_measurable_streamD x a s).aestronglyMeasurable
    (μ := fourStreamLaw n P)
  exact (memLp_two_iff_integrable_sq (hv.mul (hg.sub hd))).mpr
    (upper_streamVG_sub_VD_sq_integrable hn P x a s)

/-- The full selected missing-membership correction is square integrable,
since it is the sum of the heavy product and selected remainder. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_memLp_two
lemma upper_streamVG_memLp_two {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    MemLp (fun streams => streamV n d streams x a s * streamG n d streams x a s)
      2 (fourStreamLaw n P) := by
  convert (upper_streamVD_memLp_two (n := n) P x a s).add
    (upper_streamVG_sub_VD_memLp_two hn P x a s) using 1
  ext streams
  simp only [Pi.add_apply]
  ring

/-- Splitting off the heavy branch bounds the selected cell variance by twice
the heavy variance plus twice the selected remainder's second moment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_variance_le
lemma upper_streamVG_variance_le {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    variance (fun streams => streamV n d streams x a s * streamG n d streams x a s)
      (fourStreamLaw n P) ≤
      2 * variance (fun streams => streamV n d streams x a s * streamD d streams x a s)
        (fourStreamLaw n P) +
      2 * (∫ streams, (streamV n d streams x a s *
        (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hd := upper_streamVD_memLp_two (n := n) P x a s
  have hr := upper_streamVG_sub_VD_memLp_two hn P x a s
  have hsplit : (fun streams => streamV n d streams x a s * streamG n d streams x a s) =
      (fun streams => streamV n d streams x a s * streamD d streams x a s +
        streamV n d streams x a s *
          (streamG n d streams x a s - streamD d streams x a s)) := by
    ext streams
    ring
  rw [hsplit]
  exact (upper_variance_add_le_twice hd hr).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (variance_le_expectation_sq hr.aestronglyMeasurable) (by norm_num : (0 : ℝ) ≤ 2)) _)

/-- The sum of selected cell variances has the squared-bias scale and a
universal inverse-sample-size budget obtained from equations (16)--(19). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_streamVG_variance_sum_rate
lemma upper_streamVG_variance_sum_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      variance (fun streams => streamV n d streams x a s * streamG n d streams x a s)
        (fourStreamLaw n P)) ≤
      (delta q * (d : ℝ) / ((n : ℝ) * ell n)) ^ 2 +
        ((201719808 : ℝ) ^ 2 *
          ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) + 118) / (n : ℝ) := by
  calc
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (2 * variance (fun streams => streamV n d streams x a s * streamD d streams x a s)
          (fourStreamLaw n P) +
        2 * (∫ streams, (streamV n d streams x a s *
          (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      exact upper_streamVG_variance_le hn P x a s
    _ = 2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        variance (fun streams => streamV n d streams x a s * streamD d streams x a s)
          (fourStreamLaw n P)) +
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (∫ streams, (streamV n d streams x a s *
          (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (34 / (n : ℝ)) +
      2 * ((delta q * (d : ℝ) / ((n : ℝ) * ell n)) ^ 2 / 2 +
        ((201719808 : ℝ) ^ 2 *
          ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) / 2 + 25) / (n : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (upper_streamVD_variance_sum_le hn P h hq) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (upper_stream_correction_second_moment_sum_rate hn hL P h hq) (by norm_num))
    _ = _ := by ring

end CausalSmith.Stat.MarNearcompleteFrontier
