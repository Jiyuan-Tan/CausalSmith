module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLargeVariance

/-!
# Absorbing the correction variance into the frontier rate

Equation (19) follows from the sixth Taylor term of the exponential and
Young's inequality. These bounds retain the exact exponential logarithmic
scale of equation (17), avoiding an unnecessary approximation by n^(1/8).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory
open scoped BigOperators

/-- The sixth logarithmic power is dominated by an exponential with exponent
three quarters, with a fixed numerical constant. Given [the specified input `L`](hyp:L), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_log_sixth_exp_bound
lemma upper_log_sixth_exp_bound {L : ℝ} (hL : 0 ≤ L) :
    L ^ 6 ≤ (720 * (4 / 3 : ℝ) ^ 6) * Real.exp (3 * L / 4) := by
  have ht := Real.pow_div_factorial_le_exp (3 * L / 4) (show 0 ≤ 3 * L / 4 by positivity) 6
  norm_num [Nat.factorial] at ht
  nlinarith only [ht]

/-- The exponential of the sample logarithm is at most a fixed multiple of
sample size, including the smallest positive sample size. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_exp_ell_le_sample
lemma upper_exp_ell_le_sample {n : ℕ} (hn : 0 < n) :
    Real.exp (ell n) ≤ (Real.exp 1 + 1) * (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [ell, Real.exp_log (by positivity)]
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- Squaring the factor paired with the bias scale in equation (19) costs
only a universal multiple of inverse sample size. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_variance_log_factor_sq_le
lemma upper_variance_log_factor_sq_le {n : ℕ} (hn : 0 < n)
    (hL : 0 ≤ ell n) :
    (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ)) ^ 2 ≤
      ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hp := mul_le_mul_of_nonneg_left (upper_log_sixth_exp_bound hL)
    (Real.exp_pos (ell n / 4)).le
  have he : Real.exp (ell n / 4) * Real.exp (3 * ell n / 4) =
      Real.exp (ell n) := by rw [← Real.exp_add]; congr 1; ring
  have hs : (Real.exp (ell n / 8)) ^ 2 = Real.exp (ell n / 4) := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  calc
    _ = Real.exp (ell n / 4) * (ell n) ^ 6 / (n : ℝ) ^ 2 := by rw [← hs]; ring
    _ ≤ (720 * (4 / 3 : ℝ) ^ 6) * Real.exp (ell n) / (n : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      calc
        _ ≤ Real.exp (ell n / 4) *
            ((720 * (4 / 3 : ℝ) ^ 6) * Real.exp (3 * ell n / 4)) := hp
        _ = _ := by rw [mul_left_comm, he]
    _ ≤ (720 * (4 / 3 : ℝ) ^ 6) * ((Real.exp 1 + 1) * (n : ℝ)) /
        (n : ℝ) ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (upper_exp_ell_le_sample hn) (by positivity))
      (sq_nonneg _)
    _ = _ := by field_simp

/-- Young's inequality absorbs any fixed multiple of the nonparametric
correction term into squared bias and inverse sample size. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `A`](hyp:A), [the specified input `x`](hyp:x), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_variance_cross_term_le
lemma upper_variance_cross_term_le {n : ℕ} (hn : 0 < n)
    (hL : 0 ≤ ell n) (A x : ℝ) :
    A * x * (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ)) ≤
      x ^ 2 / 2 +
        (A ^ 2 * ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) / 2) / (n : ℝ) := by
  have hb := mul_le_mul_of_nonneg_left (upper_variance_log_factor_sq_le hn hL)
    (sq_nonneg A)
  have hy := sq_nonneg (x - A * (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ)))
  have hb' : (A * (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ))) ^ 2 / 2 ≤
      (A ^ 2 * ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) / 2) / (n : ℝ) := by
    convert mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1 <;>
      first | rfl | ring
  calc
    _ ≤ x ^ 2 / 2 + (A * (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ))) ^ 2 / 2 :=
      by nlinarith only [hy]
    _ ≤ _ := add_le_add_right hb' _

/-- The explicit small-cell envelope in equation (17) factors into the bias
scale times the logarithmic factor controlled by equation (19). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_small_variance_envelope_le
lemma upper_small_variance_envelope_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    12 * (d : ℝ) * Real.exp (ell n / 8) *
      ((4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 + 2 * delta q * polyThreshold n) /
        ((n : ℝ) / 8) ^ 2) ≤
      201719808 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) *
        (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hδ1 : delta q ≤ 1 := by unfold delta; linarith [hq.1]
  have hδsq : (delta q) ^ 2 ≤ delta q := by nlinarith
  have hLpos : 0 < ell n := by linarith
  have hLsq : ell n ≤ (ell n) ^ 2 := by nlinarith
  have hquad := mul_le_mul_of_nonneg_right hδsq (sq_nonneg (ell n))
  have hlin := mul_le_mul_of_nonneg_left hLsq hδ
  have hnum : 4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 +
      2 * delta q * polyThreshold n ≤ 262656 * delta q * (ell n) ^ 2 := by
    unfold polyThreshold
    nlinarith only [hquad, hlin]
  calc
    _ ≤ 12 * (d : ℝ) * Real.exp (ell n / 8) *
        ((262656 * delta q * (ell n) ^ 2) / ((n : ℝ) / 8) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hnum (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp; ring

/-- Combining equations (17)--(19) bounds the full correction second-moment
budget by squared bias scale plus a universal inverse-sample-size term. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_correction_second_moment_sum_rate
lemma upper_stream_correction_second_moment_sum_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (∫ streams, (streamV n d streams x a s *
        (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)) ≤
      (delta q * (d : ℝ) / ((n : ℝ) * ell n)) ^ 2 / 2 +
        ((201719808 : ℝ) ^ 2 *
          ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) / 2 + 25) / (n : ℝ) := by
  have hsmall := upper_small_variance_envelope_le (d := d) hn hL hq
  have hcross := upper_variance_cross_term_le hn (by linarith : 0 ≤ ell n)
    201719808 (delta q * (d : ℝ) / ((n : ℝ) * ell n))
  calc
    _ ≤ _ := upper_stream_correction_second_moment_sum_le hn hL P h hq
    _ ≤ 201719808 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) *
        (Real.exp (ell n / 8) * (ell n) ^ 3 / (n : ℝ)) + 25 / (n : ℝ) :=
      add_le_add hsmall le_rfl
    _ ≤ ((delta q * (d : ℝ) / ((n : ℝ) * ell n)) ^ 2 / 2 +
        ((201719808 : ℝ) ^ 2 *
          ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) / 2) / (n : ℝ)) +
        25 / (n : ℝ) := add_le_add hcross le_rfl
    _ = _ := by ring

end CausalSmith.Stat.MarNearcompleteFrontier
