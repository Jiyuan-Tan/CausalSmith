module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorTuning

/-! # Integer-depth tuning for the sparse lower experiment

These estimates implement equations (46)--(50) of the common-kernel lower
bound: the ceiling depth meets the reference KL budget and loses at most one
factor of the mixing coefficient in the value gap.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- The small-information regime threshold in equation (46). -/
-- @node: lowerDepthThreshold
noncomputable def lowerDepthThreshold (t0 zeta B : ℝ) : ℝ :=
  min (1 / 4) (32 * B * Real.exp
    (-(2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))))

/-- The ceiling depth prescribed in equation (47). -/
-- @node: lowerTestingDepth
noncomputable def lowerTestingDepth (t0 zeta B q u : ℝ) : Nat :=
  Nat.ceil (Real.log (32 * B * q ^ 2 / u) /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)))

/-- The threshold is strictly positive for a positive KL constant. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the second event](hyp:B), and
[the second event assumption](hyp:hB), this establishes
[the lower depth threshold positivity result](goal). -/
-- @node: lowerDepthThreshold_pos
lemma lowerDepthThreshold_pos (t0 zeta B : ℝ) (hB : 0 < B) :
    0 < lowerDepthThreshold t0 zeta B := by
  unfold lowerDepthThreshold
  exact lt_min (by norm_num) (by positivity)

/-- In the hidden regime the unrounded depth is at least one. For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the second event](hyp:B), [the q](hyp:q),
[the observed prefix](hyp:u), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the second event assumption](hyp:_hB),
[the q assumption](hyp:_hq), [the observed prefix assumption](hyp:hu), and
[the small assumption](hyp:hsmall), this establishes
[the lower depth coordinate ge one result](goal). -/
-- @node: lower_depth_coordinate_ge_one
lemma lower_depth_coordinate_ge_one (t0 zeta B q u : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (_hB : 0 < B)
    (_hq : 0 < q) (hu : 0 < u)
    (hsmall : u ≤ lowerDepthThreshold t0 zeta B * q ^ 2) :
    1 ≤ Real.log (32 * B * q ^ 2 / u) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) := by
  let D := 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)
  have hD : 0 < D := selector_tuning_denominator_pos t0 zeta ht0 hzeta
  have hth : lowerDepthThreshold t0 zeta B ≤ 32 * B * Real.exp (-D) :=
    min_le_right _ _
  have hbound : u ≤ (32 * B * q ^ 2) * Real.exp (-D) := by
    have := hsmall.trans (mul_le_mul_of_nonneg_right hth (sq_nonneg q))
    nlinarith
  have hexp : Real.exp D ≤ 32 * B * q ^ 2 / u := by
    apply (le_div_iff₀ hu).mpr
    have := mul_le_mul_of_nonneg_right hbound (Real.exp_pos D).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
    nlinarith
  have hlog : D ≤ Real.log (32 * B * q ^ 2 / u) := by
    have := Real.log_le_log (Real.exp_pos D) hexp
    simpa only [Real.log_exp] using this
  exact (le_div_iff₀ hD).mpr (by simpa using hlog)

/-- The prescribed integer depth is admissible, and its rounding loss is at most one. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the second event](hyp:B),
[the q](hyp:q), [the observed prefix](hyp:u), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the second event assumption](hyp:hB),
[the q assumption](hyp:hq), [the observed prefix assumption](hyp:hu), and
[the small assumption](hyp:hsmall), this establishes
[the lower testing depth bounds result](goal). -/
-- @node: lower_testing_depth_bounds
lemma lower_testing_depth_bounds (t0 zeta B q u : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hB : 0 < B)
    (hq : 0 < q) (hu : 0 < u)
    (hsmall : u ≤ lowerDepthThreshold t0 zeta B * q ^ 2) :
    1 ≤ lowerTestingDepth t0 zeta B q u ∧
      (lowerTestingDepth t0 zeta B q u : ℝ) ≤
        Real.log (32 * B * q ^ 2 / u) /
          (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) + 1 := by
  have hx := lower_depth_coordinate_ge_one t0 zeta B q u ht0 hzeta hB hq hu hsmall
  constructor
  · have hc := Nat.le_ceil (Real.log (32 * B * q ^ 2 / u) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)))
    exact_mod_cast hx.trans hc
  · exact (Nat.ceil_lt_add_one (by linarith : 0 ≤
      Real.log (32 * B * q ^ 2 / u) /
        (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)))).le

/-- The product of the squared mixing power and inverse action factor is the exponential decay
appearing in equation (48). For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), and [the hidden-depth scale](hyp:Q), this establishes
[the lower information decay equality result](goal). -/
-- @node: lower_information_decay_eq
lemma lower_information_decay_eq (t0 zeta : ℝ) (Q : Nat) :
    mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ)) =
      Real.exp (-(2 * Real.log (1 / mixingAlpha t0) +
        Real.log (policyFactor zeta)) * (Q : ℝ)) := by
  rw [zpow_neg, zpow_natCast]
  simp only [mixingAlpha, policyFactor, one_div, Real.log_inv, Real.log_exp, neg_neg]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Rounding upward meets the reference KL budget in equation (48). For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the second event](hyp:B),
[the q](hyp:q), [the observed prefix](hyp:u), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the second event assumption](hyp:hB),
[the q assumption](hyp:hq), and [the observed prefix assumption](hyp:hu), this establishes
[the lower testing depth information bound result](goal). -/
-- @node: lower_testing_depth_information_le
lemma lower_testing_depth_information_le (t0 zeta B q u : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hB : 0 < B)
    (hq : 0 < q) (hu : 0 < u) :
    B * q ^ 2 * mixingAlpha t0 ^ (2 * lowerTestingDepth t0 zeta B q u) *
      policyFactor zeta ^ (-(lowerTestingDepth t0 zeta B q u : ℤ)) ≤ u / 32 := by
  let D := 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)
  have hD : 0 < D := selector_tuning_denominator_pos t0 zeta ht0 hzeta
  have hr : 0 < 32 * B * q ^ 2 / u := by positivity
  have hc := Nat.le_ceil (Real.log (32 * B * q ^ 2 / u) / D)
  have hdec : -(D * (lowerTestingDepth t0 zeta B q u : ℝ)) ≤
      -Real.log (32 * B * q ^ 2 / u) := by
    have := (div_le_iff₀ hD).mp hc
    change Real.log (32 * B * q ^ 2 / u) ≤
      (lowerTestingDepth t0 zeta B q u : ℝ) * D at this
    linarith
  have he := Real.exp_le_exp.mpr hdec
  rw [Real.exp_neg (Real.log (32 * B * q ^ 2 / u)), Real.exp_log hr] at he
  calc
    _ = B * q ^ 2 * Real.exp (-(D * (lowerTestingDepth t0 zeta B q u : ℝ))) := by
      rw [mul_assoc, lower_information_decay_eq]
      congr 2; ring
    _ ≤ B * q ^ 2 * (32 * B * q ^ 2 / u)⁻¹ :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = u / 32 := by field_simp

/-- Rounding upward loses at most one mixing factor in equation (50). For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the second event](hyp:B),
[the q](hyp:q), [the observed prefix](hyp:u), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the second event assumption](hyp:hB),
[the q assumption](hyp:hq), [the observed prefix assumption](hyp:hu), and
[the small assumption](hyp:hsmall), this establishes
[the lower testing depth gap ge result](goal). -/
-- @node: lower_testing_depth_gap_ge
lemma lower_testing_depth_gap_ge (t0 zeta B q u : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hB : 0 < B)
    (hq : 0 < q) (hu : 0 < u)
    (hsmall : u ≤ lowerDepthThreshold t0 zeta B * q ^ 2) :
    mixingAlpha t0 * (u / (32 * B * q ^ 2)) ^ (rateExponent t0 zeta / 2) ≤
      mixingAlpha t0 ^ lowerTestingDepth t0 zeta B q u := by
  have hα : 0 < mixingAlpha t0 := Real.exp_pos _
  have hα1 : mixingAlpha t0 ≤ 1 := by
    unfold mixingAlpha
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hx := (lower_testing_depth_bounds t0 zeta B q u ht0 hzeta hB hq hu hsmall).2
  have hmono := Real.rpow_le_rpow_of_exponent_ge hα hα1 hx
  rw [Real.rpow_natCast] at hmono
  refine le_trans ?_ hmono
  apply le_of_eq
  have hr : 0 < u / (32 * B * q ^ 2) := by positivity
  have hlog : Real.log (u / (32 * B * q ^ 2)) =
      -Real.log (32 * B * q ^ 2 / u) := by
    rw [show u / (32 * B * q ^ 2) = (32 * B * q ^ 2 / u)⁻¹ by field_simp,
      Real.log_inv]
  have hlogα : Real.log (mixingAlpha t0) = -Real.log (1 / mixingAlpha t0) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hr]
  conv_lhs => lhs; rw [← Real.exp_log hα]
  rw [← Real.exp_add]
  congr 1
  rw [hlog, hlogα, ← selector_tuning_rate_identity t0 zeta ht0 hzeta]
  ring

/-- Factoring the retained signal gives the hidden-memory frontier coordinate. For
[the second event](hyp:B), [the q](hyp:q), [the observed prefix](hyp:u),
[the rate exponent](hyp:beta), [the second event assumption](hyp:hB),
[the q assumption](hyp:hq), and [the observed prefix assumption](hyp:hu), this establishes
[the lower gap rate factorization result](goal). -/
-- @node: lower_gap_rate_factorization
lemma lower_gap_rate_factorization (B q u beta : ℝ)
    (hB : 0 < B) (hq : 0 < q) (hu : 0 < u) :
    q * (u / (32 * B * q ^ 2)) ^ (beta / 2) =
      (32 * B) ^ (-(beta / 2)) * q ^ (1 - beta) * u ^ (beta / 2) := by
  have hb : 0 < 32 * B := by positivity
  have hd : 0 < 32 * B * q ^ 2 := by positivity
  have hr : 0 < u / (32 * B * q ^ 2) := by positivity
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hb,
    Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hu]
  conv_lhs => lhs; rw [← Real.exp_log hq]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    Real.log_div hu.ne' hd.ne', Real.log_mul hb.ne' (pow_ne_zero _ hq.ne'),
    Real.log_pow]
  congr 1
  ring

/-- The integer-depth gap retains a fixed positive multiple of the rate in (51). For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the second event](hyp:B),
[the q](hyp:q), [the observed prefix](hyp:u), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the second event assumption](hyp:hB),
[the q assumption](hyp:hq), [the observed prefix assumption](hyp:hu), and
[the small assumption](hyp:hsmall), this establishes
[the lower testing depth frontier gap ge result](goal). -/
-- @node: lower_testing_depth_frontier_gap_ge
lemma lower_testing_depth_frontier_gap_ge (t0 zeta B q u : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hB : 0 < B)
    (hq : 0 < q) (hu : 0 < u)
    (hsmall : u ≤ lowerDepthThreshold t0 zeta B * q ^ 2) :
    (mixingAlpha t0 * (32 * B) ^ (-(rateExponent t0 zeta / 2))) *
        (q ^ (1 - rateExponent t0 zeta) * u ^ (rateExponent t0 zeta / 2)) ≤
      q * mixingAlpha t0 ^ lowerTestingDepth t0 zeta B q u := by
  have hgap := mul_le_mul_of_nonneg_left
    (lower_testing_depth_gap_ge t0 zeta B q u ht0 hzeta hB hq hu hsmall) hq.le
  calc
    _ = mixingAlpha t0 *
        (q * (u / (32 * B * q ^ 2)) ^ (rateExponent t0 zeta / 2)) := by
      rw [lower_gap_rate_factorization B q u _ hB hq hu]
      ring
    _ ≤ _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using hgap

/-- Scaling the one-step budget by trajectory length gives log(M)/32 in (48). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the second event](hyp:B), [the q](hyp:q),
[the time horizon assumption](hyp:hT), [the candidate-policy count assumption](hyp:hM),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the second event assumption](hyp:hB), and [the q assumption](hyp:hq), this establishes
[the lower testing depth trajectory budget bound result](goal). -/
-- @node: lower_testing_depth_trajectory_budget_le
lemma lower_testing_depth_trajectory_budget_le (T M : Nat) (t0 zeta B q : ℝ)
    (hT : 0 < T) (hM : 2 ≤ M) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hB : 0 < B) (hq : 0 < q) :
    B * (T : ℝ) * q ^ 2 *
        mixingAlpha t0 ^ (2 * lowerTestingDepth t0 zeta B q ((listInformationRatio T M (by omega) hM))) *
        policyFactor zeta ^ (-(lowerTestingDepth t0 zeta B q ((listInformationRatio T M (by omega) hM)) : ℤ)) ≤
      Real.log (M : ℝ) / 32 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hu : 0 < (listInformationRatio T M (by omega) hM) := by
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < M by omega))) hTr
  have hbudget := mul_le_mul_of_nonneg_left
    (lower_testing_depth_information_le t0 zeta B q ((listInformationRatio T M (by omega) hM))
      ht0 hzeta hB hq hu) hTr.le
  calc
    _ = (T : ℝ) * (B * q ^ 2 *
        mixingAlpha t0 ^ (2 * lowerTestingDepth t0 zeta B q ((listInformationRatio T M (by omega) hM))) *
        policyFactor zeta ^ (-(lowerTestingDepth t0 zeta B q ((listInformationRatio T M (by omega) hM)) : ℤ))) := by
      ring
    _ ≤ (T : ℝ) * ((listInformationRatio T M (by omega) hM) / 32) := hbudget
    _ = Real.log (M : ℝ) / 32 := by
      unfold listInformationRatio
      field_simp

/-- The retained-signal constant in (51) is positive and depends only on the regime parameters
and the KL constant. For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the second event](hyp:B), [the action](hyp:a), [the second event assumption](hyp:hB), and
[the action assumption](hyp:ha), this establishes
[the lower hidden rate constant positivity result](goal). -/
-- @node: lower_hidden_rate_constant_pos
lemma lower_hidden_rate_constant_pos (t0 zeta B a : ℝ) (hB : 0 < B) (ha : 0 < a) :
    0 < a * mixingAlpha t0 / 8 * (32 * B) ^ (-(rateExponent t0 zeta / 2)) := by
  have hα : 0 < mixingAlpha t0 := Real.exp_pos _
  positivity

end CausalSmith.Stat.PomdpPolicyclassRegret
