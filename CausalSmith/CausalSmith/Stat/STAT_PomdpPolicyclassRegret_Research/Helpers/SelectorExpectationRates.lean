module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorExpectation
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorMomentRates

/-! # Radius-adaptive expectation rates

Combine layer-cake with the low-radius and balanced-depth moment envelopes
from equations (14) through (16). The block threshold depends only on the regime.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Zero-depth bias and deviation give the parametric block rate. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the sample size assumption](hyp:hn), and
[the small assumption](hyp:hsmall), this establishes
[the selector expected regret low radius result](goal). -/
-- @node: selector_expectedRegret_low_radius
lemma selector_expectedRegret_low_radius {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M)
    (hsmall : (blockLen T M : ℝ) * overlapRadius C ^ 2 ≤ 1) :
    expectedRegret (blockSelector T M (by have := m.list_size; omega) t0 zeta C) m ≤
      (2 * (1 + 1 / (1 - mixingAlpha t0)) + 8 * Real.exp 1 *
        Real.sqrt ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
          policyFactor zeta)) * Real.sqrt (1 / (blockLen T M : ℝ)) := by
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos))
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hClass.zeta_pos
  have hb := selector_low_radius_le_sqrt (blockLen T M) (overlapRadius C) (by omega) hsmall
  have ht := selector_inv_len_le_sqrt (blockLen T M) (by omega)
  have he := selector_block_expectedRegret_le_bias_sd t0 zeta C m hClass hn
  rw [selector_adaptiveDepth_zero _ _ _ _ hsmall] at he
  simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, pow_one] at he
  have hs : Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta / (blockLen T M : ℝ)) =
      Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta) *
          Real.sqrt (1 / (blockLen T M : ℝ)) := by
    rw [div_eq_mul_one_div, Real.sqrt_mul (by positivity)]
  rw [hs] at he
  have htrans := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 1 / (1 - mixingAlpha t0))
  have hid : 1 / ((blockLen T M : ℝ) * (1 - mixingAlpha t0)) =
      (1 / (1 - mixingAlpha t0)) * (1 / (blockLen T M : ℝ)) := by simp only [one_div, mul_inv_rev]
  rw [hid] at he
  nlinarith

/-- In the balanced branch, equation (15) and the transient correction bound the expectation by
the sum of the two block rate coordinates. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the sample size assumption](hyp:hn),
[the large assumption](hyp:hlarge), and [the cap assumption](hyp:hcap), this establishes
[the selector expected regret balanced result](goal). -/
-- @node: selector_expectedRegret_balanced
lemma selector_expectedRegret_balanced {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M)
    (hlarge : 1 < (blockLen T M : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((blockLen T M : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (blockLen T M / 2 : Nat)) :
    expectedRegret (blockSelector T M (by have := m.list_size; omega) t0 zeta C) m ≤
      (4 / (1 - mixingAlpha t0)) * Real.sqrt (1 / (blockLen T M : ℝ)) +
      (2 * (mixingAlpha t0)⁻¹ + 8 * Real.exp 1 *
        Real.sqrt (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
          Real.sqrt (2 * policyFactor zeta)) *
      (overlapRadius C ^ (1 - rateExponent t0 zeta) *
        (blockLen T M : ℝ) ^ (-(rateExponent t0 zeta / 2))) := by
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos))
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hClass.zeta_pos
  have hb := selector_adaptiveDepth_total_bias_le (blockLen T M) t0 zeta C
    hClass.t0_pos hClass.zeta_pos hClass.C_ge_one hlarge hcap
  have hs := selector_adaptiveDepth_sd_rate (blockLen T M) t0 zeta C
    hClass.t0_pos hClass.zeta_pos hClass.C_ge_one hlarge hcap
  have he := selector_block_expectedRegret_le_bias_sd t0 zeta C m hClass hn
  dsimp only at he
  rw [show (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (adaptiveDepth (blockLen T M) t0 zeta C + 1) /
        (blockLen T M - adaptiveDepth (blockLen T M) t0 zeta C : Nat) =
      (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      (policyFactor zeta ^ (adaptiveDepth (blockLen T M) t0 zeta C + 1) /
        (blockLen T M - adaptiveDepth (blockLen T M) t0 zeta C : Nat)) by ring,
    Real.sqrt_mul (by positivity)] at he
  have hs' := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 8 * Real.exp 1 *
      Real.sqrt (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)))
  have ht := mul_le_mul_of_nonneg_left
    (selector_inv_len_le_sqrt (blockLen T M) (by omega))
    (by positivity : 0 ≤ 4 / (1 - mixingAlpha t0))
  have hid : 2 * ((2 / (1 - mixingAlpha t0)) / (blockLen T M : ℝ)) =
      (4 / (1 - mixingAlpha t0)) * (1 / (blockLen T M : ℝ)) := by ring
  nlinarith [hid]

/-- A single regime constant and threshold give equation (16) uniformly in the model, list size,
trajectory length and stationary-overlap radius. For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the selector expected regret block rate result](goal). -/
-- @node: selector_expectedRegret_block_rate
lemma selector_expectedRegret_block_rate (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ (K : ℝ) (n0 : Nat), 0 < K ∧ 4 ≤ n0 ∧
      ∀ {T M : Nat} (C : ℝ) (m : ModelIndex T M), PolicyListClass t0 zeta C m →
        n0 ≤ blockLen T M →
        expectedRegret (blockSelector T M (by have := m.list_size; omega) t0 zeta C) m ≤
          K * (Real.sqrt (1 / (blockLen T M : ℝ)) +
            overlapRadius C ^ (1 - rateExponent t0 zeta) *
              (blockLen T M : ℝ) ^ (-(rateExponent t0 zeta / 2))) := by
  obtain ⟨n0, hn0, hcap⟩ := selector_eventually_cap_inactive t0 zeta ht0 hzeta
  let A := 1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)
  let K1 := 2 * (1 + 1 / (1 - mixingAlpha t0)) +
    8 * Real.exp 1 * Real.sqrt (A * policyFactor zeta)
  let K2 := 4 / (1 - mixingAlpha t0)
  let K3 := 2 * (mixingAlpha t0)⁻¹ +
    8 * Real.exp 1 * Real.sqrt A * Real.sqrt (2 * policyFactor zeta)
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr ht0))
  have hα0 : 0 < mixingAlpha t0 := Real.exp_pos _
  have h1 : 0 < K1 := by dsimp [K1]; positivity
  have h2 : 0 < K2 := by dsimp [K2]; positivity
  have h3 : 0 < K3 := by dsimp [K3]; positivity
  refine ⟨K1 + K2 + K3, n0, by positivity, hn0, ?_⟩
  intro T M C m hClass hn
  have hn4 := hn0.trans hn
  have hq : 0 ≤ overlapRadius C := by
    unfold overlapRadius
    exact div_nonneg (by have := hClass.C_ge_one; linarith) (by have := hClass.C_ge_one; linarith)
  have hs0 : 0 ≤ Real.sqrt (1 / (blockLen T M : ℝ)) := Real.sqrt_nonneg _
  have hr0 : 0 ≤ overlapRadius C ^ (1 - rateExponent t0 zeta) *
      (blockLen T M : ℝ) ^ (-(rateExponent t0 zeta / 2)) := by positivity
  by_cases hsmall : (blockLen T M : ℝ) * overlapRadius C ^ 2 ≤ 1
  · have he := selector_expectedRegret_low_radius t0 zeta C m hClass hn4 hsmall
    change expectedRegret _ m ≤ K1 * _ at he
    nlinarith
  · have he := selector_expectedRegret_balanced t0 zeta C m hClass hn4
      (lt_of_not_ge hsmall) (hcap _ hn C hClass.C_ge_one (lt_of_not_ge hsmall))
    change expectedRegret _ m ≤ K2 * _ + K3 * _ at he
    nlinarith

end CausalSmith.Stat.PomdpPolicyclassRegret
