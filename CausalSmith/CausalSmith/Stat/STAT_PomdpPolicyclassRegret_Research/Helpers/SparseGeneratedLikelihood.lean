module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseGeneratedRewardInformation

/-! # Likelihood of the generated observed prefix

The hidden-history marginal of the actual chronological law is positive and
has the observed reward likelihood product and logarithmic expansion. These
identities include the stationary initial context and all common behavior
factors, without exposing the hidden history to the observer.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

section History

variable {T M d Q : Nat} (hd : 0 < d) (t0 zeta C : ℝ)
  (code : Fin M → Fin d → Bool) (v : Fin M)
  (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)

set_option quotPrecheck false

local notation "F" => sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
local notation "hist" => (fun (t : Fin T) (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) ↦
  (((fun k : Fin t.val ↦ (x k.val, h k.castSucc)),
    (fun k : Fin t.val ↦ (a k.val, r k.val))),
    (x t.val, h (Fin.last t.val))))
local notation "H" => (fun (t : Fin T) (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) ↦
  (((F).law.map (finiteHistStateView t)) (hist t h)).toReal)
local notation "J" => (fun (t : Fin T) (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) ↦
  (((F).law.map (finiteHistActionPair t)) (hist t h, a t.val)).toReal)
local notation "N" => (fun (t : Fin T) (h : Fin (t.val + 1) → Fin (2 * (Q + 1)))
  (y : Fin 2) ↦ ∑ s' : JointState (d * hdepth Q) (2 * (Q + 1)),
    (((F).law.map (finiteHistNextPair t)) ((hist t h, a t.val), (y, s'))).toReal)
local notation "A" => (fun n : Nat ↦
  ∏ k : Fin n, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal)
local notation "κ" => (((d * hdepth Q : Nat) : ℝ)⁻¹)
local notation "D" => (fun n : Nat ↦
  ∑ h', sparseHiddenFilter hd t0 zeta C code v x a r n h')
local notation "Z" => (fun n : Nat ↦
  (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
    (depthSignEquiv Q (Fin.last Q, u))) / D n)
local notation "μ" => (fun n : Nat ↦
  sparseSignal t0 * sparseFilterBias hd zeta C code v x a n Q * Z n)

/-- Every observed prefix and current context has positive generated mass, so its Bayes
denominator can be cancelled on every word. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated history mass positivity result](goal). -/
-- @node: sparse_generated_history_mass_pos
lemma sparse_generated_history_mass_pos (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    0 < ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h := by
  rw [sparse_generated_history_hidden_marginal_eq_filter hd t0 zeta C code v x a r
    ht0 hC]
  exact mul_pos (sparse_observed_behavior_history_weight_pos zeta x a hzeta t.val)
    (sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC t.val)

/-- Including the fresh observed action preserves positivity of the marginal history mass under
the behavior policy. For the time horizon, the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated action history mass positivity result](goal). -/
-- @node: sparse_generated_action_history_mass_pos
lemma sparse_generated_action_history_mass_pos (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    0 < ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h := by
  simp_rw [sparse_generated_action_history_mass hd t0 zeta C code v x a r]
  rw [← Finset.sum_mul]
  apply mul_pos (sparse_generated_history_mass_pos hd t0 zeta C code v x a r
    ht0 hzeta hC t)
  rw [sparse_behavior_pmf_toReal zeta hzeta]
  exact sparse_behavior_weight_pos zeta hzeta _

/-- The actual generated reward likelihood ratio relative to a fair reward is one plus the
observed sign times the filtered reward mean, as in (8) and (16). For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the epoch index](hyp:t), and [the y](hyp:y),
this establishes [the sparse generated action history reward ratio result](goal). -/
-- @node: sparse_generated_action_history_reward_ratio
lemma sparse_generated_action_history_reward_ratio (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) (y : Fin 2) :
    (((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) / (1 / 2 : ℝ)) =
      1 + (if y = 0 then -1 else 1 : ℝ) * μ t.val := by
  rw [sparse_generated_action_history_normalized_reward_eq_filter
    hd t0 zeta C code v x a r ht0 hzeta hC,
    sparse_hidden_filter_normalized_reward hd t0 zeta C code v x a r ht0 hzeta hC]
  ring

/-- The hidden-history marginal of the actual prefix law has the exact chronological likelihood
product; stationary context and behavior masses are retained explicitly. For
the time horizon, the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated history likelihood product result](goal). -/
-- @node: sparse_generated_history_likelihood_product
lemma sparse_generated_history_likelihood_product (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h) =
      A t.val * (κ * (κ / 2) ^ t.val *
        ∏ k ∈ Finset.range t.val, (1 + (if r k = 0 then -1 else 1 : ℝ) * μ k)) := by
  rw [sparse_generated_history_hidden_marginal_eq_filter hd t0 zeta C code v x a r
    ht0 hC]
  exact congrArg (fun z : ℝ ↦ A t.val * z)
    (sparse_hidden_filter_total_likelihood_product hd t0 zeta C code v x a r
      ht0 hzeta hC t.val)

/-- Taking the logarithm of the actual prefix likelihood relative to its common fair
context-action-reward factors gives the sum of observed reward log likelihood ratios in
(16)--(18). For the time horizon, the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated history log likelihood ratio result](goal). -/
-- @node: sparse_generated_history_log_likelihood_ratio
lemma sparse_generated_history_log_likelihood_ratio (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    Real.log ((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h) /
      (A t.val * (κ * (κ / 2) ^ t.val))) =
      ∑ k ∈ Finset.range t.val,
        Real.log (1 + (if r k = 0 then -1 else 1 : ℝ) * μ k) := by
  rw [sparse_generated_history_hidden_marginal_eq_filter hd t0 zeta C code v x a r
    ht0 hC, mul_div_mul_left _ _ (ne_of_gt
      (sparse_observed_behavior_history_weight_pos zeta x a hzeta t.val))]
  exact sparse_hidden_filter_log_likelihood_ratio hd t0 zeta C code v x a r
    ht0 hzeta hC t.val

/-- Summing the two possible rewards in the generated next-epoch law recovers its observed
action-history mass, with all successor states and hidden histories marginalized. For
the time horizon, the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC), and
[the epoch index](hyp:t), this establishes
[the sparse generated action history reward mass sum result](goal). -/
-- @node: sparse_generated_action_history_reward_mass_sum
lemma sparse_generated_action_history_reward_mass_sum (ht0 : 0 < t0)
    (hC : 1 ≤ C) (t : Fin T) :
    (∑ y : Fin 2, ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) =
      ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h := by
  simp_rw [sparse_generated_reward_history_mass hd t0 zeta C code v x a r ht0 hC,
    sparse_generated_action_history_mass hd t0 zeta C code v x a r]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sparse_reward_weight_sum, mul_one]

/-- Every conditional reward likelihood ratio of the generated observed history is positive;
taking its logarithm is legitimate for either reward. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the epoch index](hyp:t), and [the y](hyp:y),
this establishes [the sparse generated action history reward ratio positivity result](goal). -/
-- @node: sparse_generated_action_history_reward_ratio_pos
lemma sparse_generated_action_history_reward_ratio_pos (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) (y : Fin 2) :
    0 < (((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) / (1 / 2 : ℝ)) := by
  rw [sparse_generated_action_history_reward_ratio hd t0 zeta C code v x a r
    ht0 hzeta hC]
  have hb := sparse_hidden_filter_reward_mean_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC t.val
  dsimp only
  split_ifs <;> nlinarith [hb.1, hb.2]

/-- Multiplying the conditional reward information bound by the actual observed action-history
mass gives the unnormalized chain-rule contribution in (18). The squared retention window is
preserved for stationary prefixes. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated action history weighted reward KL bound window result](goal). -/
-- @node: sparse_generated_action_history_weighted_reward_kl_le_window
lemma sparse_generated_action_history_weighted_reward_kl_le_window
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    (∑ y : Fin 2,
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) *
      Real.log (((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
        (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) / (1 / 2 : ℝ))) ≤
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h) *
      (sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
        mixingAlpha t0 ^ (2 * Q) *
        (sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
          ∏ k ∈ Finset.Ico (t.val - min Q t.val) t.val,
            retentionIndicator hd code v (x k) (a k)) ^ 2) := by
  have hpos := sparse_generated_action_history_mass_pos hd t0 zeta C code v x a r
    ht0 hzeta hC t
  have hbound := mul_le_mul_of_nonneg_left
    (sparse_generated_action_history_reward_kl_le_window hd t0 zeta C code v x a r
      ht0 hzeta hC t) (le_of_lt hpos)
  calc
    _ = (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h) *
        (∑ y : Fin 2,
          ((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
            (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) *
          Real.log (((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
            (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) / (1 / 2 : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos)]
    _ ≤ _ := hbound

end History

end CausalSmith.Stat.PomdpPolicyclassRegret
