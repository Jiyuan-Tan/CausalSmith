module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFilterPath

/-! # Information cost under the generated observed history

Endpoint marginalization transports the recursive reward law and its
information bound to the actual trajectory law, summing all hidden histories.
The stationary initial window is included in the same identities.
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

local notation "F" => sparseHiddenFilter hd t0 zeta C code v x a r
local notation "A" => (fun n : Nat ↦
  ∏ k : Fin n, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal)
local notation "H" => (fun (t : Fin T) (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) ↦
  (((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law.map
    (finiteHistStateView t))
    (((fun k : Fin t.val ↦ (x k.val, h k.castSucc)),
      (fun k : Fin t.val ↦ (a k.val, r k.val))),
      (x t.val, h (Fin.last t.val)))).toReal)

/-- The actual history mass with its current hidden state specified is the endpoint filter mass
times the common behavior likelihood. The hidden prefix is marginalized, rather than revealed to
the observer. For the time horizon, the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the epoch index](hyp:t), and
[the alternate stated assumption](hyp:h'), this establishes
[the sparse generated history endpoint mass equality filter result](goal). -/
-- @node: sparse_generated_history_endpoint_mass_eq_filter
lemma sparse_generated_history_endpoint_mass_eq_filter (ht0 : 0 < t0)
    (hC : 1 ≤ C) (t : Fin T) (h' : Fin (2 * (Q + 1))) :
    (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      if h (Fin.last t.val) = h' then H t h else 0) = A t.val * F t.val h' := by
  classical
  have hstates (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) :
      finiteHistoryStates
        (((fun k : Fin t.val ↦ (x k.val, h k.castSucc)),
          (fun k : Fin t.val ↦ (a k.val, r k.val))),
          (x t.val, h (Fin.last t.val))) = (fun k ↦ (x k.val, h k)) := by
    funext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp [finiteHistoryStates]
  simp_rw [finiteHistStateView_mass_toReal, hstates]
  dsimp only [sparseFinite]
  simp_rw [sparse_fixed_prefix_weight_eq_hidden_path_weight hd t0 zeta C code v x a r ht0 hC]
  rw [sparse_hidden_filter_eq_path_endpoint_mass hd t0 zeta C code v x a r]
  simp only [Finset.mul_sum, mul_ite, mul_zero]

/-- Weighting the current hidden endpoint by any function commutes with marginalization. In
particular this transports the actual reward kernel without conditioning on a reset indicator.
For the time horizon, the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the epoch index](hyp:t), and [the g](hyp:g), this establishes
[the sparse generated history endpoint expectation equality filter result](goal). -/
-- @node: sparse_generated_history_endpoint_expectation_eq_filter
lemma sparse_generated_history_endpoint_expectation_eq_filter (ht0 : 0 < t0)
    (hC : 1 ≤ C) (t : Fin T) (g : Fin (2 * (Q + 1)) → ℝ) :
    (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      H t h * g (h (Fin.last t.val))) = A t.val * ∑ h', F t.val h' * g h' := by
  classical
  calc
    _ = ∑ h' : Fin (2 * (Q + 1)),
        (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
          if h (Fin.last t.val) = h' then H t h else 0) * g h' := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      simp
    _ = _ := by
      simp_rw [sparse_generated_history_endpoint_mass_eq_filter hd t0 zeta C code v x a r
        ht0 hC]
      simp only [Finset.mul_sum, mul_assoc]

/-- The common behavior likelihood is positive for every observed history, so cancelling it in
the Bayes quotient loses no stationary prefix. For the code dimension,
the hidden-depth scale, the policy-overlap scale,
the observed state, the action,
[the policy-overlap scale assumption](hyp:hzeta), and [the sample size](hyp:n), this establishes
[the sparse observed behavior history weight positivity result](goal). -/
-- @node: sparse_observed_behavior_history_weight_pos
lemma sparse_observed_behavior_history_weight_pos (hzeta : 0 < zeta) (n : Nat) :
    0 < A n := by
  apply Finset.prod_pos
  intro k _
  rw [sparse_behavior_pmf_toReal zeta hzeta]
  exact sparse_behavior_weight_pos zeta hzeta _

/-- The reward probability given the observed prefix and fresh context, computed by summing the
generated hidden histories, is exactly the normalized recursive reward law used in the one-step
KL calculation. For the time horizon, the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the epoch index](hyp:t), and [the y](hyp:y),
this establishes [the sparse generated history normalized reward equality filter result](goal). -/
-- @node: sparse_generated_history_normalized_reward_eq_filter
lemma sparse_generated_history_normalized_reward_eq_filter (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) (y : Fin 2) :
    (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      H t h * sparseRewardWeight t0 Q (h (Fin.last t.val)) y) /
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h) =
      (∑ h', F t.val h' * sparseRewardWeight t0 Q h' y) / (∑ h', F t.val h') := by
  rw [sparse_generated_history_endpoint_expectation_eq_filter hd t0 zeta C code v x a r
    ht0 hC t (fun h ↦ sparseRewardWeight t0 Q h y),
    sparse_generated_history_hidden_marginal_eq_filter hd t0 zeta C code v x a r ht0 hC]
  exact mul_div_mul_left _ _ (ne_of_gt
    (sparse_observed_behavior_history_weight_pos zeta x a hzeta t.val))

/-- Normalizing the actual terminal-depth marginal cancels the common behavior likelihood and
gives the recursive depth posterior. Both signs and all past hidden states are marginalized. For
the time horizon, the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated history terminal posterior equality filter result](goal). -/
-- @node: sparse_generated_history_terminal_posterior_eq_filter
lemma sparse_generated_history_terminal_posterior_eq_filter (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    (∑ u : Fin 2, ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      if h (Fin.last t.val) = depthSignEquiv Q (Fin.last Q, u) then H t h else 0) /
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h) =
      (∑ u : Fin 2, F t.val (depthSignEquiv Q (Fin.last Q, u))) / (∑ h', F t.val h') := by
  simp_rw [sparse_generated_history_endpoint_mass_eq_filter hd t0 zeta C code v x a r
    ht0 hC]
  rw [← Finset.mul_sum,
    sparse_generated_history_hidden_marginal_eq_filter hd t0 zeta C code v x a r ht0 hC]
  exact mul_div_mul_left _ _ (ne_of_gt
    (sparse_observed_behavior_history_weight_pos zeta x a hzeta t.val))

/-- The posterior uniform bound (15) holds for the generated observed history, including every
stationary initial window, without any assumed filter recurrence or likelihood identity. For
the time horizon, the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated history terminal posterior bound result](goal). -/
-- @node: sparse_generated_history_terminal_posterior_le
lemma sparse_generated_history_terminal_posterior_le (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    (∑ u : Fin 2, ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      if h (Fin.last t.val) = depthSignEquiv Q (Fin.last Q, u) then H t h else 0) /
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h) ≤
        filterConstant t0 * mixingAlpha t0 ^ Q := by
  rw [sparse_generated_history_terminal_posterior_eq_filter hd t0 zeta C code v x a r
    ht0 hzeta hC]
  exact sparse_hidden_filter_uniform_bound hd t0 zeta C ht0 hzeta hC code v x a r t.val

/-- The conditional information cost under the actual generated history keeps the squared
observed retention window, as required by (18)--(19). All hidden prefixes are summed out,
including stationary initial windows. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated history reward KL bound window result](goal). -/
-- @node: sparse_generated_history_reward_kl_le_window
lemma sparse_generated_history_reward_kl_le_window (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    (∑ y : Fin 2,
      ((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
          H t h * sparseRewardWeight t0 Q (h (Fin.last t.val)) y) /
        (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h)) *
      Real.log (((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
          H t h * sparseRewardWeight t0 Q (h (Fin.last t.val)) y) /
        (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), H t h)) / (1 / 2 : ℝ))) ≤
      sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
        mixingAlpha t0 ^ (2 * Q) *
        (sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
          ∏ k ∈ Finset.Ico (t.val - min Q t.val) t.val,
            retentionIndicator hd code v (x k) (a k)) ^ 2 := by
  simp_rw [sparse_generated_history_normalized_reward_eq_filter hd t0 zeta C code v x a r
    ht0 hzeta hC]
  exact sparse_hidden_filter_reward_kl_le_window hd t0 zeta C code v x a r
    ht0 hzeta hC t.val

end History

end CausalSmith.Stat.PomdpPolicyclassRegret
