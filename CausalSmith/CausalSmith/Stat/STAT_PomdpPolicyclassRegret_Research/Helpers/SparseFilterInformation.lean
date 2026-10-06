module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseKLBounds

/-! # One-step information cost of the sparse observed filter

The normalized reward probabilities are a Rademacher law. The uniform
posterior bound controls its squared mean and its relative entropy against a
fair reward, retaining the observed window factor for the moment calculation.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

section Filter

variable {M d Q : Nat} (hd : 0 < d) (t0 zeta C : ℝ)
  (code : Fin M → Fin d → Bool) (v : Fin M)
  (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)

local notation "F" => sparseHiddenFilter hd t0 zeta C code v x a r
local notation "Z" => (fun n : Nat ↦
  (∑ u, F n (depthSignEquiv Q (Fin.last Q, u))) / (∑ h, F n h))
local notation "μ" => (fun n : Nat ↦
  sparseSignal t0 * sparseFilterBias hd zeta C code v x a n Q * Z n)
local notation "P" => (fun n : Nat ↦ fun y : Fin 2 ↦
  (∑ h, F n h * sparseRewardWeight t0 Q h y) / (∑ h, F n h))

/-- The conditional reward mean is nonnegative and strictly below one for every observed word,
including stationary prefix windows. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter reward mean bounds result](goal). -/
-- @node: sparse_hidden_filter_reward_mean_bounds
lemma sparse_hidden_filter_reward_mean_bounds (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    0 ≤ μ n ∧ μ n < 1 := by
  have hc := sparse_signal_bounds t0 ht0
  have hb := sparse_filter_bias_bounds hd zeta C code v x a hzeta hC n Q
  have hz := sparse_hidden_filter_depth_ratio_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC n (Fin.last Q)
  have hcb : 0 ≤ sparseSignal t0 * sparseFilterBias hd zeta C code v x a n Q :=
    mul_nonneg hc.1.le hb.1
  have hcb_le := mul_le_mul_of_nonneg_left hb.2 hc.1.le
  have hmean_le := mul_le_mul_of_nonneg_left hz.2 hcb
  constructor
  · exact mul_nonneg hcb hz.1
  · dsimp only at hcb_le hmean_le ⊢
    nlinarith

/-- Squaring the exact conditional reward mean and using the analytic filter bootstrap gives the
pointwise information cost in equation (18). For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter reward mean sq bound result](goal). -/
-- @node: sparse_hidden_filter_reward_mean_sq_le
lemma sparse_hidden_filter_reward_mean_sq_le (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    (μ n) ^ 2 ≤ sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 *
      filterConstant t0 ^ 2 * mixingAlpha t0 ^ (2 * Q) *
      (sparseRetentionProbability Q zeta ^ (Q - min Q n) *
        ∏ k ∈ Finset.Ico (n - min Q n) n,
          retentionIndicator hd code v (x k) (a k)) ^ 2 := by
  have hz := sparse_hidden_filter_uniform_bound hd t0 zeta C ht0 hzeta hC
    code v x a r n
  have hz0 := (sparse_hidden_filter_depth_ratio_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC n (Fin.last Q)).1
  have hsq : (Z n) ^ 2 ≤ (filterConstant t0 * mixingAlpha t0 ^ Q) ^ 2 := by
    gcongr
  have hm := mul_le_mul_of_nonneg_left hsq
    (sq_nonneg (sparseSignal t0 * sparseFilterBias hd zeta C code v x a n Q))
  have hpow : mixingAlpha t0 ^ (2 * Q) = (mixingAlpha t0 ^ Q) ^ 2 := by
    rw [mul_comm 2 Q, pow_mul]
  dsimp only at hm ⊢
  rw [sparse_filter_bias_eq_window] at hm
  rw [hpow, sparse_filter_bias_eq_window]
  nlinarith only [hm]

/-- The relative entropy of the actual normalized reward law against a fair reward is at most
its squared mean, as in equation (17). For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter reward KL bound sq result](goal). -/
-- @node: sparse_hidden_filter_reward_kl_le_sq
lemma sparse_hidden_filter_reward_kl_le_sq (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    (∑ y : Fin 2, P n y * Real.log (P n y / (1 / 2 : ℝ))) ≤ (μ n) ^ 2 := by
  have hb := sparse_hidden_filter_reward_mean_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC n
  have hk := rademacher_kl_le_sq (μ n) (by linarith [hb.1]) hb.2
  have hp0 : P n 0 = (1 - μ n) / 2 := by
    simpa [sub_eq_add_neg] using sparse_hidden_filter_normalized_reward hd t0 zeta C code v x a r
      ht0 hzeta hC n 0
  have hp1 : P n 1 = (1 + μ n) / 2 := by
    simpa [sub_eq_add_neg] using sparse_hidden_filter_normalized_reward hd t0 zeta C code v x a r
      ht0 hzeta hC n 1
  rw [Fin.sum_univ_two, hp0, hp1]
  have hdiv (z : ℝ) : z / 2 / (1 / 2 : ℝ) = z := by ring
  rw [hdiv, hdiv, add_comm]
  exact hk

/-- The one-step entropy cost keeps the squared retention window, ready for averaging over the
common context-action law in equations (18)--(19). For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter reward KL bound window result](goal). -/
-- @node: sparse_hidden_filter_reward_kl_le_window
lemma sparse_hidden_filter_reward_kl_le_window (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    (∑ y : Fin 2, P n y * Real.log (P n y / (1 / 2 : ℝ))) ≤
      sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 *
      filterConstant t0 ^ 2 * mixingAlpha t0 ^ (2 * Q) *
      (sparseRetentionProbability Q zeta ^ (Q - min Q n) *
        ∏ k ∈ Finset.Ico (n - min Q n) n,
          retentionIndicator hd code v (x k) (a k)) ^ 2 := by
  exact (sparse_hidden_filter_reward_kl_le_sq hd t0 zeta C code v x a r
    ht0 hzeta hC n).trans
      (sparse_hidden_filter_reward_mean_sq_le hd t0 zeta C code v x a r
        ht0 hzeta hC n)


local notation "D" => (fun n : Nat ↦ ∑ h, F n h)
local notation "κ" => (((d * hdepth Q : Nat) : ℝ)⁻¹)

/-- Each realized reward has a strictly positive likelihood ratio against a fair reward, so
logarithms of the chronological product are well defined. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter reward ratio positivity result](goal). -/
-- @node: sparse_hidden_filter_reward_ratio_pos
lemma sparse_hidden_filter_reward_ratio_pos (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    0 < 1 + (if r n = 0 then -1 else 1 : ℝ) * μ n := by
  have hb := sparse_hidden_filter_reward_mean_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC n
  dsimp only
  split_ifs <;> nlinarith [hb.1, hb.2]

/-- The exact Bayes update factors into the fresh context mass, the fair reward mass and its
observed conditional likelihood ratio. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter total likelihood update result](goal). -/
-- @node: sparse_hidden_filter_total_likelihood_update
lemma sparse_hidden_filter_total_likelihood_update (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    D (n + 1) = (κ / 2) * D n * (1 + (if r n = 0 then -1 else 1 : ℝ) * μ n) := by
  have hp := ne_of_gt
    (sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC n)
  have hn := sparse_hidden_filter_normalized_reward hd t0 zeta C code v x a r
    ht0 hzeta hC n (r n)
  have he := (div_eq_iff hp).mp hn
  dsimp only
  rw [sparse_hidden_filter_total_update hd t0 zeta C code v x a r, he]
  ring

/-- Iterating the exact update yields the product likelihood in equation (16) at the
recursive-filter level, including its stationary initial mass. The filter also records the fresh
context at the end of the reward prefix. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter total likelihood product result](goal). -/
-- @node: sparse_hidden_filter_total_likelihood_product
lemma sparse_hidden_filter_total_likelihood_product (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    D n = κ * (κ / 2) ^ n *
      ∏ k ∈ Finset.range n, (1 + (if r k = 0 then -1 else 1 : ℝ) * μ k) := by
  induction n with
  | zero =>
    simpa using sparse_hidden_filter_initial_total hd t0 zeta C code v x a r
      ht0 hzeta hC
  | succ n ih =>
    rw [sparse_hidden_filter_total_likelihood_update hd t0 zeta C code v x a r
      ht0 hzeta hC, ih, pow_succ, Finset.prod_range_succ]
    ring

/-- Removing the common fair context-reward likelihood from the filter mass leaves exactly the
product of observed reward likelihood ratios. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter likelihood ratio product result](goal). -/
-- @node: sparse_hidden_filter_likelihood_ratio_product
lemma sparse_hidden_filter_likelihood_ratio_product (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    D n / (κ * (κ / 2) ^ n) =
      ∏ k ∈ Finset.range n, (1 + (if r k = 0 then -1 else 1 : ℝ) * μ k) := by
  have hκ : 0 < κ := by
    apply inv_pos.mpr
    exact_mod_cast Nat.mul_pos hd (show 0 < hdepth Q by simp [hdepth])
  have hbase : κ * (κ / 2) ^ n ≠ 0 := ne_of_gt (by positivity)
  rw [sparse_hidden_filter_total_likelihood_product hd t0 zeta C code v x a r
    ht0 hzeta hC]
  exact mul_div_cancel_left₀ _ hbase

/-- The logarithm of the filter likelihood ratio is the chronological sum of its conditional
reward log likelihoods, the pointwise identity behind (18). For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter log likelihood ratio result](goal). -/
-- @node: sparse_hidden_filter_log_likelihood_ratio
lemma sparse_hidden_filter_log_likelihood_ratio (ht0 : 0 < t0)
    (hzeta : 0 < zeta) (hC : 1 ≤ C) (n : Nat) :
    Real.log (D n / (κ * (κ / 2) ^ n)) =
      ∑ k ∈ Finset.range n, Real.log (1 + (if r k = 0 then -1 else 1 : ℝ) * μ k) := by
  rw [sparse_hidden_filter_likelihood_ratio_product hd t0 zeta C code v x a r
    ht0 hzeta hC]
  apply Real.log_prod
  intro k _
  exact ne_of_gt (sparse_hidden_filter_reward_ratio_pos hd t0 zeta C code v x a r
    ht0 hzeta hC k)

end Filter

end CausalSmith.Stat.PomdpPolicyclassRegret
