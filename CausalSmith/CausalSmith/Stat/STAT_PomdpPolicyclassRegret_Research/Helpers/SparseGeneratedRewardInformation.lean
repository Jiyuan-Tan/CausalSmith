module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseGeneratedFilterInformation

/-! # Observed reward information from the generated trajectory

Marginalize successor states and hidden histories in the actual chronological
law. The fresh behavior action cancels in the conditional reward distribution,
so the squared retention-window information bound applies to the observer's
history including the current action, with stationary prefixes included.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Summing out the successor state leaves the displayed reward law of the common sparse kernel.
For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the state](hyp:s),
[the action](hyp:a), and [the y](hyp:y), this establishes
[the sparse kernel reward marginal result](goal). -/
-- @node: sparse_kernel_reward_marginal
lemma sparse_kernel_reward_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) (y : Fin 2) :
    (∑ s', (sparseKernel hd t0 C code v false s a (y, s')).toReal) =
      sparseRewardWeight t0 Q s.2 y := by
  simp_rw [sparse_kernel_toReal hd t0 C ht0 hC code v false]
  simp only [Bool.false_eq_true, if_false, ← Finset.mul_sum,
    sparse_state_weight_sum, mul_one]

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
local notation "b" => (fun t : Fin T ↦ (sparseBehaviorPMF zeta d Q (x t.val) (a t.val)).toReal)

/-- The generated action-history mass factors into its state-history mass and the common
behavior likelihood. The action depends only on observed context. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the epoch index](hyp:t), and [the stated assumption](hyp:h), this establishes
[the sparse generated action history mass result](goal). -/
-- @node: sparse_generated_action_history_mass
lemma sparse_generated_action_history_mass (t : Fin T)
    (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) : J t h = H t h * b t := by
  dsimp only
  rw [finiteHistActionPair_mass_toReal, finiteHistStateView_mass_toReal]
  rfl

/-- Summing the actual next-epoch law over its unobserved successor state leaves the generated
history mass times the behavior and reward factors. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the epoch index](hyp:t), [the stated assumption](hyp:h), and [the y](hyp:y), this establishes
[the sparse generated reward history mass result](goal). -/
-- @node: sparse_generated_reward_history_mass
lemma sparse_generated_reward_history_mass (ht0 : 0 < t0) (hC : 1 ≤ C)
    (t : Fin T) (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) (y : Fin 2) :
    N t h y = H t h * b t * sparseRewardWeight t0 Q (h (Fin.last t.val)) y := by
  simp_rw [finiteHistNextPair_mass_toReal]
  rw [← Finset.mul_sum]
  change _ * (∑ s', (sparseKernel hd t0 C code v false
    (x t.val, h (Fin.last t.val)) (a t.val) (y, s')).toReal) = _
  rw [sparse_kernel_reward_marginal hd t0 C ht0 hC code v,
    finiteHistStateView_mass_toReal]
  rfl

/-- Conditioning on the current observed action leaves the normalized filter reward law
unchanged: all hidden prefixes and successor states are marginalized in the numerator and all
hidden prefixes in the denominator. For the time horizon,
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the epoch index](hyp:t), and [the y](hyp:y),
this establishes
[the sparse generated action history normalized reward equality filter result](goal). -/
-- @node: sparse_generated_action_history_normalized_reward_eq_filter
lemma sparse_generated_action_history_normalized_reward_eq_filter
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) (y : Fin 2) :
    (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h) =
      (∑ h', sparseHiddenFilter hd t0 zeta C code v x a r t.val h' *
        sparseRewardWeight t0 Q h' y) /
      (∑ h', sparseHiddenFilter hd t0 zeta C code v x a r t.val h') := by
  simp_rw [sparse_generated_reward_history_mass hd t0 zeta C code v x a r ht0 hC,
    sparse_generated_action_history_mass hd t0 zeta C code v x a r]
  have hb : b t ≠ 0 := by
    dsimp only
    rw [sparse_behavior_pmf_toReal zeta hzeta]
    exact ne_of_gt (sparse_behavior_weight_pos zeta hzeta _)
  have hnum : (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      H t h * b t * sparseRewardWeight t0 Q (h (Fin.last t.val)) y) =
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
        H t h * sparseRewardWeight t0 Q (h (Fin.last t.val)) y) * b t := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hnum, ← Finset.sum_mul, mul_div_mul_right _ _ hb]
  exact sparse_generated_history_normalized_reward_eq_filter hd t0 zeta C code v x a r
    ht0 hzeta hC t y

/-- The conditional KL cost of the generated reward, given the observed history including its
current action, retains the squared observed window. Neither reset indicators nor hidden states
enter this conditional law. For the time horizon, the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the epoch index](hyp:t), this establishes
[the sparse generated action history reward KL bound window result](goal). -/
-- @node: sparse_generated_action_history_reward_kl_le_window
lemma sparse_generated_action_history_reward_kl_le_window
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (t : Fin T) :
    (∑ y : Fin 2,
      ((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
        (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) *
      Real.log (((∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), N t h y) /
        (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)), J t h)) / (1 / 2 : ℝ))) ≤
      sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
        mixingAlpha t0 ^ (2 * Q) *
        (sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
          ∏ k ∈ Finset.Ico (t.val - min Q t.val) t.val,
            retentionIndicator hd code v (x k) (a k)) ^ 2 := by
  simp_rw [sparse_generated_action_history_normalized_reward_eq_filter
    hd t0 zeta C code v x a r ht0 hzeta hC]
  exact sparse_hidden_filter_reward_kl_le_window hd t0 zeta C code v x a r
    ht0 hzeta hC t.val

end History

end CausalSmith.Stat.PomdpPolicyclassRegret
