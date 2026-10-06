module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFilterStep

/-! # Total and forced-depth masses of the observed filter

The filter denominator updates by the observed reward likelihood. Positive
incoming weights remain positive in total, and forced advance windows have
explicit structural masses, including the stationary initial prefix.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- The next observed context is uniform after marginalizing the hidden state. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the codeword index](hyp:v), [the fair-reference flag](hyp:fair), [the state](hyp:s),
[the action](hyp:a), and [the x'](hyp:x'), this establishes
[the sparse state weight context mass result](goal). -/
-- @node: sparse_state_weight_context_mass
lemma sparse_state_weight_context_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x' : Fin (d * hdepth Q)) :
    (∑ h', sparseStateWeight hd t0 C code v fair s (x', h') a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  classical
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h' ↦ sparseStateWeight hd t0 C code v fair s (x', h') a)
    (fun z ↦ sparseStateWeight hd t0 C code v fair s (x', depthSignEquiv Q z) a)
    (fun h' ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp_rw [sparse_state_weight_sum_at_depth, ← Finset.mul_sum]
  suffices hdepthsum : (∑ j' : Fin (Q + 1),
      if hiddenDepth Q s.2 = Q then
        if j'.val = 0 then (1 : ℝ) else 0
      else
        (if j'.val = 0 then 1 - mixingAlpha t0 else 0) +
          (if j'.val = hiddenDepth Q s.2 + 1 then mixingAlpha t0 else 0)) = 1 by
    rw [hdepthsum, mul_one]
  by_cases hterm : hiddenDepth Q s.2 = Q
  · simp [hterm]
  · have hjlt : hiddenDepth Q s.2 < Q := by
      have hjle : hiddenDepth Q s.2 ≤ Q := by
        unfold hiddenDepth
        have := s.2.isLt
        omega
      omega
    let jnext : Fin (Q + 1) := ⟨hiddenDepth Q s.2 + 1, by omega⟩
    have hind (j' : Fin (Q + 1)) :
        (j'.val = hiddenDepth Q s.2 + 1) = (j' = jnext) := by
      apply propext
      simp [jnext, Fin.ext_iff]
    simp [hterm, Finset.sum_add_distrib, hind]

/-- Every reward outcome has a positive probability uniformly over hidden states. For
[the mixing scale](hyp:t0), [the mixing scale assumption](hyp:ht0),
[the hidden-depth scale](hyp:Q), [the stated assumption](hyp:h), and [the reward symbol](hyp:r),
this establishes [the sparse reward weight lower result](goal). -/
-- @node: sparse_reward_weight_lower
lemma sparse_reward_weight_lower (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (h : Fin (2 * (Q + 1))) (r : Fin 2) :
    (1 - sparseSignal t0) / 2 ≤ sparseRewardWeight t0 Q h r := by
  have hc := sparse_signal_bounds t0 ht0
  unfold sparseRewardWeight signValue
  fin_cases r <;> split_ifs <;> norm_num <;> linarith

/-- Marginalizing the new hidden state updates total mass by the realized reward likelihood and
the uniform next-context probability. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the observed state](hyp:x), [the x'](hyp:x'), [the action](hyp:a), [the reward symbol](hyp:r),
and [the f](hyp:f), this establishes [the sparse hidden filter step total result](goal). -/
-- @node: sparse_hidden_filter_step_total
lemma sparse_hidden_filter_step_total {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2)
    (f : Fin (2 * (Q + 1)) → ℝ) :
    (∑ h', sparseHiddenFilterStep hd t0 C code v x x' a r f h') =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        ∑ h, f h * sparseRewardWeight t0 Q h r := by
  unfold sparseHiddenFilterStep
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sparse_state_weight_context_mass hd t0 C code v]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Nonnegative incoming hidden weights remain nonnegative after observing a reward and
propagating through the common kernel. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x),
[the successor observed state](hyp:x'), [the action](hyp:a), [the reward symbol](hyp:r),
[the test function](hyp:f), [the test-function assumption](hyp:hf), and
[the alternate stated assumption](hyp:h'), this establishes
[the sparse hidden filter step nonnegativity result](goal). -/
-- @node: sparse_hidden_filter_step_nonneg
lemma sparse_hidden_filter_step_nonneg {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2)
    (f : Fin (2 * (Q + 1)) → ℝ) (hf : ∀ h, 0 ≤ f h) (h' : Fin (2 * (Q + 1))) :
    0 ≤ sparseHiddenFilterStep hd t0 C code v x x' a r f h' := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (mul_nonneg (hf h) (sparse_reward_weight_nonneg t0 ht0 Q h r))
    (sparse_state_weight_nonneg hd t0 C ht0 hC code v false (x, h) (x', h') a)

section Filter

variable {M d Q : Nat} (hd : 0 < d) (t0 zeta C : ℝ)
  (code : Fin M → Fin d → Bool) (v : Fin M)
  (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)

/-- Every unnormalized observed-prefix hidden weight is nonnegative. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the sample size](hyp:n), and [the stated assumption](hyp:h), this establishes
[the sparse hidden filter nonnegativity result](goal). -/
-- @node: sparse_hidden_filter_nonneg
lemma sparse_hidden_filter_nonneg (ht0 : 0 < t0) (hC : 1 ≤ C)
    (n : Nat) (h : Fin (2 * (Q + 1))) :
    0 ≤ sparseHiddenFilter hd t0 zeta C code v x a r n h := by
  induction n generalizing h with
  | zero => exact ENNReal.toReal_nonneg
  | succ n ih =>
    exact sparse_hidden_filter_step_nonneg hd t0 C ht0 hC code v _ _ _ _ _ ih h

/-- The actual recursive filter denominator satisfies the one-step likelihood update at every
observed epoch. For the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol, and
[the sample size](hyp:n), this establishes [the sparse hidden filter total update result](goal). -/
-- @node: sparse_hidden_filter_total_update
lemma sparse_hidden_filter_total_update (n : Nat) :
    (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r (n + 1) h) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        ∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h *
          sparseRewardWeight t0 Q h (r n) := by
  exact sparse_hidden_filter_step_total hd t0 C code v _ _ _ _ _

/-- Each observed reward costs at least its uniform Bernoulli lower bound in the filter
denominator, without conditioning on a reset. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter total lower result](goal). -/
-- @node: sparse_hidden_filter_total_lower
lemma sparse_hidden_filter_total_lower (ht0 : 0 < t0) (hC : 1 ≤ C) (n : Nat) :
    ((d * hdepth Q : Nat) : ℝ)⁻¹ * ((1 - sparseSignal t0) / 2) *
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) ≤
      ∑ h, sparseHiddenFilter hd t0 zeta C code v x a r (n + 1) h := by
  rw [sparse_hidden_filter_total_update]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [mul_comm ((1 - sparseSignal t0) / 2)]
  exact mul_le_mul_of_nonneg_left (sparse_reward_weight_lower t0 ht0 Q h (r n))
    (sparse_hidden_filter_nonneg hd t0 zeta C code v x a r ht0 hC n h)

/-- Every observed-prefix filter has strictly positive total mass, so its finite Bayes
normalization is well defined. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter total positivity result](goal). -/
-- @node: sparse_hidden_filter_total_pos
lemma sparse_hidden_filter_total_pos (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) :
    0 < ∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h := by
  have hn : (0 : ℝ) < (d * hdepth Q : Nat) := by
    exact_mod_cast Nat.mul_pos hd (show 0 < hdepth Q by simp [hdepth])
  induction n with
  | zero =>
    simp only [sparseHiddenFilter,
      sparse_init_eq_signed_density hd t0 zeta C ht0 hzeta hC code v]
    rw [sparse_signed_density_context_mass d Q t0 C _ ht0]
    positivity
  | succ n ih =>
    have hc := sparse_signal_bounds t0 ht0
    have hp : 0 < ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        ((1 - sparseSignal t0) / 2) *
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) := by
      apply mul_pos (mul_pos (inv_pos.mpr hn) (by linarith)) ih
    exact hp.trans_le
      (sparse_hidden_filter_total_lower hd t0 zeta C code v x a r ht0 hC n)

/-- A positive-depth filter mass comes from the preceding depth with one advance and one fair
reward, regardless of the realized reward sign. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the sample size](hyp:n),
[the candidate index](hyp:j), and [the candidate index assumption](hyp:hj), this establishes
[the sparse hidden filter depth update result](goal). -/
-- @node: sparse_hidden_filter_depth_update
lemma sparse_hidden_filter_depth_update (n : Nat) (j : Fin (Q + 1)) (hj : j.val < Q) :
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r (n + 1)
      (depthSignEquiv Q (⟨j.val + 1, by omega⟩, u))) =
      (((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2) *
        ∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
          (depthSignEquiv Q (j, u)) := by
  exact sparse_hidden_filter_advance_mass hd t0 C code v _ _ _ _ _ j hj

/-- Iterating the fair advance update gives the structural mass of any forced positive-depth
observed window. For the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the sample size](hyp:n), [the block index](hyp:ell), [the candidate index](hyp:j),
[the elln assumption](hyp:helln), and [the ellj assumption](hyp:hellj), this establishes
[the sparse hidden filter forced window result](goal). -/
-- @node: sparse_hidden_filter_forced_window
lemma sparse_hidden_filter_forced_window (n ell : Nat) (j : Fin (Q + 1))
    (helln : ell ≤ n) (hellj : ell ≤ j.val) :
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (j, u))) =
      (((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2) ^ ell *
        ∑ u, sparseHiddenFilter hd t0 zeta C code v x a r (n - ell)
          (depthSignEquiv Q (⟨j.val - ell, by omega⟩, u)) := by
  induction ell generalizing n j with
  | zero => simp
  | succ ell ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    let k : Fin (Q + 1) := ⟨j.val - 1, by omega⟩
    have hk : k.val < Q := by dsimp [k]; omega
    have hj : j = ⟨k.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [k]
      omega
    conv_lhs => rw [hj]
    rw [sparse_hidden_filter_depth_update hd t0 zeta C code v x a r m k hk,
      ih m k (by omega) (by dsimp [k]; omega)]
    have hidx : m + 1 - (ell + 1) = m - ell := by omega
    have hdepth : j.val - (ell + 1) = k.val - ell := by dsimp [k]; omega
    simp only [hidx, hdepth, pow_succ]
    ring

/-- At an early epoch, the forced terminal window has its stationary terminal mass times only
the common fair likelihood factors, as in (11). For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the sample size](hyp:n), and
[the sample size assumption](hyp:hn), this establishes
[the sparse hidden filter early terminal mass result](goal). -/
-- @node: sparse_hidden_filter_early_terminal_mass
lemma sparse_hidden_filter_early_terminal_mass (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) (hn : n ≤ Q) :
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (Fin.last Q, u))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ ^ (n + 1) / (2 : ℝ) ^ n *
        depthMass t0 Q Q := by
  rw [sparse_hidden_filter_forced_window hd t0 zeta C code v x a r n n
    (Fin.last Q) (by omega) hn]
  simp only [Nat.sub_self, sparseHiddenFilter, Fin.val_last]
  rw [sparse_init_context_depth_mass hd t0 zeta C ht0 hzeta hC code v]
  have hstat := sparse_stationary_prefix_advance_mass t0 Q n hn
  simp only [div_pow, mul_pow, pow_succ]
  calc
    _ = ((d * hdepth Q : Nat) : ℝ)⁻¹ ^ n * ((d * hdepth Q : Nat) : ℝ)⁻¹ /
        (2 : ℝ) ^ n * (depthMass t0 Q (Q - n) * mixingAlpha t0 ^ n) := by ring
    _ = _ := by rw [hstat]

/-- A complete terminal window starts at depth zero and has Q fair rewards and Q advances; its
mass depends only on the earlier depth-zero mass. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the sample size](hyp:n), and
[the sample size assumption](hyp:hn), this establishes
[the sparse hidden filter complete terminal mass result](goal). -/
-- @node: sparse_hidden_filter_complete_terminal_mass
lemma sparse_hidden_filter_complete_terminal_mass (n : Nat) (hn : Q ≤ n) :
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (Fin.last Q, u))) =
      (((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2) ^ Q *
        ∑ u, sparseHiddenFilter hd t0 zeta C code v x a r (n - Q)
          (depthSignEquiv Q (0, u)) := by
  simpa using sparse_hidden_filter_forced_window hd t0 zeta C code v x a r n Q
    (Fin.last Q) hn (by simp)

/-- A depth mass is bounded by the total observed-prefix filter mass. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the sample size](hyp:n), and [the candidate index](hyp:j), this establishes
[the sparse hidden filter depth bound total result](goal). -/
-- @node: sparse_hidden_filter_depth_le_total
lemma sparse_hidden_filter_depth_le_total (ht0 : 0 < t0) (hC : 1 ≤ C)
    (n : Nat) (j : Fin (Q + 1)) :
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (j, u))) ≤
        ∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h := by
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm _
    (fun z ↦ sparseHiddenFilter hd t0 zeta C code v x a r n (depthSignEquiv Q z))
    (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro k _
  exact Finset.sum_nonneg (fun u _ ↦
    sparse_hidden_filter_nonneg hd t0 zeta C code v x a r ht0 hC n _)

/-- Normalizing a depth mass produces a posterior between zero and one. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the sample size](hyp:n), and
[the candidate index](hyp:j), this establishes
[the sparse hidden filter depth ratio bounds result](goal). -/
-- @node: sparse_hidden_filter_depth_ratio_bounds
lemma sparse_hidden_filter_depth_ratio_bounds (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) (j : Fin (Q + 1)) :
    0 ≤ (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (j, u))) /
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) ∧
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (j, u))) /
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) ≤ 1 := by
  have hp := sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC n
  constructor
  · apply div_nonneg _ hp.le
    exact Finset.sum_nonneg (fun u _ ↦
      sparse_hidden_filter_nonneg hd t0 zeta C code v x a r ht0 hC n _)
  · exact (div_le_one hp).2
      (sparse_hidden_filter_depth_le_total hd t0 zeta C code v x a r ht0 hC n j)

/-- Normalizing the exact signed-depth reward likelihood gives the observed Bernoulli reward law
with mean c times bias times terminal posterior, as in (8). For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the sample size](hyp:n), and [the y](hyp:y),
this establishes [the sparse hidden filter normalized reward result](goal). -/
-- @node: sparse_hidden_filter_normalized_reward
lemma sparse_hidden_filter_normalized_reward (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) (y : Fin 2) :
    (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h *
      sparseRewardWeight t0 Q h y) /
      (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) =
        (1 + (if y = 0 then -1 else 1 : ℝ) * sparseSignal t0 *
          sparseFilterBias hd zeta C code v x a n Q *
          ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
            (depthSignEquiv Q (Fin.last Q, u))) /
            (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h))) / 2 := by
  rw [sparse_hidden_filter_reward_likelihood hd t0 zeta C ht0 hzeta hC code v]
  have hp := ne_of_gt
    (sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC n)
  field_simp
  <;> ring

/-- The retained sign bias stays between zero and one, including its stationary padding and all
observed advance histories. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action,
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the sample size](hyp:n), and
[the candidate index](hyp:j), this establishes [the sparse filter bias bounds result](goal). -/
-- @node: sparse_filter_bias_bounds
lemma sparse_filter_bias_bounds (hzeta : 0 < zeta) (hC : 1 ≤ C) (n j : Nat) :
    0 ≤ sparseFilterBias hd zeta C code v x a n j ∧
      sparseFilterBias hd zeta C code v x a n j ≤ 1 := by
  have he := sparse_epsilon_bounds C hC
  have hp := sparseRetentionProbability_mem_unitInterval Q zeta hzeta
  induction n generalizing j with
  | zero =>
    simp only [sparseFilterBias]
    constructor
    · exact mul_nonneg he.1 (pow_nonneg hp.1 _)
    · have hpow := pow_le_one₀ hp.1 hp.2 (n := j)
      nlinarith [pow_nonneg hp.1 j]
  | succ n ih =>
    by_cases hj : j = 0
    · simp only [sparseFilterBias, if_pos hj]
      constructor <;> linarith
    · simp only [sparseFilterBias, if_neg hj]
      have hr := sparse_retention_indicator_cases hd code v (x n) (a n)
      rcases hr with hr | hr <;> rw [hr]
      · simp
      · simpa using ih (j - 1)

/-- The normalized observed reward probability has the sharper Bayes lower bound (9), involving
only the normalized terminal depth mass. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the sample size](hyp:n), and [the y](hyp:y),
this establishes [the sparse hidden filter normalized reward lower result](goal). -/
-- @node: sparse_hidden_filter_normalized_reward_lower
lemma sparse_hidden_filter_normalized_reward_lower (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) (y : Fin 2) :
    (1 - sparseSignal t0 *
      ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
        (depthSignEquiv Q (Fin.last Q, u))) /
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h))) / 2 ≤
      (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h *
        sparseRewardWeight t0 Q h y) /
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) := by
  rw [sparse_hidden_filter_normalized_reward hd t0 zeta C code v x a r
    ht0 hzeta hC n y]
  have hc := sparse_signal_bounds t0 ht0
  have hb := sparse_filter_bias_bounds hd zeta C code v x a hzeta hC n Q
  have hz := sparse_hidden_filter_depth_ratio_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC n (Fin.last Q)
  have hcz : 0 ≤ sparseSignal t0 *
      ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
        (depthSignEquiv Q (Fin.last Q, u))) /
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h)) :=
    mul_nonneg hc.1.le hz.1
  split_ifs <;> nlinarith [mul_nonneg hcz hb.1,
    mul_le_mul_of_nonneg_left hb.2 hcz]

end Filter

end CausalSmith.Stat.PomdpPolicyclassRegret
