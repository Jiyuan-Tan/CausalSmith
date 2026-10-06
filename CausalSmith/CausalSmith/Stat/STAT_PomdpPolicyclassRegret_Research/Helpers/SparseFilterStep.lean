module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseInitialFilter

/-! # Observed reward and hidden-filter propagation

One-step depth and signed-depth identities for arbitrary incoming hidden
weights. Positive-depth advances have fair preceding rewards and preserve
the incoming sign exactly on the observed retention event. Resets restore
the reset bias. These are the local identities behind (5)--(8) of the KL proof.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Summing the outgoing signed mass keeps reset bias and multiplies every advance sign by the
observed retention indicator. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the fair-reference flag](hyp:fair), [the state](hyp:s), [the action](hyp:a), [the x'](hyp:x'),
and [the j'](hyp:j'), this establishes
[the sparse state weight signed sum at depth result](goal). -/
-- @node: sparse_state_weight_signed_sum_at_depth
lemma sparse_state_weight_signed_sum_at_depth {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x' : Fin (d * hdepth Q)) (j' : Fin (Q + 1)) :
    (∑ u' : Fin 2, sparseStateWeight hd t0 C code v fair s
      (x', depthSignEquiv Q (j', u')) a *
        signValue (hiddenSign Q (depthSignEquiv Q (j', u')))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        (if hiddenDepth Q s.2 = Q then
          if j'.val = 0 then (if fair then 0 else sparseEpsilon C) else 0
        else
          (if j'.val = 0 then
            (1 - mixingAlpha t0) * (if fair then 0 else sparseEpsilon C) else 0) +
          (if j'.val = hiddenDepth Q s.2 + 1 then
            mixingAlpha t0 * retentionIndicator hd code v s.1 a *
              signValue (hiddenSign Q s.2) else 0)) := by
  classical
  rw [Fin.sum_univ_two]
  rcases sparse_retention_indicator_cases hd code v s.1 a with hr | hr <;>
    by_cases hterm : hiddenDepth Q s.2 = Q <;>
    by_cases hj0 : j'.val = 0 <;>
    by_cases hjnext : j'.val = hiddenDepth Q s.2 + 1 <;>
    cases fair <;> generalize hu : hiddenSign Q s.2 = u <;> cases u <;>
    simp [sparseStateWeight, sparse_hidden_depth_enumeration,
      (sparse_hidden_sign_enumeration Q j').1,
      (sparse_hidden_sign_enumeration Q j').2,
      resetSignWeight, signValue, hu, hterm, hj0, hjnext, hr] <;> ring

/-- At a positive outgoing depth, the old depth is necessarily nonterminal; its observed reward
is fair, including advances reaching terminal depth. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the state](hyp:s), [the action](hyp:a), [the x'](hyp:x'), [the j'](hyp:j'),
[the candidate index alternate assumption](hyp:hj'), and [the reward symbol](hyp:r), this
establishes [the sparse reward depth advance mass result](goal). -/
-- @node: sparse_reward_depth_advance_mass
lemma sparse_reward_depth_advance_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x' : Fin (d * hdepth Q)) (j' : Fin (Q + 1)) (hj' : 0 < j'.val)
    (r : Fin 2) :
    sparseRewardWeight t0 Q s.2 r *
      (∑ u' : Fin 2, sparseStateWeight hd t0 C code v false s
        (x', depthSignEquiv Q (j', u')) a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2 *
        (if j'.val = hiddenDepth Q s.2 + 1 then 1 else 0) := by
  rw [sparse_state_weight_sum_at_depth]
  have hj0 : j'.val ≠ 0 := Nat.ne_of_gt hj'
  by_cases hn : j'.val = hiddenDepth Q s.2 + 1
  · have ht : hiddenDepth Q s.2 ≠ Q := by omega
    simp [hj0, ht, hn, sparseRewardWeight]
    ring
  · simp only [if_neg hn]
    by_cases ht : hiddenDepth Q s.2 = Q <;> simp [hj0, ht, hn]

/-- The corresponding outgoing signed mass is the incoming sign times the retention indicator,
with the same fair reward factor. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the state](hyp:s), [the action](hyp:a), [the x'](hyp:x'), [the j'](hyp:j'),
[the candidate index alternate assumption](hyp:hj'), and [the reward symbol](hyp:r), this
establishes [the sparse reward depth advance signed mass result](goal). -/
-- @node: sparse_reward_depth_advance_signed_mass
lemma sparse_reward_depth_advance_signed_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x' : Fin (d * hdepth Q)) (j' : Fin (Q + 1)) (hj' : 0 < j'.val)
    (r : Fin 2) :
    sparseRewardWeight t0 Q s.2 r *
      (∑ u' : Fin 2, sparseStateWeight hd t0 C code v false s
        (x', depthSignEquiv Q (j', u')) a *
          signValue (hiddenSign Q (depthSignEquiv Q (j', u')))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2 *
        retentionIndicator hd code v s.1 a *
          (if j'.val = hiddenDepth Q s.2 + 1 then
            signValue (hiddenSign Q s.2) else 0) := by
  rw [sparse_state_weight_signed_sum_at_depth]
  have hj0 : j'.val ≠ 0 := Nat.ne_of_gt hj'
  by_cases hn : j'.val = hiddenDepth Q s.2 + 1
  · have ht : hiddenDepth Q s.2 ≠ Q := by omega
    simp [hj0, ht, hn, sparseRewardWeight]
    ring
  · simp only [if_neg hn]
    by_cases ht : hiddenDepth Q s.2 = Q <;> simp [hj0, ht, hn]

/-- A new depth-zero sign is a fresh reset sign, even when the old reward was terminal and
informative. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the codeword index](hyp:v), [the state](hyp:s), [the action](hyp:a), and [the x'](hyp:x'), this
establishes [the sparse state weight reset signed mass result](goal). -/
-- @node: sparse_state_weight_reset_signed_mass
lemma sparse_state_weight_reset_signed_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x' : Fin (d * hdepth Q)) :
    (∑ u' : Fin 2, sparseStateWeight hd t0 C code v false s
      (x', depthSignEquiv Q (0, u')) a *
        signValue (hiddenSign Q (depthSignEquiv Q (0, u')))) =
      sparseEpsilon C *
        ∑ u' : Fin 2, sparseStateWeight hd t0 C code v false s
          (x', depthSignEquiv Q (0, u')) a := by
  rw [sparse_state_weight_signed_sum_at_depth, sparse_state_weight_sum_at_depth]
  by_cases ht : hiddenDepth Q s.2 = Q <;> simp [ht] <;> ring

/-- An observed reward and action propagate arbitrary incoming hidden
weights through the displayed common kernel, at the fixed next context. -/
-- @node: sparseHiddenFilterStep
noncomputable def sparseHiddenFilterStep {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2)
    (f : Fin (2 * (Q + 1)) → ℝ) (h' : Fin (2 * (Q + 1))) : ℝ :=
    ∑ h, f h * sparseRewardWeight t0 Q h r *
      sparseStateWeight hd t0 C code v false (x, h) (x', h') a

/-- A positive-depth filter update reads only the previous depth and incurs one advance
probability and one fair reward factor. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the observed state](hyp:x), [the x'](hyp:x'), [the action](hyp:a), [the reward symbol](hyp:r),
[the f](hyp:f), [the candidate index](hyp:j), and [the candidate index assumption](hyp:hj), this
establishes [the sparse hidden filter advance mass result](goal). -/
-- @node: sparse_hidden_filter_advance_mass
lemma sparse_hidden_filter_advance_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2)
    (f : Fin (2 * (Q + 1)) → ℝ) (j : Fin (Q + 1)) (hj : j.val < Q) :
    (∑ u' : Fin 2, sparseHiddenFilterStep hd t0 C code v x x' a r f
      (depthSignEquiv Q (⟨j.val + 1, by omega⟩, u'))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2 *
        ∑ u : Fin 2, f (depthSignEquiv Q (j, u)) := by
  classical
  unfold sparseHiddenFilterStep
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, mul_assoc]
  simp_rw [sparse_reward_depth_advance_mass hd t0 C code v (x, _) a x'
    ⟨j.val + 1, by omega⟩ (by simp) r]
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm _
    (fun z ↦ f (depthSignEquiv Q z) *
      (((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2 *
        (if j.val + 1 = hiddenDepth Q (depthSignEquiv Q z) + 1 then 1 else 0)))
    (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [sparse_hidden_depth_enumeration, Nat.add_right_cancel_iff,
    show ∀ k : Fin (Q + 1), (j.val = k.val) ↔ k = j from
      fun k ↦ by simp [Fin.ext_iff, eq_comm]]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The signed advance update carries exactly the old signed depth mass multiplied by the
observed retention indicator. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the observed state](hyp:x), [the x'](hyp:x'), [the action](hyp:a), [the reward symbol](hyp:r),
[the f](hyp:f), [the candidate index](hyp:j), and [the candidate index assumption](hyp:hj), this
establishes [the sparse hidden filter advance signed mass result](goal). -/
-- @node: sparse_hidden_filter_advance_signed_mass
lemma sparse_hidden_filter_advance_signed_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2)
    (f : Fin (2 * (Q + 1)) → ℝ) (j : Fin (Q + 1)) (hj : j.val < Q) :
    (∑ u' : Fin 2, sparseHiddenFilterStep hd t0 C code v x x' a r f
      (depthSignEquiv Q (⟨j.val + 1, by omega⟩, u')) *
        signValue (hiddenSign Q (depthSignEquiv Q (⟨j.val + 1, by omega⟩, u')))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2 *
        retentionIndicator hd code v x a *
          ∑ u : Fin 2, f (depthSignEquiv Q (j, u)) *
            signValue (hiddenSign Q (depthSignEquiv Q (j, u))) := by
  classical
  unfold sparseHiddenFilterStep
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [sparse_reward_depth_advance_signed_mass hd t0 C code v (x, _) a x'
    ⟨j.val + 1, by omega⟩ (by simp) r]
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm _
    (fun z ↦ f (depthSignEquiv Q z) *
      (((d * hdepth Q : Nat) : ℝ)⁻¹ * mixingAlpha t0 / 2 *
        retentionIndicator hd code v x a *
          (if j.val + 1 = hiddenDepth Q (depthSignEquiv Q z) + 1 then
            signValue (hiddenSign Q (depthSignEquiv Q z)) else 0)))
    (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [sparse_hidden_depth_enumeration, Nat.add_right_cancel_iff,
    show ∀ k : Fin (Q + 1), (j.val = k.val) ↔ k = j from
      fun k ↦ by simp [Fin.ext_iff, eq_comm]]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Arbitrary incoming weights, including an informative old reward, produce the reset bias at
outgoing depth zero. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the x'](hyp:x'), [the action](hyp:a),
[the reward symbol](hyp:r), and [the f](hyp:f), this establishes
[the sparse hidden filter reset signed mass result](goal). -/
-- @node: sparse_hidden_filter_reset_signed_mass
lemma sparse_hidden_filter_reset_signed_mass {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2)
    (f : Fin (2 * (Q + 1)) → ℝ) :
    (∑ u' : Fin 2, sparseHiddenFilterStep hd t0 C code v x x' a r f
      (depthSignEquiv Q (0, u')) *
        signValue (hiddenSign Q (depthSignEquiv Q (0, u')))) =
      sparseEpsilon C * ∑ u' : Fin 2,
        sparseHiddenFilterStep hd t0 C code v x x' a r f
          (depthSignEquiv Q (0, u')) := by
  classical
  unfold sparseHiddenFilterStep
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum,
    sparse_state_weight_reset_signed_mass hd t0 C code v (x, _) a x']
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The reward likelihood of any incoming hidden weights consists of fair mass plus the terminal
signed mass. This is the unnormalized form of (8). For [the hidden-depth scale](hyp:Q),
[the mixing scale](hyp:t0), [the f](hyp:f), and [the reward symbol](hyp:r), this establishes
[the sparse hidden reward likelihood result](goal). -/
-- @node: sparse_hidden_reward_likelihood
lemma sparse_hidden_reward_likelihood (Q : Nat) (t0 : ℝ)
    (f : Fin (2 * (Q + 1)) → ℝ) (r : Fin 2) :
    (∑ h, f h * sparseRewardWeight t0 Q h r) =
      ((∑ h, f h) + (if r = 0 then -1 else 1 : ℝ) * sparseSignal t0 *
        (∑ u : Fin 2, f (depthSignEquiv Q (Fin.last Q, u)) *
          signValue (hiddenSign Q (depthSignEquiv Q (Fin.last Q, u))))) / 2 := by
  classical
  have hterminal : (∑ h, f h * signValue (hiddenSign Q h) *
      (if hiddenDepth Q h = Q then 1 else 0)) =
      ∑ u : Fin 2, f (depthSignEquiv Q (Fin.last Q, u)) *
        signValue (hiddenSign Q (depthSignEquiv Q (Fin.last Q, u))) := by
    rw [Fintype.sum_equiv (depthSignEquiv Q).symm _
      (fun z ↦ f (depthSignEquiv Q z) *
        signValue (hiddenSign Q (depthSignEquiv Q z)) *
          (if hiddenDepth Q (depthSignEquiv Q z) = Q then 1 else 0))
      (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
    simp_rw [sparse_hidden_depth_enumeration,
      show ∀ j : Fin (Q + 1), (j.val = Q) ↔ j = Fin.last Q from
        fun j ↦ by simp [Fin.ext_iff]]
    simp
  rw [← hterminal]
  simp only [sparseRewardWeight, Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Unnormalized hidden weights after a realized observed prefix. The
recursion uses rewards and actions only; resets remain unobserved. -/
-- @node: sparseHiddenFilter
noncomputable def sparseHiddenFilter {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2) :
    Nat → Fin (2 * (Q + 1)) → ℝ
  | 0 => fun h ↦ (sparseInit hd t0 zeta C code v false (x 0, h)).toReal
  | n + 1 => sparseHiddenFilterStep hd t0 C code v (x n) (x (n + 1)) (a n) (r n)
      (sparseHiddenFilter hd t0 zeta C code v x a r n)

/-- The sign bias at a given depth: stationary padding initially, a fresh
reset bias at depth zero, and observed retention on each advance. -/
-- @node: sparseFilterBias
noncomputable def sparseFilterBias {M d Q : Nat} (hd : 0 < d)
    (zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) : Nat → Nat → ℝ
  | 0, j => sparseEpsilon C * sparseRetentionProbability Q zeta ^ j
  | n + 1, j => if j = 0 then sparseEpsilon C else
      retentionIndicator hd code v (x n) (a n) *
        sparseFilterBias hd zeta C code v x a n (j - 1)

/-- At every epoch and depth, the propagated signed mass is exactly the propagated depth mass
times its observed retention bias. This proves the local filtering content of (5)--(7),
including stationary-prefix padding. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the action](hyp:a),
[the reward symbol](hyp:r), [the sample size](hyp:n), and [the candidate index](hyp:j), this
establishes [the sparse hidden filter signed invariant result](goal). -/
-- @node: sparse_hidden_filter_signed_invariant
lemma sparse_hidden_filter_signed_invariant {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)
    (n : Nat) (j : Fin (Q + 1)) :
    (∑ u : Fin 2, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (j, u)) *
        signValue (hiddenSign Q (depthSignEquiv Q (j, u)))) =
      sparseFilterBias hd zeta C code v x a n j.val *
        ∑ u : Fin 2, sparseHiddenFilter hd t0 zeta C code v x a r n
          (depthSignEquiv Q (j, u)) := by
  induction n generalizing j with
  | zero =>
    simp only [sparseHiddenFilter, sparseFilterBias]
    rw [sparse_init_context_depth_signed_mass hd t0 zeta C ht0 hzeta hC code v,
      sparse_init_context_depth_mass hd t0 zeta C ht0 hzeta hC code v]
    ring
  | succ n ih =>
    by_cases hj0 : j.val = 0
    · have hj : j = 0 := Fin.ext hj0
      subst j
      simp only [sparseHiddenFilter, sparseFilterBias, Fin.val_zero, if_pos rfl]
      exact sparse_hidden_filter_reset_signed_mass hd t0 C code v _ _ _ _ _
    · let k : Fin (Q + 1) := ⟨j.val - 1, by omega⟩
      have hk : k.val < Q := by dsimp [k]; omega
      have hj : j = ⟨k.val + 1, by omega⟩ := by
        apply Fin.ext
        dsimp [k]
        omega
      simp only [sparseHiddenFilter, sparseFilterBias, if_neg hj0]
      rw [hj, sparse_hidden_filter_advance_signed_mass hd t0 C code v _ _ _ _ _ k hk,
        sparse_hidden_filter_advance_mass hd t0 C code v _ _ _ _ _ k hk, ih k]
      change _ = retentionIndicator hd code v (x n) (a n) *
        sparseFilterBias hd zeta C code v x a n (k.val + 1 - 1) * _
      rw [Nat.add_sub_cancel]
      ring

/-- The realized reward likelihood at every epoch is fair mass plus the terminal mass times its
retention bias, the finite-filter form of (8). For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the action](hyp:a),
[the reward symbol](hyp:r), [the sample size](hyp:n), and [the y](hyp:y), this establishes
[the sparse hidden filter reward likelihood result](goal). -/
-- @node: sparse_hidden_filter_reward_likelihood
lemma sparse_hidden_filter_reward_likelihood {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)
    (n : Nat) (y : Fin 2) :
    (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h *
      sparseRewardWeight t0 Q h y) =
      ((∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) +
        (if y = 0 then -1 else 1 : ℝ) * sparseSignal t0 *
          (sparseFilterBias hd zeta C code v x a n Q *
            ∑ u : Fin 2, sparseHiddenFilter hd t0 zeta C code v x a r n
              (depthSignEquiv Q (Fin.last Q, u)))) / 2 := by
  rw [sparse_hidden_reward_likelihood,
    sparse_hidden_filter_signed_invariant hd t0 zeta C ht0 hzeta hC code v x a r]
  rfl

/-- The recursive bias equals stationary pre-sample padding times the retention indicators in
the recorded window, precisely (2), (5), and (6). For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the observed state](hyp:x), [the action](hyp:a), [the sample size](hyp:n), and
[the candidate index](hyp:j), this establishes
[the sparse filter bias equality window result](goal). -/
-- @node: sparse_filter_bias_eq_window
lemma sparse_filter_bias_eq_window {M d Q : Nat} (hd : 0 < d)
    (zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (n j : Nat) :
    sparseFilterBias hd zeta C code v x a n j =
      sparseEpsilon C * sparseRetentionProbability Q zeta ^ (j - min j n) *
        ∏ k ∈ Finset.Ico (n - min j n) n,
          retentionIndicator hd code v (x k) (a k) := by
  induction n generalizing j with
  | zero => simp [sparseFilterBias]
  | succ n ih =>
    by_cases hj : j = 0
    · subst j
      simp [sparseFilterBias]
    · have hstart : n + 1 - min j (n + 1) = n - min (j - 1) n := by omega
      have hpad : j - min j (n + 1) = j - 1 - min (j - 1) n := by omega
      rw [sparseFilterBias, if_neg hj, ih, hstart, hpad,
        Finset.prod_Ico_succ_top (Nat.sub_le n (min (j - 1) n))]
      ring

/-- The signed-depth invariant with the explicit stationary or complete observed window. No
reward, reset, or latent observation enters the bias. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the action](hyp:a),
[the reward symbol](hyp:r), [the sample size](hyp:n), and [the candidate index](hyp:j), this
establishes [the sparse hidden filter signed window result](goal). -/
-- @node: sparse_hidden_filter_signed_window
lemma sparse_hidden_filter_signed_window {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)
    (n : Nat) (j : Fin (Q + 1)) :
    (∑ u : Fin 2, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (j, u)) *
        signValue (hiddenSign Q (depthSignEquiv Q (j, u)))) =
      (sparseEpsilon C * sparseRetentionProbability Q zeta ^ (j.val - min j.val n) *
        ∏ k ∈ Finset.Ico (n - min j.val n) n,
          retentionIndicator hd code v (x k) (a k)) *
        ∑ u : Fin 2, sparseHiddenFilter hd t0 zeta C code v x a r n
          (depthSignEquiv Q (j, u)) := by
  rw [sparse_hidden_filter_signed_invariant hd t0 zeta C ht0 hzeta hC,
    sparse_filter_bias_eq_window]

end CausalSmith.Stat.PomdpPolicyclassRegret
