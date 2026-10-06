module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFilterInformation
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteHistoryFactorization

/-! # Hidden-path realization of the observed filter

Marginalizing the hidden history of a fixed context-action-reward word gives
exactly the recursive filter. Behavior action masses are common factors and
are restored when comparing with the actual generated trajectory law.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Split a hidden history into its prefix and final hidden state. -/
-- @node: finiteHiddenHistorySnocEquiv
def finiteHiddenHistorySnocEquiv (n nH : Nat) :
    (Fin (n + 2) → Fin nH) ≃ (Fin (n + 1) → Fin nH) × Fin nH where
  toFun h := (fun i ↦ h i.castSucc, h (Fin.last (n + 1)))
  invFun z := Fin.lastCases z.2 z.1
  left_inv h := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  right_inv z := by
    apply Prod.ext
    · funext i
      simp
    · simp

section Path

variable {M d Q : Nat} (hd : 0 < d) (t0 zeta C : ℝ)
  (code : Fin M → Fin d → Bool) (v : Fin M)
  (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)

/-- Hidden-path likelihood with the common behavior-action factors removed.
The final context is retained, matching the recursive filter's convention. -/
-- @node: sparseHiddenPathWeight
noncomputable def sparseHiddenPathWeight (n : Nat)
    (h : Fin (n + 1) → Fin (2 * (Q + 1))) : ℝ :=
  (sparseInit hd t0 zeta C code v false (x 0, h 0)).toReal *
    ∏ k : Fin n, sparseRewardWeight t0 Q (h k.castSucc) (r k.val) *
      sparseStateWeight hd t0 C code v false (x k.val, h k.castSucc)
        (x (k.val + 1), h k.succ) (a k.val)

/-- Appending a hidden state multiplies the prefix likelihood by the last reward-transition
weight of the same common kernel. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the sample size](hyp:n),
[the stated assumption](hyp:h), and [the alternate stated assumption](hyp:h'), this establishes
[the sparse hidden path weight snoc result](goal). -/
-- @node: sparse_hidden_path_weight_snoc
lemma sparse_hidden_path_weight_snoc (n : Nat)
    (h : Fin (n + 1) → Fin (2 * (Q + 1))) (h' : Fin (2 * (Q + 1))) :
    sparseHiddenPathWeight hd t0 zeta C code v x a r (n + 1) (Fin.lastCases h' h) =
      sparseHiddenPathWeight hd t0 zeta C code v x a r n h *
        sparseRewardWeight t0 Q (h (Fin.last n)) (r n) *
          sparseStateWeight hd t0 C code v false (x n, h (Fin.last n))
            (x (n + 1), h') (a n) := by
  have hzero : Fin.lastCases h' h (0 : Fin (n + 2)) = h 0 := by
    rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
      Fin.lastCases_castSucc]
  have hnext (k : Fin n) :
      Fin.lastCases h' h k.castSucc.succ = h k.succ := by
    rw [show k.castSucc.succ = k.succ.castSucc by rfl, Fin.lastCases_castSucc]
  simp [sparseHiddenPathWeight, Fin.prod_univ_castSucc, hzero, hnext]
  ring

/-- The forward filter is the exact endpoint marginal of all compatible hidden paths, including
the stationary initial weight. No reset is observed. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the sample size](hyp:n), and
[the alternate stated assumption](hyp:h'), this establishes
[the sparse hidden filter equality path endpoint mass result](goal). -/
-- @node: sparse_hidden_filter_eq_path_endpoint_mass
lemma sparse_hidden_filter_eq_path_endpoint_mass (n : Nat)
    (h' : Fin (2 * (Q + 1))) :
    sparseHiddenFilter hd t0 zeta C code v x a r n h' =
      ∑ h : Fin (n + 1) → Fin (2 * (Q + 1)),
        if h (Fin.last n) = h' then
          sparseHiddenPathWeight hd t0 zeta C code v x a r n h else 0 := by
  classical
  induction n generalizing h' with
  | zero =>
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (2 * (Q + 1))))
      _ (fun u ↦ if u = h' then (sparseInit hd t0 zeta C code v false (x 0, u)).toReal else 0)
      (fun h ↦ by simp [sparseHiddenPathWeight])]
    simp [sparseHiddenFilter]
  | succ n ih =>
    rw [Fintype.sum_equiv (finiteHiddenHistorySnocEquiv n (2 * (Q + 1)))
      _ (fun z ↦ if z.2 = h' then
        sparseHiddenPathWeight hd t0 zeta C code v x a r (n + 1)
          (Fin.lastCases z.2 z.1) else 0)
      (fun h ↦ by
        have he : (fun i ↦ Fin.lastCases (h (Fin.last (n + 1)))
            (fun j ↦ h j.castSucc) i) = h := by
          funext i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
        change (if h (Fin.last (n + 1)) = h' then
          sparseHiddenPathWeight hd t0 zeta C code v x a r (n + 1) h else 0) =
          if h (Fin.last (n + 1)) = h' then
            sparseHiddenPathWeight hd t0 zeta C code v x a r (n + 1)
              (fun i ↦ Fin.lastCases (h (Fin.last (n + 1)))
                (fun j ↦ h j.castSucc) i) else 0
        rw [he])]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [sparse_hidden_path_weight_snoc]
    simp only [sparseHiddenFilter, sparseHiddenFilterStep, ih, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    simp

/-- Summing the endpoint marginal recovers the likelihood of all compatible hidden histories,
without conditioning on any latent coordinate. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, and [the sample size](hyp:n), this establishes
[the sparse hidden filter total equality path mass result](goal). -/
-- @node: sparse_hidden_filter_total_eq_path_mass
lemma sparse_hidden_filter_total_eq_path_mass (n : Nat) :
    (∑ h', sparseHiddenFilter hd t0 zeta C code v x a r n h') =
      ∑ h : Fin (n + 1) → Fin (2 * (Q + 1)),
        sparseHiddenPathWeight hd t0 zeta C code v x a r n h := by
  classical
  simp_rw [sparse_hidden_filter_eq_path_endpoint_mass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp

/-- Restoring the common behavior-action factors turns each hidden-path weight into the
generated chronological prefix likelihood. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the sample size](hyp:n), and
[the stated assumption](hyp:h), this establishes
[the sparse fixed prefix weight equality hidden path weight result](goal). -/
-- @node: sparse_fixed_prefix_weight_eq_hidden_path_weight
lemma sparse_fixed_prefix_weight_eq_hidden_path_weight (ht0 : 0 < t0)
    (hC : 1 ≤ C) (n : Nat) (h : Fin (n + 1) → Fin (2 * (Q + 1))) :
    finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
      (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
      (sparseBehaviorPMF zeta d Q) (fun k : Fin n ↦ (a k.val, r k.val))
      (fun k ↦ (x k.val, h k)) =
      (∏ k : Fin n, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal) *
        sparseHiddenPathWeight hd t0 zeta C code v x a r n h := by
  simp only [finiteFixedPrefixWeight, sparseHiddenPathWeight,
    sparse_kernel_toReal hd t0 C ht0 hC code v false, Bool.false_eq_true,
    if_false, Finset.prod_mul_distrib, Fin.val_castSucc, Fin.val_succ, Fin.val_zero, Nat.add_comm]
  ring

/-- The recursive filter, multiplied by the observed behavior likelihood, is the full
hidden-state marginal of the generated prefix likelihood. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC), and
[the sample size](hyp:n), this establishes
[the sparse fixed prefix hidden marginal equality filter result](goal). -/
-- @node: sparse_fixed_prefix_hidden_marginal_eq_filter
lemma sparse_fixed_prefix_hidden_marginal_eq_filter (ht0 : 0 < t0)
    (hC : 1 ≤ C) (n : Nat) :
    (∑ h : Fin (n + 1) → Fin (2 * (Q + 1)),
      finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
        (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
        (sparseBehaviorPMF zeta d Q) (fun k : Fin n ↦ (a k.val, r k.val))
        (fun k ↦ (x k.val, h k))) =
      (∏ k : Fin n, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal) *
        (∑ h', sparseHiddenFilter hd t0 zeta C code v x a r n h') := by
  simp_rw [sparse_fixed_prefix_weight_eq_hidden_path_weight hd t0 zeta C code v x a r
    ht0 hC]
  rw [← Finset.mul_sum, sparse_hidden_filter_total_eq_path_mass]

/-- The actual generated state-history law, after marginalizing every hidden coordinate, is the
recursive filter with the common behavior factors restored. The final context is fixed, but its
hidden state remains unobserved. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the time horizon](hyp:T),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC), and
[the epoch index](hyp:t), this establishes
[the sparse generated history hidden marginal equality filter result](goal). -/
-- @node: sparse_generated_history_hidden_marginal_eq_filter
lemma sparse_generated_history_hidden_marginal_eq_filter {T : Nat}
    (ht0 : 0 < t0) (hC : 1 ≤ C) (t : Fin T) :
    (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
      (((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law.map
        (finiteHistStateView t))
        (((fun k : Fin t.val ↦ (x k.val, h k.castSucc)),
          (fun k : Fin t.val ↦ (a k.val, r k.val))),
          (x t.val, h (Fin.last t.val)))).toReal) =
      (∏ k : Fin t.val, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal) *
        (∑ h', sparseHiddenFilter hd t0 zeta C code v x a r t.val h') := by
  classical
  have hstates (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) :
      finiteHistoryStates
        (((fun k : Fin t.val ↦ (x k.val, h k.castSucc)),
          (fun k : Fin t.val ↦ (a k.val, r k.val))),
          (x t.val, h (Fin.last t.val))) = (fun k ↦ (x k.val, h k)) := by
    funext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp [finiteHistoryStates]
  simp_rw [finiteHistStateView_mass_toReal, hstates]
  exact sparse_fixed_prefix_hidden_marginal_eq_filter hd t0 zeta C code v x a r
    ht0 hC t.val

end Path

end CausalSmith.Stat.PomdpPolicyclassRegret
