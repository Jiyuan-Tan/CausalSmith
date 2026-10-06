module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseObservedRewardAveraging
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TSparsePackingMembership

/-! # Finite-word certificate for the sparse-context observed law

Epoch `t : Fin T` corresponds to paper epoch `t + 1`, so the recorded
retention window has length `min Q t.val`. The pre-reward history contains
the past observed triples and the current context and action. Finite Bayes
sums define the conditional signed reward mean and terminal-depth posterior
from the actual stationary behavior law, before asserting their identities.
The fair law and the alternative use the same selected separated code at
`codeDimension M = ceil (24 log M)`; no reset indicator is observed.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- The finite value of the paper's pre-reward observed history `G_t^-`. -/
def contextualPreRewardHistory {T d Q : Nat} (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    SparseRewardHistory t.val (d * hdepth Q) :=
  (((fun i ↦ (w (prefixIndex t i)).1),
    (fun i ↦ (w (prefixIndex t i)).2)), (w t).1, (w t).2.1)

/-- `E[2 Y_t - 1 | G_t^-]`, computed from actual joint reward/history masses. -/
noncomputable def contextualConditionalRewardMean {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  let H := contextualPreRewardHistory t w
  (∑ y : Fin 2, (if y = 0 then -1 else 1 : ℝ) *
    sparseRewardHistoryRewardMass hd t0 zeta C code v t H y) /
      sparseRewardHistoryMass hd t0 zeta C code v t H

/-- `Pr(J_t = Q | G_t^-)`, with all compatible hidden prefixes marginalized. -/
noncomputable def contextualTerminalPosterior {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ := by
  classical
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  let H := contextualPreRewardHistory t w
  exact (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
    if hiddenDepth Q (h (Fin.last t.val)) = Q then
      ((F.law.map (finiteHistActionPair t))
        ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))).symm
          (H, h))).toReal else 0) /
    sparseRewardHistoryMass hd t0 zeta C code v t H
  -- @realizes z_vt(terminal-depth posterior given past triples and current context-action)

/-- The finite Bayes signed reward mean equals the chronological filter mean. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the contextual conditional reward mean equality filter result](goal). -/
-- @node: contextualConditionalRewardMean_eq_filter
lemma contextualConditionalRewardMean_eq_filter {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    contextualConditionalRewardMean hd t0 zeta C code v t w =
      sparseObservedRewardMean hd t0 zeta C code v t w := by
  rw [sparse_observed_reward_mean_eq_history_mean]
  dsimp only [contextualConditionalRewardMean, contextualPreRewardHistory]
  rw [Finset.sum_div]
  simp_rw [mul_div_assoc, sparse_reward_history_normalized_reward hd t0 zeta C
    ht0 hzeta hC code v t]
  rw [Fin.sum_univ_two]
  norm_num
  ring

/-- The actual observed likelihood factors using the explicitly conditioned means. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the v0](hyp:v0), and
[the observed word](hyp:w), this establishes [the contextual likelihood product result](goal). -/
-- @node: contextual_likelihood_product
lemma contextual_likelihood_product {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 0 < T) (code : Fin M → Fin d → Bool) (v v0 : Fin M)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    (sparseObservedPMF hd t0 zeta C code v false w).toReal =
      (sparseObservedPMF hd t0 zeta C code v0 true w).toReal *
        ∏ t : Fin T, (1 + (if (w t).2.2 = 0 then -1 else 1 : ℝ) *
          contextualConditionalRewardMean hd t0 zeta C code v t w) := by
  simp_rw [contextualConditionalRewardMean_eq_filter hd t0 zeta C ht0 hzeta hC]
  let x := fun k ↦ (sparseObservedWordExtension hd w k).1
  let a := fun k ↦ (sparseObservedWordExtension hd w k).2.1
  let r := fun k ↦ (sparseObservedWordExtension hd w k).2.2
  have hw : (fun k : Fin T ↦ (x k.val, a k.val, r k.val)) = w := by
    funext k
    simp [x, a, r, sparseObservedWordExtension, k.isLt]
  have h := sparse_observed_full_likelihood_product hd t0 zeta C ht0 hzeta hC hT
    code v v0 x a r
  rw [hw] at h
  rw [h, ← Fin.prod_univ_eq_prod_range]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  simp [sparseObservedRewardMean, x, a, r, sparseObservedWordExtension, k.isLt]

/-- The contextual Bayes quotient is the normalized terminal forward-filter mass. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the contextual terminal posterior equality filter result](goal). -/
-- @node: contextualTerminalPosterior_eq_filter
lemma contextualTerminalPosterior_eq_filter {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    contextualTerminalPosterior hd t0 zeta C code v t w =
      let x := fun n ↦ (sparseObservedWordExtension hd w n).1
      let a := fun n ↦ (sparseObservedWordExtension hd w n).2.1
      let r := fun n ↦ (sparseObservedWordExtension hd w n).2.2
      (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r t.val
        (depthSignEquiv Q (Fin.last Q, u))) /
        (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r t.val h) := by
  classical
  let H := contextualPreRewardHistory t w
  let x := fun n ↦ (sparseRewardHistoryExtension H n).1
  let a := fun n ↦ (sparseRewardHistoryExtension H n).2.1
  let r := fun n ↦ (sparseRewardHistoryExtension H n).2.2
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  let mass := fun h : Fin (t.val + 1) → Fin (2 * (Q + 1)) ↦
    ((F.law.map (finiteHistStateView t))
      (((fun k : Fin t.val ↦ (x k.val, h k.castSucc)),
        (fun k : Fin t.val ↦ (a k.val, r k.val))),
        (x t.val, h (Fin.last t.val)))).toReal
  let filt := sparseHiddenFilter hd t0 zeta C code v x a r t.val
  have hnum := sparse_generated_history_endpoint_expectation_eq_filter hd t0 zeta C
    code v x a r ht0 hC t (fun h ↦ if hiddenDepth Q h = Q then 1 else 0)
  have hden := sparse_generated_history_hidden_marginal_eq_filter hd t0 zeta C
    code v x a r ht0 hC t
  have hterm : (∑ h, filt h * (if hiddenDepth Q h = Q then 1 else 0)) =
      ∑ u, filt (depthSignEquiv Q (Fin.last Q, u)) := by
    rw [← (depthSignEquiv Q).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [sparse_hidden_depth_enumeration, mul_ite, mul_one, mul_zero]
    have hi (j : Fin (Q + 1)) : j.val = Q ↔ j = Fin.last Q := by
      constructor
      · intro h; exact Fin.ext h
      · rintro rfl; rfl
    simp_rw [hi]
    simp
  change (∑ h, mass h * (if hiddenDepth Q (h (Fin.last t.val)) = Q then 1 else 0)) =
    _ * ∑ h, filt h * (if hiddenDepth Q h = Q then 1 else 0) at hnum
  change (∑ h, mass h) = _ * ∑ h, filt h at hden
  have hb : (sparseBehaviorPMF zeta d Q (x t.val) (a t.val)).toReal ≠ 0 := by
    rw [sparse_behavior_pmf_toReal zeta hzeta]
    exact (sparse_behavior_weight_pos zeta hzeta _).ne'
  have hm (h : Fin (t.val + 1) → Fin (2 * (Q + 1))) :
      ((F.law.map (finiteHistActionPair t))
        ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))).symm
          (H, h))).toReal =
      mass h * (sparseBehaviorPMF zeta d Q (x t.val) (a t.val)).toReal := by
    simpa [F, mass, x, a, r, sparseRewardHistoryHiddenEquiv,
      sparseRewardHistoryExtension, Fin.isLt] using
      sparse_generated_action_history_mass hd t0 zeta C code v x a r t h
  have hquot : contextualTerminalPosterior hd t0 zeta C code v t w =
      (∑ u, filt (depthSignEquiv Q (Fin.last Q, u))) / ∑ h, filt h := by
    dsimp only [contextualTerminalPosterior, sparseRewardHistoryMass]
    change (∑ h, if hiddenDepth Q (h (Fin.last t.val)) = Q then
      ((F.law.map (finiteHistActionPair t))
        ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))).symm
          (H, h))).toReal else 0) /
      (∑ h, ((F.law.map (finiteHistActionPair t))
        ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))).symm
          (H, h))).toReal) = _
    simp_rw [hm]
    have hi (p : Prop) [Decidable p] (u b : ℝ) : (if p then u * b else 0) =
        (if p then u else 0) * b := by split_ifs <;> simp
    simp_rw [hi]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [mul_div_mul_right _ _ hb]
    simp only [mul_ite, mul_one, mul_zero] at hnum hterm
    rw [hnum, hden, mul_div_mul_left _ _
      (sparse_observed_behavior_history_weight_pos zeta x a hzeta t.val).ne', hterm]
  rw [hquot]
  have hx (n : Nat) (hn : n ≤ t.val) :
      x n = (sparseObservedWordExtension hd w n).1 := by
    have hnT : n < T := lt_of_le_of_lt hn t.isLt
    by_cases hnt : n < t.val
    · simp [x, H, contextualPreRewardHistory, sparseObservedWordExtension,
        sparseRewardHistoryExtension, hnT, hnt, prefixIndex]
    · have heq : n = t.val := by omega
      subst n
      simp [x, H, contextualPreRewardHistory, sparseObservedWordExtension,
        sparseRewardHistoryExtension, t.isLt]
  have hao (n : Nat) (hn : n < t.val) :
      (sparseRewardHistoryExtension H n).2 = (sparseObservedWordExtension hd w n).2 := by
    have hnT : n < T := lt_trans hn t.isLt
    simp [H, contextualPreRewardHistory, sparseObservedWordExtension,
      sparseRewardHistoryExtension, hnT, hn, prefixIndex]
  dsimp only [filt]
  rw [sparse_hidden_filter_prefix_congr hd t0 zeta C code v _ _ _ _ _ _ t.val
    hx (fun n hn ↦ congrArg Prod.fst (hao n hn))
      (fun n hn ↦ congrArg Prod.snd (hao n hn))]

/-- The forced terminal path gives the observed retention factor in the conditional mean. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the contextual conditional reward mean equality retention result](goal). -/
-- @node: contextualConditionalRewardMean_eq_retention
lemma contextualConditionalRewardMean_eq_retention {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    contextualConditionalRewardMean hd t0 zeta C code v t w =
      sparseSignal t0 * sparseEpsilon C * retentionFactor hd zeta code v t w *
        contextualTerminalPosterior hd t0 zeta C code v t w := by
  rw [contextualConditionalRewardMean_eq_filter hd t0 zeta C ht0 hzeta hC,
    contextualTerminalPosterior_eq_filter hd t0 zeta C ht0 hzeta hC]
  dsimp only [sparseObservedRewardMean]
  rw [sparse_filter_bias_eq_window]
  have hset : (Finset.range T).filter
      (fun k ↦ t.val - min Q t.val ≤ k ∧ k < t.val) =
      Finset.Ico (t.val - min Q t.val) t.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hret : retentionFactor hd zeta code v t w =
      sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
        ∏ k ∈ Finset.Ico (t.val - min Q t.val) t.val,
          retentionIndicator hd code v (sparseObservedWordExtension hd w k).1
            (sparseObservedWordExtension hd w k).2.1 := by
    dsimp only [retentionFactor]
    rw [hset]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have hkT : k < T := lt_trans (Finset.mem_Ico.mp hk).2 t.isLt
    simp [sparseObservedWordExtension, hkT]
  rw [hret]
  ring

/-- The uniform filter bound applies to every explicitly conditioned observed history. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the contextual terminal posterior bound result](goal). -/
-- @node: contextualTerminalPosterior_le
lemma contextualTerminalPosterior_le {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    contextualTerminalPosterior hd t0 zeta C code v t w ≤
      filterConstant t0 * mixingAlpha t0 ^ Q := by
  rw [contextualTerminalPosterior_eq_filter hd t0 zeta C ht0 hzeta hC]
  exact sparse_hidden_filter_uniform_bound hd t0 zeta C ht0 hzeta hC code v
    (fun n ↦ (sparseObservedWordExtension hd w n).1)
    (fun n ↦ (sparseObservedWordExtension hd w n).2.1)
    (fun n ↦ (sparseObservedWordExtension hd w n).2.2) t.val

/-- Separate a state history into its observed past, fresh context, and hidden path. -/
-- @node: contextualStateHistoryEquiv
def contextualStateHistoryEquiv (k nX nH : Nat) :
    (((Fin k → JointState nX nH) × (Fin k → Bool × Fin 2)) × JointState nX nH) ≃
      ((Fin k → Fin nX) × (Fin k → Bool × Fin 2)) ×
        (Fin nX × (Fin (k + 1) → Fin nH)) where
  toFun h := (((fun i ↦ (h.1.1 i).1), h.1.2),
    h.2.1, Fin.lastCases h.2.2 (fun i ↦ (h.1.1 i).2))
  invFun z := (((fun i ↦ (z.1.1 i, z.2.2 i.castSucc)), z.1.2),
    (z.2.1, z.2.2 (Fin.last k)))
  left_inv h := by
    rcases h with ⟨⟨s, o⟩, x, u⟩
    simp
  right_inv z := by
    rcases z with ⟨⟨x, o⟩, c, h⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

open Classical in
/-- Marginalizing full trajectories with an observed past fixed sums precisely all fresh
contexts and all compatible hidden histories. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH), [the event family](hyp:F),
[the epoch index](hyp:t), [the observed word](hyp:w), and [the g](hyp:g), this establishes
[the contextual past endpoint sum result](goal). -/
-- @node: contextual_past_endpoint_sum
lemma contextual_past_endpoint_sum {T nX nH : Nat}
    (F : FiniteRewardModel T nX nH 2) (t : Fin T)
    (w : FiniteObsView T nX 2) (g : Fin nH → ℝ) :
    (∑ tau, if observedPrefixAgrees t (finObsProj tau) w then
      (F.law tau).toReal * g (tau.1 t.castSucc).2 else 0) =
    ∑ c : Fin nX, ∑ h : Fin (t.val + 1) → Fin nH,
      ((F.law.map (finiteHistStateView t))
        (((fun i ↦ ((w (prefixIndex t i)).1, h i.castSucc)),
          (fun i ↦ (w (prefixIndex t i)).2)),
          (c, h (Fin.last t.val)))).toReal * g (h (Fin.last t.val)) := by
  classical
  let past := ((fun i ↦ (w (prefixIndex t i)).1),
    (fun i ↦ (w (prefixIndex t i)).2))
  let e := contextualStateHistoryEquiv t.val nX nH
  have hp (tau : FiniteTrajectory T nX nH 2) :
      (e (finiteHistStateView t tau)).1 = past ↔
        observedPrefixAgrees t (finObsProj tau) w := by
    change ((fun i ↦ (tau.1 (prefixIndex t i).castSucc).1),
      (fun i ↦ tau.2 (prefixIndex t i))) = past ↔ _
    simp only [past, Prod.mk.injEq, funext_iff, observedPrefixAgrees, finObsProj]
    constructor
    · rintro ⟨hx, ho⟩ r hr
      apply Prod.ext
      · simpa [prefixIndex] using hx ⟨r.val, hr⟩
      · simpa [prefixIndex] using ho ⟨r.val, hr⟩
    · intro hh
      constructor
      · intro i; exact congrArg Prod.fst (hh (prefixIndex t i) i.isLt)
      · intro i; exact congrArg Prod.snd (hh (prefixIndex t i) i.isLt)
  have hm := finitePMF_map_sum F.law (finiteHistStateView t)
    (fun H ↦ if (e H).1 = past then
      g ((e H).2.2 (Fin.last t.val)) else 0)
  simp only [hp] at hm
  simp only [e, contextualStateHistoryEquiv, Equiv.coe_fn_mk, finiteHistStateView,
    Fin.lastCases_last, mul_ite, mul_zero] at hm
  rw [← hm, ← e.symm.sum_comp]
  simp [e, contextualStateHistoryEquiv, Equiv.coe_fn_mk,
    Fintype.sum_prod_type, past]

/-- The fresh current context does not change the unnormalized hidden filter. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the x'](hyp:x'), [the action](hyp:a),
[the reward symbol](hyp:r), [the sample size](hyp:n), and
[the observed state assumption](hyp:hx), this establishes
[the sparse hidden filter fresh context congr result](goal). -/
-- @node: sparse_hidden_filter_fresh_context_congr
lemma sparse_hidden_filter_fresh_context_congr {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)
    (n : Nat) (hx : ∀ k < n, x k = x' k) :
    sparseHiddenFilter hd t0 zeta C code v x a r n =
      sparseHiddenFilter hd t0 zeta C code v x' a r n := by
  cases n with
  | zero =>
    funext h
    simp only [sparseHiddenFilter,
      sparse_init_eq_signed_density hd t0 zeta C ht0 hzeta hC code v,
      sparseSignedDensity]
  | succ n =>
    rw [sparseHiddenFilter, sparseHiddenFilter,
      sparse_hidden_filter_prefix_congr hd t0 zeta C code v x x' a a r r n
        (fun k hk ↦ hx k (by omega)) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl),
      hx n (by omega)]
    rfl

open Classical in
/-- The past-only endpoint expectation has a common context and behavior factor, independent of
the endpoint test function. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), [the observed word](hyp:w), and
[the g](hyp:g), this establishes [the contextual past filter expectation result](goal). -/
-- @node: contextual_past_filter_expectation
lemma contextual_past_filter_expectation {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) (g : Fin (2 * (Q + 1)) → ℝ) :
    let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
    let x := fun n ↦ (sparseObservedWordExtension hd w n).1
    let a := fun n ↦ (sparseObservedWordExtension hd w n).2.1
    let r := fun n ↦ (sparseObservedWordExtension hd w n).2.2
    (∑ tau, if observedPrefixAgrees t (finObsProj tau) w then
      (F.law tau).toReal * g (tau.1 t.castSucc).2 else 0) =
    ((d * hdepth Q : Nat) : ℝ) *
      (∏ k : Fin t.val, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal) *
      ∑ h, sparseHiddenFilter hd t0 zeta C code v x a r t.val h * g h := by
  classical
  dsimp only
  rw [contextual_past_endpoint_sum]
  let x := fun n ↦ (sparseObservedWordExtension hd w n).1
  let a := fun n ↦ (sparseObservedWordExtension hd w n).2.1
  let r := fun n ↦ (sparseObservedWordExtension hd w n).2.2
  let A := ∏ k : Fin t.val, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal
  let f := sparseHiddenFilter hd t0 zeta C code v x a r t.val
  have hc (c : Fin (d * hdepth Q)) :
      (∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
        (((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law.map
          (finiteHistStateView t))
          (((fun i ↦ ((w (prefixIndex t i)).1, h i.castSucc)),
            (fun i ↦ (w (prefixIndex t i)).2)),
            (c, h (Fin.last t.val)))).toReal * g (h (Fin.last t.val))) =
        A * ∑ h, f h * g h := by
    let xc := fun n ↦ if n = t.val then c else x n
    have hxc (n : Nat) (hn : n < t.val) : xc n = x n := by
      simp [xc, Nat.ne_of_lt hn]
    have hx (i : Fin t.val) : xc i.val = (w (prefixIndex t i)).1 := by
      rw [hxc i.val i.isLt]
      simp [x, sparseObservedWordExtension, lt_trans i.isLt t.isLt, prefixIndex]
    have hao (i : Fin t.val) : (a i.val, r i.val) = (w (prefixIndex t i)).2 := by
      simp [a, r, sparseObservedWordExtension, lt_trans i.isLt t.isLt, prefixIndex]
    have he := sparse_generated_history_endpoint_expectation_eq_filter hd t0 zeta C
      code v xc a r ht0 hC t g
    simp_rw [hx, hao] at he
    simp only [xc, if_pos rfl] at he
    rw [sparse_hidden_filter_fresh_context_congr hd t0 zeta C ht0 hzeta hC
      code v xc x a r t.val hxc] at he
    have ha : (∏ k : Fin t.val,
        (sparseBehaviorPMF zeta d Q (xc k.val) (a k.val)).toReal) = A := by
      apply Finset.prod_congr rfl
      intro k _
      rw [hxc k.val k.isLt]
    simp_rw [hx] at ha
    rw [ha] at he
    exact he
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [A, f, x, a, r]
  ring

/-- Fresh context and memoryless behavior action carry no extra information about terminal depth
after the observed past is fixed. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the contextual terminal posterior equality terminal posterior result](goal). -/
-- @node: contextualTerminalPosterior_eq_terminalPosterior
lemma contextualTerminalPosterior_eq_terminalPosterior {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    contextualTerminalPosterior hd t0 zeta C code v t w =
      terminalPosterior hd t0 zeta C code v t w := by
  classical
  rw [contextualTerminalPosterior_eq_filter hd t0 zeta C ht0 hzeta hC]
  let x := fun n ↦ (sparseObservedWordExtension hd w n).1
  let a := fun n ↦ (sparseObservedWordExtension hd w n).2.1
  let r := fun n ↦ (sparseObservedWordExtension hd w n).2.2
  let f := sparseHiddenFilter hd t0 zeta C code v x a r t.val
  let A := ((d * hdepth Q : Nat) : ℝ) *
    ∏ k : Fin t.val, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal
  have hn := contextual_past_filter_expectation hd t0 zeta C ht0 hzeta hC
    code v t w (fun h ↦ if hiddenDepth Q h = Q then 1 else 0)
  have hd' := contextual_past_filter_expectation hd t0 zeta C ht0 hzeta hC
    code v t w (fun _ ↦ 1)
  have hnum : terminalPrefixMass hd t0 zeta C code v t w =
      A * ∑ h, f h * (if hiddenDepth Q h = Q then 1 else 0) := by
    simpa only [terminalPrefixMass, mul_ite, mul_one, mul_zero, ite_and] using hn
  have hden : observedPrefixMass hd t0 zeta C code v t w = A * ∑ h, f h := by
    simpa only [observedPrefixMass, mul_one] using hd'
  have hA : A ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
    · exact (sparse_observed_behavior_history_weight_pos zeta x a hzeta t.val).ne'
  have hterm : (∑ h, f h * (if hiddenDepth Q h = Q then 1 else 0)) =
      ∑ u, f (depthSignEquiv Q (Fin.last Q, u)) := by
    rw [← (depthSignEquiv Q).sum_comp, Fintype.sum_prod_type]
    simp only [sparse_hidden_depth_enumeration, mul_ite, mul_one, mul_zero]
    have hi (j : Fin (Q + 1)) : j.val = Q ↔ j = Fin.last Q := by
      constructor
      · intro h; exact Fin.ext h
      · rintro rfl; rfl
    simp_rw [hi]
    simp
  rw [terminalPosterior, hnum, hden, mul_div_mul_left _ _ hA, hterm]

/-- The conditional means, pointwise likelihood product, exact retention moments and observed KL
budget, including every stationary initial window. The posterior equality identifies
conditioning on `G_t^-` with the existing likelihood handle's prefix posterior, since the
current context and behavior action supply no additional hidden-depth information. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the contextual observed word certificate result](goal). -/
-- @node: thm:contextual-observed-word-certificate
theorem contextual_observed_word_certificate (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    resetRatio t0 < 1 ∧
      ∀ (T M Q : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) (hQ : 1 ≤ Q)
        (C : ℝ) (hC : 1 < C)
        (code : Fin M → Fin (codeDimension M) → Bool)
        (hCode : CodeSeparated code) (v : Fin M),
        let hd := codeDimension_pos M hM
        let p := sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false
        let p0 := sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true
        let a := retentionFactor (T := T) (Q := Q) hd zeta code v
        let z := contextualTerminalPosterior (T := T) (Q := Q) hd t0 zeta C code v
        let m := contextualConditionalRewardMean (T := T) (Q := Q) hd t0 zeta C code v
        (∀ (t : Fin T) (w : FiniteObsView T (codeDimension M * hdepth Q) 2),
          z t w = terminalPosterior hd t0 zeta C code v t w ∧
          m t w = sparseSignal t0 * sparseEpsilon C * a t w * z t w ∧
          z t w ≤ filterConstant t0 * mixingAlpha t0 ^ Q) ∧
        (∀ w : FiniteObsView T (codeDimension M * hdepth Q) 2,
          0 < (p0 w).toReal ∧
          (p w).toReal = (p0 w).toReal *
            ∏ t : Fin T, (1 + (if (w t).2.2 = 0 then -1 else 1 : ℝ) * m t w)) ∧
        (∀ t : Fin T,
          (∑ w : FiniteObsView T (codeDimension M * hdepth Q) 2,
            (p w).toReal * a t w ^ 2) =
              sparseRetentionProbability Q zeta ^ (2 * Q - min Q t.val) ∧
          sparseRetentionProbability Q zeta ^ (2 * Q - min Q t.val) ≤
            Real.exp (policyFactor zeta - 1) * policyFactor zeta ^ (-(Q : ℤ))) ∧
        (InformationTheory.klDiv
          (obsLaw (sparsePackingExperiment T M (codeDimension M) Q
            hd rfl hM t0 zeta C code hCode v).Mx.toRawB)
          (sparseReferenceLaw T M (codeDimension M) Q
            hd (by omega) t0 zeta C code)).toReal ≤
          klConstant t0 zeta * T * overlapRadius C ^ 2 *
            mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ)) := by
  refine ⟨resetRatio_lt_one t0 ht0, ?_⟩
  intro T M Q hT hM hQ C hC code hCode v
  dsimp only
  let hd := codeDimension_pos M hM
  have hC' : 1 ≤ C := hC.le
  have hT' : 0 < T := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t w
    refine ⟨?_, contextualConditionalRewardMean_eq_retention hd t0 zeta C
      ht0 hzeta hC' code v t w,
      contextualTerminalPosterior_le hd t0 zeta C ht0 hzeta hC' code v t w⟩
    exact contextualTerminalPosterior_eq_terminalPosterior hd t0 zeta C
      ht0 hzeta hC' code v t w
  · intro w
    exact ⟨sparse_fair_observed_pmf_pos hd t0 zeta C ht0 hzeta hC' code
      ⟨0, by omega⟩ w,
      contextual_likelihood_product hd t0 zeta C ht0 hzeta hC' hT'
        code v ⟨0, by omega⟩ w⟩
  · intro t
    refine ⟨sparse_observed_retention_second_moment hd t0 zeta C
      ht0 hzeta hC' code v t, ?_⟩
    obtain ⟨hp0, hp1⟩ := sparseRetentionProbability_mem_unitInterval Q zeta hzeta
    exact le_trans (pow_le_pow_of_le_one hp0 hp1 (by omega))
      (sparseRetentionProbability_pow_le Q zeta hzeta)
  · have hfinite := sparse_observed_klDiv_ne_top (T := T) (Q := Q) hd
      t0 zeta C ht0 hzeta hC' code v ⟨0, by omega⟩
    have hdecode := embed_klDiv_le
      (F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)
      (G := sparseFinite (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true) rfl
    exact le_trans (ENNReal.toReal_mono hfinite hdecode)
      (sparse_observed_klDiv_le_budget hd t0 zeta C ht0 hzeta hC' hT'
        code v ⟨0, by omega⟩)

end CausalSmith.Stat.PomdpPolicyclassRegret
