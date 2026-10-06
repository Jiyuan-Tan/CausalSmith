module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseGeneratedLikelihood

/-! # Hidden fibers of the full observed trajectory

The observer's full word is obtained by summing hidden prefixes and the final
joint state. This connects the generated chronological likelihood to the
observed-word information calculation, without observing a reset indicator.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Separate an observed word from its hidden prefix and final joint state. -/
-- @node: finiteObservedHiddenEquiv
def finiteObservedHiddenEquiv (T nX nH nR : Nat) :
    FiniteTrajectory T nX nH nR ≃
      FiniteObsView T nX nR × (Fin T → Fin nH) × JointState nX nH where
  toFun tau := (finObsProj tau, (fun k ↦ (tau.1 k.castSucc).2), tau.1 (Fin.last T))
  invFun z := (Fin.lastCases z.2.2 (fun k ↦ ((z.1 k).1, z.2.1 k)),
    fun k ↦ (z.1 k).2)
  left_inv tau := by
    apply Prod.ext
    · funext k
      refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp [finObsProj]
    · rfl
  right_inv z := by
    apply Prod.ext
    · funext k
      simp [finObsProj]
    · apply Prod.ext
      · funext k
        simp
      · simp

/-- The observed atom mass is the sum over precisely its compatible hidden prefixes and final
joint states, including the unrecorded successor context. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the reward-symbol count](hyp:nR), [the event family](hyp:F), and [the observed word](hyp:w),
this establishes [the finite observed mass equality hidden fiber sum result](goal). -/
-- @node: finite_observed_mass_eq_hidden_fiber_sum
lemma finite_observed_mass_eq_hidden_fiber_sum {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (w : FiniteObsView T nX nR) :
    (F.obsPMF w).toReal =
      ∑ h : Fin T → Fin nH, ∑ s : JointState nX nH,
        (F.law (Fin.lastCases s (fun k ↦ ((w k).1, h k)),
          fun k ↦ (w k).2)).toReal := by
  classical
  have hm := finiteRewardModel_observed_sum F (fun u ↦ if u = w then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hm
  rw [hm]
  rw [Fintype.sum_equiv (finiteObservedHiddenEquiv T nX nH nR)
    _ (fun z ↦ if z.1 = w then
      (F.law ((finiteObservedHiddenEquiv T nX nH nR).symm z)).toReal else 0)
    (fun tau ↦ by
      rw [Equiv.symm_apply_apply]
      rfl)]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [finiteObservedHiddenEquiv]

/-- The mass of a full chronological path is its real prefix weight, with all reward-transition
factors from the same kernel. For [the time horizon](hyp:T), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the reward-symbol count](hyp:nR), [the event family](hyp:F),
[the o](hyp:o), and [the sigma](hyp:sigma), this establishes
[the finite full path mass equality prefix weight result](goal). -/
-- @node: finite_full_path_mass_eq_prefix_weight
lemma finite_full_path_mass_eq_prefix_weight {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR)
    (o : Fin T → Bool × Fin nR) (sigma : Fin (T + 1) → JointState nX nH) :
    (F.law (sigma, o)).toReal =
      finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b o sigma := by
  rw [F.law_generated, ENNReal.toReal_mul, ENNReal.toReal_prod]
  simp only [finiteFixedPrefixWeight, ENNReal.toReal_mul]

/-- The full observed mass is the hidden-fiber sum of the chronological prefix likelihood, so
the filter path identities apply at the final epoch. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the reward-symbol count](hyp:nR), [the event family](hyp:F), and [the observed word](hyp:w),
this establishes [the finite observed mass equality prefix weight sum result](goal). -/
-- @node: finite_observed_mass_eq_prefix_weight_sum
lemma finite_observed_mass_eq_prefix_weight_sum {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (w : FiniteObsView T nX nR) :
    (F.obsPMF w).toReal =
      ∑ h : Fin T → Fin nH, ∑ s : JointState nX nH,
        finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b
          (fun k ↦ (w k).2) (Fin.lastCases s (fun k ↦ ((w k).1, h k))) := by
  rw [finite_observed_mass_eq_hidden_fiber_sum]
  simp_rw [finite_full_path_mass_eq_prefix_weight]

/-- Split a hidden path at its final state, including paths of length zero. -/
-- @node: finiteHiddenPrefixEquiv
def finiteHiddenPrefixEquiv (T nH : Nat) :
    (Fin (T + 1) → Fin nH) ≃ (Fin T → Fin nH) × Fin nH where
  toFun h := (fun k ↦ h k.castSucc, h (Fin.last T))
  invFun z := Fin.lastCases z.2 z.1
  left_inv h := by
    funext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp
  right_inv z := by
    apply Prod.ext
    · funext k
      simp
    · simp

/-- Changing the unobserved final context leaves a positive-length sparse prefix likelihood
unchanged. Fresh contexts have a common uniform weight. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x),
[the action](hyp:a), [the reward symbol](hyp:r), [the stated assumption](hyp:h), and
[the c](hyp:c), this establishes [the sparse prefix weight final context equality result](goal). -/
-- @node: sparse_prefix_weight_final_context_eq
lemma sparse_prefix_weight_final_context_eq {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C) (hT : 0 < T)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)
    (h : Fin (T + 1) → Fin (2 * (Q + 1))) (c : Fin (d * hdepth Q)) :
    finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
      (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
      (sparseBehaviorPMF zeta d Q) (fun k : Fin T ↦ (a k.val, r k.val))
      (Fin.lastCases (c, h (Fin.last T)) (fun k ↦ (x k.val, h k.castSucc))) =
    finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
      (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
      (sparseBehaviorPMF zeta d Q) (fun k : Fin T ↦ (a k.val, r k.val))
      (fun k ↦ (x k.val, h k)) := by
  have hhidden (k : Fin (T + 1)) :
      ((Fin.lastCases (c, h (Fin.last T))
        (fun j : Fin T ↦ (x j.val, h j.castSucc)) :
        Fin (T + 1) → JointState (d * hdepth Q) (2 * (Q + 1))) k).2 = h k := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp
  have hzero : (0 : Fin (T + 1)) = (⟨0, hT⟩ : Fin T).castSucc := rfl
  simp only [finiteFixedPrefixWeight]
  congr 1
  · rw [hzero, Fin.lastCases_castSucc]
    rfl
  · apply Finset.prod_congr rfl
    intro k _
    simp only [Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_succ]
    rw [sparse_kernel_toReal hd t0 C ht0 hC code v false,
      sparse_kernel_toReal hd t0 C ht0 hC code v false]
    simp only [sparseStateWeight, hhidden]

/-- At the last recorded epoch the full observed law is the total hidden filter mass times the
behavior likelihood, with the final context summed out. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x),
[the action](hyp:a), and [the reward symbol](hyp:r), this establishes
[the sparse observed full mass equality filter result](goal). -/
-- @node: sparse_observed_full_mass_eq_filter
lemma sparse_observed_full_mass_eq_filter {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C) (hT : 0 < T)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2) :
    (sparseObservedPMF hd t0 zeta C code v false
      (fun k : Fin T ↦ (x k.val, a k.val, r k.val))).toReal =
      (d * hdepth Q : Nat) *
        ((∏ k : Fin T, (sparseBehaviorPMF zeta d Q (x k.val) (a k.val)).toReal) *
          ∑ h', sparseHiddenFilter hd t0 zeta C code v x a r T h') := by
  classical
  rw [show sparseObservedPMF (T := T) hd t0 zeta C code v false =
    (sparseFinite hd t0 zeta C code v false).obsPMF from rfl,
    finite_observed_mass_eq_prefix_weight_sum]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Eq.trans _ (congrArg (fun z : ℝ ↦ (d * hdepth Q : Nat) * z)
    (sparse_fixed_prefix_hidden_marginal_eq_filter hd t0 zeta C code v x a r ht0 hC T))
  rw [show ((d * hdepth Q : Nat) : ℝ) * (∑ h : Fin (T + 1) → Fin (2 * (Q + 1)),
      finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
        (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
        (sparseBehaviorPMF zeta d Q) (fun k : Fin T ↦ (a k.val, r k.val))
        (fun k ↦ (x k.val, h k))) =
      ∑ _c : Fin (d * hdepth Q), ∑ h : Fin (T + 1) → Fin (2 * (Q + 1)),
        finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
          (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
          (sparseBehaviorPMF zeta d Q) (fun k : Fin T ↦ (a k.val, r k.val))
          (fun k ↦ (x k.val, h k)) by simp]
  apply Finset.sum_congr rfl
  intro c _
  let f : (Fin T → Fin (2 * (Q + 1))) × Fin (2 * (Q + 1)) → ℝ := fun z ↦
    finiteFixedPrefixWeight (sparseKernel hd t0 C code v false)
      (fun s ↦ (sparseInit hd t0 zeta C code v false s).toReal)
      (sparseBehaviorPMF zeta d Q) (fun k : Fin T ↦ (a k.val, r k.val))
      (Fin.lastCases (c, z.2) (fun k ↦ (x k.val, z.1 k)))
  change (∑ h, ∑ u, f (h, u)) = _
  rw [← Fintype.sum_prod_type]
  symm
  apply Fintype.sum_equiv (finiteHiddenPrefixEquiv T (2 * (Q + 1)))
  intro h
  simpa [finiteHiddenPrefixEquiv, sparseFinite, f] using
    (sparse_prefix_weight_final_context_eq hd t0 zeta C ht0 hC hT code v x a r h c).symm

/-- The full observed likelihood relative to the common fair law is exactly the product of
filtered reward ratios in equation (16). The last context, which the observer never sees, has
been summed out. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the v0](hyp:v0),
[the observed state](hyp:x), [the action](hyp:a), and [the reward symbol](hyp:r), this
establishes [the sparse observed full likelihood product result](goal). -/
-- @node: sparse_observed_full_likelihood_product
lemma sparse_observed_full_likelihood_product {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hT : 0 < T)
    (code : Fin M → Fin d → Bool) (v v0 : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2) :
    (sparseObservedPMF hd t0 zeta C code v false
      (fun k : Fin T ↦ (x k.val, a k.val, r k.val))).toReal =
    (sparseObservedPMF hd t0 zeta C code v0 true
      (fun k : Fin T ↦ (x k.val, a k.val, r k.val))).toReal *
      ∏ k ∈ Finset.range T,
        (1 + (if r k = 0 then -1 else 1 : ℝ) *
          (sparseSignal t0 * sparseFilterBias hd zeta C code v x a k Q *
            ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r k
                (depthSignEquiv Q (Fin.last Q, u))) /
              (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r k h)))) := by
  have hprod := sparse_hidden_filter_total_likelihood_product (Q := Q)
    hd t0 zeta C code v x a r ht0 hzeta hC T
  dsimp only at hprod
  rw [sparse_observed_full_mass_eq_filter hd t0 zeta C ht0 hC hT code v,
    hprod,
    sparse_fair_observed_pmf_toReal hd t0 zeta C ht0 hzeta hC code v0]
  simp only [sparse_behavior_pmf_toReal zeta hzeta]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  have hfair : (∏ k : Fin T,
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (a k.val) * (1 / 2)) =
      (∏ k : Fin T, sparseBehaviorWeight zeta (a k.val)) *
        (((d * hdepth Q : Nat) : ℝ)⁻¹ / 2) ^ T := by
    simp_rw [show ∀ b : ℝ, ((d * hdepth Q : Nat) : ℝ)⁻¹ * b * (1 / 2) =
      b * (((d * hdepth Q : Nat) : ℝ)⁻¹ / 2) by intro b; ring]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hfair]
  have hc (A B D : ℝ) : ((d * hdepth Q : Nat) : ℝ) *
      (A * (((d * hdepth Q : Nat) : ℝ)⁻¹ * B * D)) = (A * B) * D := by
    calc
      _ = (((d * hdepth Q : Nat) : ℝ) * ((d * hdepth Q : Nat) : ℝ)⁻¹) *
        (A * B) * D := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn, one_mul]
  exact hc _ _ _

/-- Every full observed word has positive alternative mass, by the positive forward-filter mass
and the common positive behavior likelihood. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x),
[the action](hyp:a), and [the reward symbol](hyp:r), this establishes
[the sparse observed full probability mass function positivity result](goal). -/
-- @node: sparse_observed_full_pmf_pos
lemma sparse_observed_full_pmf_pos {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hT : 0 < T)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2) :
    0 < (sparseObservedPMF hd t0 zeta C code v false
      (fun k : Fin T ↦ (x k.val, a k.val, r k.val))).toReal := by
  rw [sparse_observed_full_mass_eq_filter hd t0 zeta C ht0 hC hT code v]
  apply mul_pos
  · exact_mod_cast (Nat.mul_pos hd (by simp [hdepth]))
  · apply mul_pos
    · apply Finset.prod_pos
      intro k _
      rw [sparse_behavior_pmf_toReal zeta hzeta]
      exact sparse_behavior_weight_pos zeta hzeta _
    · exact sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC T

/-- The actual full observed log likelihood is the sum of its conditional reward log
likelihoods. This is the pointwise identity needed before taking the alternative-law expectation
in equation (18). For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the v0](hyp:v0),
[the observed state](hyp:x), [the action](hyp:a), and [the reward symbol](hyp:r), this
establishes [the sparse observed full log likelihood ratio result](goal). -/
-- @node: sparse_observed_full_log_likelihood_ratio
lemma sparse_observed_full_log_likelihood_ratio {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hT : 0 < T)
    (code : Fin M → Fin d → Bool) (v v0 : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2) :
    Real.log ((sparseObservedPMF hd t0 zeta C code v false
      (fun k : Fin T ↦ (x k.val, a k.val, r k.val))).toReal /
      (sparseObservedPMF hd t0 zeta C code v0 true
        (fun k : Fin T ↦ (x k.val, a k.val, r k.val))).toReal) =
      ∑ k ∈ Finset.range T,
        Real.log (1 + (if r k = 0 then -1 else 1 : ℝ) *
          (sparseSignal t0 * sparseFilterBias hd zeta C code v x a k Q *
            ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r k
                (depthSignEquiv Q (Fin.last Q, u))) /
              (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r k h)))) := by
  rw [sparse_observed_full_likelihood_product hd t0 zeta C ht0 hzeta hC hT code v v0,
    mul_div_cancel_left₀ _ (ne_of_gt
      (sparse_fair_observed_pmf_pos hd t0 zeta C ht0 hzeta hC code v0 _))]
  apply Real.log_prod
  intro k _
  exact ne_of_gt (sparse_hidden_filter_reward_ratio_pos hd t0 zeta C code v x a r
    ht0 hzeta hC k)

end CausalSmith.Stat.PomdpPolicyclassRegret
