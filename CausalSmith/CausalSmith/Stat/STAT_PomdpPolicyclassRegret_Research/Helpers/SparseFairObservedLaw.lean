module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.ObservedKLChain
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseContextActionLaw

/-! # Fair observed reference law

The fair experiment has independent uniform contexts, behavior actions and
fair reward symbols, including its stationary initial window. These facts
supply the reference support required by the observed KL chain rule.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- Fresh contexts and independent rewards give context-action-reward product expectations under
any initial weight with the same context marginal. Real weights permit chronological induction
through weighted prefixes. For [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the reward-symbol count](hyp:nR), [the kernel](hyp:kernel),
[the behavior policy](hyp:b), [the ν](hyp:ν), [the kernel](hyp:κ), [the ν assumption](hyp:hν),
[the kernel assumption](hyp:hkernel), the time horizon, the policy,
the mass, the policy assumption, and the f, this establishes
[the finite path context action reward product result](goal). -/
-- @node: finitePath_context_action_reward_product
lemma finitePath_context_action_reward_product {nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) (ν : Fin nX → ℝ) (κ : Fin nR → ℝ) (hν : ∑ x, ν x = 1)
    (hkernel : ∀ s a r x, (∑ h, (kernel s a (r, (x, h))).toReal) = κ r * ν x) :
    ∀ (T : Nat) (p : JointState nX nH → ℝ) (mass : ℝ)
      (_hp : ∀ x, (∑ h, p (x, h)) = mass * ν x)
      (f : Fin T → Fin nX → Bool → Fin nR → ℝ),
      (∑ tau : FiniteTrajectory T nX nH nR,
        finitePathWeightFrom kernel p b tau *
          ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1 (tau.2 t).2) =
        mass * ∏ t, ∑ x, ∑ a, ∑ r, ν x * (b x a).toReal * κ r * f t x a r := by
  classical
  intro T
  induction T with
  | zero =>
      intro p mass hp f
      rw [Fintype.sum_equiv (finiteTrajectoryZeroEquiv nX nH nR)
        (fun tau ↦ finitePathWeightFrom kernel p b tau *
          ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1 (tau.2 t).2) p
        (fun tau ↦ by simp [finitePathWeightFrom, finiteTrajectoryZeroEquiv])]
      simp only [Fintype.sum_prod_type, hp, ← Finset.mul_sum, hν,
        Fin.prod_univ_zero, mul_one]
  | succ T ih =>
      intro p mass hp f
      let massNext := ∑ s : JointState nX nH, ∑ a : Bool,
        ∑ r : Fin nR, p s * (b s.1 a).toReal * κ r * f 0 s.1 a r
      let pNext : JointState nX nH → ℝ := fun s' ↦
        ∑ s : JointState nX nH, ∑ a : Bool,
          ∑ r : Fin nR, p s * (b s.1 a).toReal * f 0 s.1 a r *
            (kernel s a (r, s')).toReal
      have hpNext (x : Fin nX) : (∑ h, pNext (x, h)) = massNext * ν x := by
        dsimp [pNext, massNext]
        rw [Finset.sum_mul, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_mul, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.mul_sum, hkernel]
        ring
      have hmassNext : massNext = mass * ∑ x, ∑ a, ∑ r, ν x * (b x a).toReal * κ r * f 0 x a r := by
        dsimp [massNext]
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.sum_comm (f := fun h a ↦ ∑ r : Fin nR, p (_, h) * (b _ a).toReal * κ r * f 0 _ a r)]
        simp_rw [Finset.sum_comm (f := fun h r ↦ p (_, h) * (b _ _).toReal * κ r * f 0 _ _ r)]
        simp_rw [← Finset.sum_mul, hp]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro r _
        ring
      have hpeel :
          (∑ tau : FiniteTrajectory (T + 1) nX nH nR,
            finitePathWeightFrom kernel p b tau *
              ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1 (tau.2 t).2) =
          ∑ tau : FiniteTrajectory T nX nH nR,
            finitePathWeightFrom kernel pNext b tau *
              ∏ t, f t.succ (tau.1 t.castSucc).1 (tau.2 t).1 (tau.2 t).2 := by
        rw [Fintype.sum_equiv (finiteTrajectorySuccEquiv T nX nH nR)
          _ (fun z ↦ finitePathWeightFrom kernel p b
            ((finiteTrajectorySuccEquiv T nX nH nR).symm z) *
              ∏ t, f t (((finiteTrajectorySuccEquiv T nX nH nR).symm z).1 t.castSucc).1
                (((finiteTrajectorySuccEquiv T nX nH nR).symm z).2 t).1
                (((finiteTrajectorySuccEquiv T nX nH nR).symm z).2 t).2)
          (fun tau ↦ by rw [Equiv.symm_apply_apply])]
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro tau _
        simp_rw [finitePathWeightFrom_succEquiv_symm, Fin.prod_univ_succ]
        simp only [finiteTrajectorySuccEquiv, Equiv.coe_fn_symm_mk, Fin.cases_zero,
          Fin.castSucc_zero, Fin.castSucc_succ, Fin.cases_succ]
        rw [finitePathWeightFrom]
        dsimp only [pNext]
        simp only [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hpeel, ih pNext massNext hpNext, hmassNext, Fin.prod_univ_succ]
      ring


/-- The reference kernel produces a fair reward independently of its fresh uniform context,
after summing out the unobserved successor sign and depth. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the state](hyp:s),
[the action](hyp:a), [the reward symbol](hyp:r), and [the observed state](hyp:x), this
establishes [the sparse fair kernel reward context marginal result](goal). -/
-- @node: sparse_fair_kernel_reward_context_marginal
lemma sparse_fair_kernel_reward_context_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (r : Fin 2) (x : Fin (d * hdepth Q)) :
    (∑ h, (sparseKernel hd t0 C code v true s a (r, (x, h))).toReal) =
      (1 / 2 : ℝ) * ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  simp_rw [sparse_kernel_toReal hd t0 C ht0 hC code v true]
  simp only [if_true, ← Finset.mul_sum]
  rw [sparse_state_weight_context_marginal]

/-- Stationarity and the fresh-context marginal make the reference initial context uniform as
well; no explicit formula for its hidden density is needed. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed state](hyp:x), this establishes
[the sparse fair init context marginal result](goal). -/
-- @node: sparse_fair_init_context_marginal
lemma sparse_fair_init_context_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) :
    (∑ h, (sparseInit hd t0 zeta C code v true (x, h)).toReal) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  let π := stationaryLaw (sparseTransition (Q := Q) hd t0 zeta C code v true)
  have hs := sparse_transition_stationary (Q := Q) hd t0 zeta C ht0 hzeta hC code v true
  simp_rw [sparse_init_toReal hd t0 zeta C ht0 hzeta hC code v true]
  change (∑ h, π (x, h)) = _
  calc
    _ = ∑ h, ∑ s, π s * sparseTransition hd t0 zeta C code v true s (x, h) := by
      apply Finset.sum_congr rfl
      intro h _
      exact (hs.2 (x, h)).symm
    _ = ∑ s, π s * ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      simp_rw [sparse_transition_weight_eq hd t0 zeta C ht0 hzeta hC code v true]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sparse_state_weight_context_marginal]
      rw [← Finset.sum_mul]
      simp [sparseBehaviorWeight]
    _ = _ := by rw [← Finset.sum_mul, hs.1.2, one_mul]

/-- The actual fair reference path has independent context-action-reward product expectations,
including its stationary initial coordinate. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the f](hyp:f), this establishes
[the sparse fair path context action reward product result](goal). -/
-- @node: sparse_fair_path_context_action_reward_product
lemma sparse_fair_path_context_action_reward_product {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (f : Fin T → Fin (d * hdepth Q) → Bool → Fin 2 → ℝ) :
    (∑ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
      ((sparseFinite hd t0 zeta C code v true).law tau).toReal *
        ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1 (tau.2 t).2) =
      ∏ t, ∑ x, ∑ a, ∑ r : Fin 2,
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta a * (1 / 2) * f t x a r := by
  let K := sparseKernel (Q := Q) hd t0 C code v true
  let b := sparseBehaviorPMF zeta d Q
  let p := fun s ↦ (sparseInit (Q := Q) hd t0 zeta C code v true s).toReal
  have hlaw (tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2) :
      ((sparseFinite hd t0 zeta C code v true).law tau).toReal =
        finitePathWeightFrom K p b tau := by
    rw [(sparseFinite hd t0 zeta C code v true).law_generated,
      ENNReal.toReal_mul, ENNReal.toReal_prod]
    simp only [ENNReal.toReal_mul]
    rfl
  simp_rw [hlaw]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  have hmass : (∑ _x : Fin (d * hdepth Q), ((d * hdepth Q : Nat) : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn
  rw [finitePath_context_action_reward_product K b _ (fun _ ↦ 1 / 2) hmass
    (sparse_fair_kernel_reward_context_marginal hd t0 C ht0 hC code v)
    T p 1 (by intro x; simpa [p] using
      sparse_fair_init_context_marginal hd t0 zeta C ht0 hzeta hC code v x) f, one_mul]
  simp only [b, sparse_behavior_pmf_toReal zeta hzeta]

/-- All observed coordinates of the fair reference have their common product expectation, with
the latent trajectory marginalized out. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the f](hyp:f), this establishes
[the sparse fair observed product result](goal). -/
-- @node: sparse_fair_observed_product
lemma sparse_fair_observed_product {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (f : Fin T → Fin (d * hdepth Q) → Bool → Fin 2 → ℝ) :
    (∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v true w).toReal *
        ∏ t, f t (w t).1 (w t).2.1 (w t).2.2) =
      ∏ t, ∑ x, ∑ a, ∑ r : Fin 2,
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta a * (1 / 2) * f t x a r := by
  rw [show sparseObservedPMF hd t0 zeta C code v true =
      (sparseFinite hd t0 zeta C code v true).obsPMF from rfl,
    finiteRewardModel_observed_sum]
  exact sparse_fair_path_context_action_reward_product hd t0 zeta C ht0 hzeta hC code v f

/-- The exact mass of each fair observed word factors into uniform contexts, behavior actions
and fair rewards. It includes every stationary initial window. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed word](hyp:w), this establishes
[the sparse fair observed probability mass function to real result](goal). -/
-- @node: sparse_fair_observed_pmf_toReal
lemma sparse_fair_observed_pmf_toReal {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    (sparseObservedPMF hd t0 zeta C code v true w).toReal =
      ∏ t, ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (w t).2.1 * (1 / 2) := by
  classical
  let f := fun (t : Fin T) (x : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2) ↦
    if (x, a, r) = w t then (1 : ℝ) else 0
  have hprod (u : FiniteObsView T (d * hdepth Q) 2) :
      (∏ t, f t (u t).1 (u t).2.1 (u t).2.2) = if u = w then 1 else 0 := by
    simp only [f, Prod.mk.eta, Finset.prod_ite_zero]
    simp [funext_iff]
  have h := sparse_fair_observed_product hd t0 zeta C ht0 hzeta hC code v f
  simp_rw [hprod] at h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro t _
  simp only [f, Prod.ext_iff, mul_ite, mul_one, mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The fair reference probability of each recorded prefix is the product of its observed
one-epoch masses, including incomplete stationary windows. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the history length](hyp:k), and [the observed word](hyp:w), this
establishes [the sparse fair observed prefix mass result](goal). -/
-- @node: sparse_fair_observed_prefix_mass
lemma sparse_fair_observed_prefix_mass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (k : Nat)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    observedWordPrefixMass (sparseObservedPMF hd t0 zeta C code v true) k w =
      ∏ t ∈ (Finset.univ : Finset (Fin T)).filter (fun t ↦ t.val < k),
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (w t).2.1 * (1 / 2) := by
  classical
  let f := fun (t : Fin T) (x : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2) ↦
    if t.val < k then (if (x, a, r) = w t then (1 : ℝ) else 0) else 1
  have hprod (u : FiniteObsView T (d * hdepth Q) 2) :
      (∏ t, f t (u t).1 (u t).2.1 (u t).2.2) =
        if (∀ t : Fin T, t.val < k → u t = w t) then 1 else 0 := by
    simp only [f, Prod.mk.eta, ← Finset.prod_filter, Finset.prod_ite_zero]
    simp
  have h := sparse_fair_observed_product hd t0 zeta C ht0 hzeta hC code v f
  simp_rw [hprod] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  change observedWordPrefixMass _ k w = _ at h
  rw [h, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro t _
  by_cases ht : t.val < k
  · simp only [f, ht, if_true, Prod.ext_iff, mul_ite, mul_one, mul_zero, ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  · simp only [f, ht, if_false, mul_one]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hd (show 0 < hdepth Q by simp [hdepth]))
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    have hh' : (hdepth Q : ℝ) ≠ 0 := by
      exact_mod_cast (show hdepth Q ≠ 0 by simp [hdepth])
    simp [sparseBehaviorWeight]
    field_simp
    ring

/-- Every behavior action has positive probability in the sparse experiment. For
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta), and
[the action](hyp:a), this establishes [the sparse behavior weight positivity result](goal). -/
-- @node: sparse_behavior_weight_pos
lemma sparse_behavior_weight_pos (zeta : ℝ) (hzeta : 0 < zeta) (a : Bool) :
    0 < sparseBehaviorWeight zeta a := by
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hp : 0 < (policyFactor zeta)⁻¹ := inv_pos.mpr (by linarith)
  have hp1 : (policyFactor zeta)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hL
  cases a <;> simp only [sparseBehaviorWeight, Bool.false_eq_true, if_false, if_true]
  · linarith
  · exact hp

/-- Every observed word has positive reference mass. No reset indicator or latent coordinate is
exposed in this support statement. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed word](hyp:w), this establishes
[the sparse fair observed probability mass function positivity result](goal). -/
-- @node: sparse_fair_observed_pmf_pos
lemma sparse_fair_observed_pmf_pos {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    0 < (sparseObservedPMF hd t0 zeta C code v true w).toReal := by
  rw [sparse_fair_observed_pmf_toReal hd t0 zeta C ht0 hzeta hC code v w]
  apply Finset.prod_pos
  intro t _
  have hn : (0 : ℝ) < (d * hdepth Q : Nat) := by
    exact_mod_cast Nat.mul_pos hd (show 0 < hdepth Q by simp [hdepth])
  exact mul_pos (mul_pos (inv_pos.mpr hn) (sparse_behavior_weight_pos zeta hzeta _))
    (by norm_num)

/-- The fair observed reference has the common one-step context-action mass times one half at
every positive prefix. This is the denominator in (16). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the sparse fair observed prefix ratio result](goal). -/
-- @node: sparse_fair_observed_prefix_ratio
lemma sparse_fair_observed_prefix_ratio {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    observedWordPrefixMass (sparseObservedPMF hd t0 zeta C code v true) (t.val + 1) w /
      observedWordPrefixMass (sparseObservedPMF hd t0 zeta C code v true) t.val w =
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (w t).2.1 * (1 / 2) := by
  classical
  have hpos : 0 < observedWordPrefixMass
      (sparseObservedPMF hd t0 zeta C code v true) t.val w :=
    lt_of_lt_of_le (sparse_fair_observed_pmf_pos hd t0 zeta C ht0 hzeta hC code v w)
      (observedWordPrefixMass_ge_word _ _ w)
  apply (div_eq_iff (ne_of_gt hpos)).mpr
  simp_rw [sparse_fair_observed_prefix_mass hd t0 zeta C ht0 hzeta hC code v]
  have hsets : (Finset.univ : Finset (Fin T)).filter (fun r ↦ r.val < t.val + 1) =
      insert t ((Finset.univ : Finset (Fin T)).filter (fun r ↦ r.val < t.val)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hr
      by_cases heq : r = t
      · exact Or.inl heq
      · exact Or.inr (by have hne : r.val ≠ t.val := fun h ↦ heq (Fin.ext h); omega)
    · rintro (rfl | hr) <;> omega
  rw [hsets, Finset.prod_insert]
  simp

/-- The finite observed divergence from the fair reference is finite for all sparse
alternatives, by the reference's full observed support. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the v0](hyp:v0), this establishes
[the sparse observed KL div ne top result](goal). -/
-- @node: sparse_observed_klDiv_ne_top
lemma sparse_observed_klDiv_ne_top {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v v0 : Fin M) :
    klDiv (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false).toMeasure
      (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v0 true).toMeasure ≠ ⊤ := by
  apply finitePMF_klDiv_ne_top
  intro w hw
  have hp := sparse_fair_observed_pmf_pos (T := T) (Q := Q) hd t0 zeta C
    ht0 hzeta hC code v0 w
  simp [hw] at hp

/-- The actual observed KL chain rule requires no separate support premise: the common fair
reference assigns positive mass to every observed word. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse observed KL div bound chain of parameters result](goal). -/
-- @node: sparse_observed_klDiv_le_chain_of_parameters
lemma sparse_observed_klDiv_le_chain_of_parameters (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    (klDiv
      (obsLaw (sparsePackingExperiment T M d Q hd hDim hM
        t0 zeta C code hCode v).Mx.toRawB)
      (sparseReferenceLaw T M d Q hd (by omega) t0 zeta C code)).toReal ≤
      ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false w).toReal *
          Real.log ((observedWordPrefixMass
            (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false) (t.val + 1) w /
            observedWordPrefixMass
              (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false) t.val w) /
            (observedWordPrefixMass
              (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true) (t.val + 1) w /
              observedWordPrefixMass
                (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true) t.val w)) := by
  apply sparse_observed_klDiv_le_chain T M d Q hd hDim hM t0 zeta C code hCode v
  intro w hw
  have hp := sparse_fair_observed_pmf_pos (T := T) (Q := Q) hd t0 zeta C
    ht0 hzeta hC code ⟨0, by omega⟩ w
  simp [hw] at hp

end CausalSmith.Stat.PomdpPolicyclassRegret
