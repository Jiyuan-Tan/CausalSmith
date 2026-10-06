module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.RetentionWindowMoments
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FinitePathMarginal

/-! # Context-action product law of the actual sparse trajectory

Marginalizing the reward and hidden transition leaves a fresh uniform context.
Chronological finite sums transfer the retention moments to the generated law.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- Summing hidden coordinates at a fixed new context leaves its uniform mass. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the codeword index](hyp:v), [the fair-reference flag](hyp:fair), [the state](hyp:s),
[the action](hyp:a), and [the observed state](hyp:x), this establishes
[the sparse state weight context marginal result](goal). -/
-- @node: sparse_state_weight_context_marginal
lemma sparse_state_weight_context_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x : Fin (d * hdepth Q)) :
    (∑ h, sparseStateWeight hd t0 C code v fair s (x, h) a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  have hx (y : Fin (d * hdepth Q)) (h : Fin (2 * (Q + 1))) :
      sparseStateWeight hd t0 C code v fair s (y, h) a =
        sparseStateWeight hd t0 C code v fair s (x, h) a := rfl
  have hsum := sparse_state_weight_sum hd t0 C code v fair s a
  rw [Fintype.sum_prod_type] at hsum
  simp_rw [hx] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  rw [← one_div]
  apply (eq_div_iff hn).mpr
  simpa only [one_div, mul_comm] using hsum

/-- Rewards and hidden transitions marginalized together give a fresh context, independent of
the previous joint state and chosen action. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the fair-reference flag](hyp:fair), [the state](hyp:s),
[the action](hyp:a), and [the observed state](hyp:x), this establishes
[the sparse kernel context marginal result](goal). -/
-- @node: sparse_kernel_context_marginal
lemma sparse_kernel_context_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x : Fin (d * hdepth Q)) :
    (∑ h, ∑ r : Fin 2, (sparseKernel hd t0 C code v fair s a (r, (x, h))).toReal) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  simp_rw [sparse_kernel_state_marginal hd t0 C ht0 hC code v fair]
  exact sparse_state_weight_context_marginal hd t0 C code v fair s a x

/-- The actual stationary initial PMF has a uniform observed context. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed state](hyp:x), this establishes
[the sparse init context marginal result](goal). -/
-- @node: sparse_init_context_marginal
lemma sparse_init_context_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) :
    (∑ h, (sparseInit hd t0 zeta C code v false (x, h)).toReal) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  simp_rw [sparse_init_toReal hd t0 zeta C ht0 hzeta hC code v false,
    sparse_transition_weight_eq hd t0 zeta C ht0 hzeta hC code v false,
    sparse_behavior_weight_stationary_density hd t0 zeta C ht0 hzeta hC code v]
  exact sparse_signed_density_context_mass d Q t0 C _ ht0 x

/-- Fresh contexts at each transition give independent context-action product expectations under
any initial weight with the same context marginal. Real weights permit chronological induction
through weighted prefixes. For [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the reward-symbol count](hyp:nR), [the kernel](hyp:kernel),
[the behavior policy](hyp:b), [the ν](hyp:ν), [the ν assumption](hyp:hν),
[the kernel assumption](hyp:hkernel), the time horizon, the policy,
the mass, the policy assumption, and the f, this establishes
[the finite path context action product result](goal). -/
-- @node: finitePath_context_action_product
lemma finitePath_context_action_product {nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) (ν : Fin nX → ℝ) (hν : ∑ x, ν x = 1)
    (hkernel : ∀ s a x, (∑ h, ∑ r : Fin nR, (kernel s a (r, (x, h))).toReal) = ν x) :
    ∀ (T : Nat) (p : JointState nX nH → ℝ) (mass : ℝ)
      (hp : ∀ x, (∑ h, p (x, h)) = mass * ν x)
      (f : Fin T → Fin nX → Bool → ℝ),
      (∑ tau : FiniteTrajectory T nX nH nR,
        finitePathWeightFrom kernel p b tau *
          ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1) =
        mass * ∏ t, ∑ x, ∑ a, ν x * (b x a).toReal * f t x a := by
  classical
  intro T
  induction T with
  | zero =>
      intro p mass hp f
      rw [Fintype.sum_equiv (finiteTrajectoryZeroEquiv nX nH nR)
        (fun tau ↦ finitePathWeightFrom kernel p b tau *
          ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1) p
        (fun tau ↦ by simp [finitePathWeightFrom, finiteTrajectoryZeroEquiv])]
      simp only [Fintype.sum_prod_type, hp, ← Finset.mul_sum, hν,
        Fin.prod_univ_zero, mul_one]
  | succ T ih =>
      intro p mass hp f
      let massNext := ∑ s : JointState nX nH, ∑ a : Bool,
        p s * (b s.1 a).toReal * f 0 s.1 a
      let pNext : JointState nX nH → ℝ := fun s' ↦
        ∑ s : JointState nX nH, ∑ a : Bool,
          p s * (b s.1 a).toReal * f 0 s.1 a *
            ∑ r : Fin nR, (kernel s a (r, s')).toReal
      have hpNext (x : Fin nX) : (∑ h, pNext (x, h)) = massNext * ν x := by
        dsimp [pNext, massNext]
        rw [Finset.sum_mul, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_mul, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, hkernel]
      have hmassNext : massNext = mass * ∑ x, ∑ a, ν x * (b x a).toReal * f 0 x a := by
        dsimp [massNext]
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.sum_comm (f := fun h a ↦ p (_, h) * (b _ a).toReal * f 0 _ a)]
        simp_rw [← Finset.sum_mul, hp]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro a _
        ring
      have hpeel :
          (∑ tau : FiniteTrajectory (T + 1) nX nH nR,
            finitePathWeightFrom kernel p b tau *
              ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1) =
          ∑ tau : FiniteTrajectory T nX nH nR,
            finitePathWeightFrom kernel pNext b tau *
              ∏ t, f t.succ (tau.1 t.castSucc).1 (tau.2 t).1 := by
        rw [Fintype.sum_equiv (finiteTrajectorySuccEquiv T nX nH nR)
          _ (fun z ↦ finitePathWeightFrom kernel p b
            ((finiteTrajectorySuccEquiv T nX nH nR).symm z) *
              ∏ t, f t (((finiteTrajectorySuccEquiv T nX nH nR).symm z).1 t.castSucc).1
                (((finiteTrajectorySuccEquiv T nX nH nR).symm z).2 t).1)
          (fun tau ↦ by rw [Equiv.symm_apply_apply])]
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro tau _
        simp_rw [finitePathWeightFrom_succEquiv_symm, Fin.prod_univ_succ]
        simp only [finiteTrajectorySuccEquiv, Equiv.coe_fn_symm_mk, Fin.cases_zero,
          Fin.castSucc_zero, Fin.castSucc_succ, Fin.cases_succ]
        rw [finitePathWeightFrom]
        dsimp only [pNext]
        simp_rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
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

/-- The actual sparse generated path has independent context-action product expectations,
including its stationary initial coordinate. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the f](hyp:f), this establishes
[the sparse path context action product result](goal). -/
-- @node: sparse_path_context_action_product
lemma sparse_path_context_action_product {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (f : Fin T → Fin (d * hdepth Q) → Bool → ℝ) :
    (∑ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
      ((sparseFinite hd t0 zeta C code v false).law tau).toReal *
        ∏ t, f t (tau.1 t.castSucc).1 (tau.2 t).1) =
      ∏ t, ∑ x, ∑ a,
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta a * f t x a := by
  let K := sparseKernel (Q := Q) hd t0 C code v false
  let b := sparseBehaviorPMF zeta d Q
  let p := fun s ↦ (sparseInit (Q := Q) hd t0 zeta C code v false s).toReal
  have hlaw (tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2) :
      ((sparseFinite hd t0 zeta C code v false).law tau).toReal =
        finitePathWeightFrom K p b tau := by
    rw [(sparseFinite hd t0 zeta C code v false).law_generated,
      ENNReal.toReal_mul, ENNReal.toReal_prod]
    simp only [ENNReal.toReal_mul]
    rfl
  simp_rw [hlaw]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  have hmass : (∑ _x : Fin (d * hdepth Q), ((d * hdepth Q : Nat) : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn
  rw [finitePath_context_action_product K b _ hmass
    (sparse_kernel_context_marginal hd t0 C ht0 hC code v false)
    T p 1 (by intro x; simpa [p] using
      sparse_init_context_marginal hd t0 zeta C ht0 hzeta hC code v x) f, one_mul]
  simp only [b, sparse_behavior_pmf_toReal zeta hzeta]

/-- A finite observed PMF expectation is the expectation of its projection under the full finite
trajectory PMF. For [the time horizon](hyp:T), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the reward-symbol count](hyp:nR), [the event family](hyp:F),
and [the g](hyp:g), this establishes [the finite reward model observed sum result](goal). -/
-- @node: finiteRewardModel_observed_sum
lemma finiteRewardModel_observed_sum {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (g : FiniteObsView T nX nR → ℝ) :
    (∑ w, (F.obsPMF w).toReal * g w) =
      ∑ tau, (F.law tau).toReal * g (finObsProj tau) := by
  have hmap := integral_map (μ := F.law.toMeasure)
    (measurable_of_finite finObsProj).aemeasurable
    (show AEStronglyMeasurable g (F.law.toMeasure.map finObsProj) by fun_prop)
  rw [PMF.toMeasure_map finObsProj F.law (measurable_of_finite _)] at hmap
  simpa only [PMF.integral_eq_sum, smul_eq_mul, Function.comp_def,
    FiniteRewardModel.obsPMF] using hmap

/-- The alternative's actual observed context-action word has product expectations; rewards and
hidden coordinates have been marginalized. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the f](hyp:f), this establishes
[the sparse observed context action product result](goal). -/
-- @node: sparse_observed_context_action_product
lemma sparse_observed_context_action_product {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (f : Fin T → Fin (d * hdepth Q) → Bool → ℝ) :
    (∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        ∏ t, f t (w t).1 (w t).2.1) =
      ∏ t, ∑ x, ∑ a,
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta a * f t x a := by
  rw [show sparseObservedPMF hd t0 zeta C code v false =
      (sparseFinite hd t0 zeta C code v false).obsPMF from rfl]
  rw [finiteRewardModel_observed_sum]
  exact sparse_path_context_action_product hd t0 zeta C ht0 hzeta hC code v f

/-- The exact squared retention-window moment under the actual alternative law. The stationary
prefix contributes its missing retention factors, while the recorded context-action window is
independent under the generated law. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the epoch index](hyp:t), this establishes
[the sparse observed retention second moment result](goal). -/
-- @node: sparse_observed_retention_second_moment
lemma sparse_observed_retention_second_moment {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T) :
    (∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        retentionFactor hd zeta code v t w ^ 2) =
      sparseRetentionProbability Q zeta ^ (2 * Q - min Q t.val) := by
  classical
  let s := (Finset.univ : Finset (Fin T)).filter
    (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val)
  let f := fun (r : Fin T) (x : Fin (d * hdepth Q)) (a : Bool) ↦
    if r ∈ s then retentionIndicator hd code v x a ^ 2 else 1
  have hfactor (w : FiniteObsView T (d * hdepth Q) 2) :
      retentionFactor hd zeta code v t w ^ 2 =
        (sparseRetentionProbability Q zeta ^ (Q - min Q t.val)) ^ 2 *
          ∏ r, f r (w r).1 (w r).2.1 := by
    rw [retentionFactor_eq_fin_window hd zeta code v, mul_pow, ← Finset.prod_pow]
    congr 1
    simp only [f, s, Finset.prod_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  have hf (r : Fin T) :
      (∑ x, ∑ a, ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        sparseBehaviorWeight zeta a * f r x a) =
        if r ∈ s then sparseRetentionProbability Q zeta else 1 := by
    by_cases hr : r ∈ s
    · simp only [f, hr, if_true]
      simpa only [Fintype.sum_prod_type] using sparse_retention_second_moment hd zeta code v
    · simp only [f, hr, if_false, mul_one]
      simpa only [Fintype.sum_prod_type] using sparse_context_action_weight_sum d Q hd zeta
  simp_rw [hfactor]
  calc
    _ = (sparseRetentionProbability Q zeta ^ (Q - min Q t.val)) ^ 2 *
        ∑ w : FiniteObsView T (d * hdepth Q) 2,
          (sparseObservedPMF hd t0 zeta C code v false w).toReal *
            ∏ r, f r (w r).1 (w r).2.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = (sparseRetentionProbability Q zeta ^ (Q - min Q t.val)) ^ 2 *
        ∏ r, if r ∈ s then sparseRetentionProbability Q zeta else 1 := by
      rw [sparse_observed_context_action_product hd t0 zeta C ht0 hzeta hC code v f]
      simp_rw [hf]
    _ = (sparseRetentionProbability Q zeta ^ (Q - min Q t.val)) ^ 2 *
        sparseRetentionProbability Q zeta ^ (min Q t.val) := by
      congr 1
      rw [← Finset.prod_filter]
      have hc : s.card = min Q t.val := retention_window_card Q t
      simpa using congrArg (fun n ↦ sparseRetentionProbability Q zeta ^ n) hc
    _ = sparseRetentionProbability Q zeta ^ (2 * Q - min Q t.val) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- Every stationary-prefix or full-depth window has actual alternative second moment at most
the full-depth behavior retention probability. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the epoch index](hyp:t), this establishes
[the sparse observed retention second moment bound result](goal). -/
-- @node: sparse_observed_retention_second_moment_le
lemma sparse_observed_retention_second_moment_le {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T) :
    (∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        retentionFactor hd zeta code v t w ^ 2) ≤
      sparseRetentionProbability Q zeta ^ Q := by
  rw [sparse_observed_retention_second_moment hd t0 zeta C ht0 hzeta hC code v t]
  obtain ⟨hp0, hp1⟩ := sparseRetentionProbability_mem_unitInterval Q zeta hzeta
  exact pow_le_pow_of_le_one hp0 hp1 (by omega)

end CausalSmith.Stat.PomdpPolicyclassRegret
