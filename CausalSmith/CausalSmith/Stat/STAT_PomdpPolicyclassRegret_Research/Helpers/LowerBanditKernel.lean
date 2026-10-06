module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditInformation
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteEncoding

/-! # Common kernel of the fully observed bandit lower experiment

The kernel emits a Bernoulli reward with the equation (41) mean and independently
redraws a uniform context. The hidden alphabet is a singleton. Consequently every
probability policy induces the same constant-row transition, with identical
stationary laws and zero total-variation contraction.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Action weights of a target codeword, including both binary actions. -/
-- @node: lowerBanditPolicyWeight
noncomputable def lowerBanditPolicyWeight {d : Nat} (eta : ℝ)
    (word : Fin d → Bool) (x : Fin d) (a : Bool) : ℝ :=
  if a then lowerBanditActionProb eta (word x) else
    1 - lowerBanditActionProb eta (word x)

/-- The equation (40) target is a probability policy. For [the code dimension](hyp:d),
[the signal parameter](hyp:eta), [the eta0 assumption](hyp:heta0),
[the eta1 assumption](hyp:heta1), and [the word](hyp:word), this establishes
[the lower bandit policy vector result](goal). -/
-- @node: lower_bandit_policy_vector
lemma lower_bandit_policy_vector {d : Nat} (eta : ℝ) (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1) (word : Fin d → Bool) :
    PolicyVector (lowerBanditPolicyWeight eta word) := by
  intro x
  have hp := lower_bandit_action_prob_unit eta heta0 heta1 (word x)
  constructor
  · intro a; cases a <;> simp [lowerBanditPolicyWeight] <;> linarith [hp.1, hp.2]
  · simp [lowerBanditPolicyWeight]

/-- Reward-symbol probability for the common bandit kernel. -/
-- @node: lowerBanditRewardWeight
noncomputable def lowerBanditRewardWeight (gamma : ℝ) (bit a : Bool) (r : Fin 2) : ℝ :=
  if r = 0 then 1 - lowerBanditRewardMean gamma bit a else
    lowerBanditRewardMean gamma bit a

/-- The two reward-symbol weights sum to one. For [the rate parameter](hyp:gamma),
[the bit](hyp:bit), and [the action](hyp:a), this establishes
[the lower bandit reward weight sum result](goal). -/
-- @node: lower_bandit_reward_weight_sum
lemma lower_bandit_reward_weight_sum (gamma : ℝ) (bit a : Bool) :
    ∑ r : Fin 2, lowerBanditRewardWeight gamma bit a r = 1 := by
  simp [Fin.sum_univ_two, lowerBanditRewardWeight]

/-- The small amplitude makes the kernel's reward weights nonnegative. For
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1),
[the bit](hyp:bit), [the action](hyp:a), and [the reward symbol](hyp:r), this establishes
[the lower bandit reward weight nonnegativity result](goal). -/
-- @node: lower_bandit_reward_weight_nonneg
lemma lower_bandit_reward_weight_nonneg (gamma : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (bit a : Bool) (r : Fin 2) :
    0 ≤ lowerBanditRewardWeight gamma bit a r := by
  have h := lower_bandit_reward_prob_unit gamma hg0 hg1 bit a
  change lowerBanditRewardMean gamma bit a ∈ Set.Icc (0 : ℝ) 1 at h
  unfold lowerBanditRewardWeight
  split_ifs <;> linarith [h.1, h.2]

/-- The uniform state vector includes the singleton hidden coordinate. -/
-- @node: lowerBanditStateWeight
noncomputable def lowerBanditStateWeight (d : Nat) (_s : JointState d 1) : ℝ :=
  (d : ℝ)⁻¹

/-- The uniform joint-state vector is a probability vector. For [the code dimension](hyp:d) and
[the code dimension assumption](hyp:hd), this establishes
[the lower bandit state probability result](goal). -/
-- @node: lower_bandit_state_probability
lemma lower_bandit_state_probability {d : Nat} (hd : 0 < d) :
    ProbabilityVector (lowerBanditStateWeight d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  constructor
  · intro s; exact inv_nonneg.mpr (Nat.cast_nonneg d)
  · simp [lowerBanditStateWeight, hd0]

/-- One kernel per environment, shared by the whole target list. -/
-- @node: lowerBanditKernel
noncomputable def lowerBanditKernel {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (s : JointState d 1) (a : Bool) :
    PMF (Fin 2 × JointState d 1) := by
  letI : NeZero d := ⟨hd.ne'⟩
  exact pmfOfRealWeight (fun q ↦ lowerBanditRewardWeight gamma (word s.1) a q.1 *
    lowerBanditStateWeight d q.2)

/-- Kernel normalization leaves the independent reward and state weights intact. For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1),
[the state](hyp:s), [the action](hyp:a), and [the q](hyp:q), this establishes
[the lower bandit kernel to real result](goal). -/
-- @node: lower_bandit_kernel_toReal
lemma lower_bandit_kernel_toReal {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (s : JointState d 1) (a : Bool) (q : Fin 2 × JointState d 1) :
    (lowerBanditKernel hd word gamma s a q).toReal =
      lowerBanditRewardWeight gamma (word s.1) a q.1 * lowerBanditStateWeight d q.2 := by
  let : NeZero d := ⟨hd.ne'⟩
  have hn : ∀ q : Fin 2 × JointState d 1,
      0 ≤ lowerBanditRewardWeight gamma (word s.1) a q.1 *
        lowerBanditStateWeight d q.2 := fun q ↦ mul_nonneg
    (lower_bandit_reward_weight_nonneg gamma hg0 hg1 _ _ _)
    ((lower_bandit_state_probability hd).1 _)
  have hs : ∑ q : Fin 2 × JointState d 1,
      lowerBanditRewardWeight gamma (word s.1) a q.1 *
        lowerBanditStateWeight d q.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (lower_bandit_state_probability hd).2, mul_one]
    exact lower_bandit_reward_weight_sum _ _ _
  change (pmfOfRealWeight _ q).toReal = _
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hn hs q, ENNReal.toReal_ofReal (hn q)]

/-- Marginalizing the reward gives a uniform next state, independently of action. For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1),
[the state](hyp:s), [the successor state](hyp:s'), and [the action](hyp:a), this establishes
[the lower bandit kernel state marginal result](goal). -/
-- @node: lower_bandit_kernel_state_marginal
lemma lower_bandit_kernel_state_marginal {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (s s' : JointState d 1) (a : Bool) :
    ∑ r : Fin 2, (lowerBanditKernel hd word gamma s a (r, s')).toReal =
      lowerBanditStateWeight d s' := by
  simp_rw [lower_bandit_kernel_toReal hd word gamma hg0 hg1]
  rw [← Finset.sum_mul, lower_bandit_reward_weight_sum, one_mul]

/-- The finite path uses fair behavior and a uniform stationary initial state. -/
-- @node: lowerBanditFinite
noncomputable def lowerBanditFinite {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) : FiniteRewardModel T d 1 2 := by
  letI : NeZero d := ⟨hd.ne'⟩
  let K := lowerBanditKernel hd word gamma
  let init := pmfOfRealWeight (lowerBanditStateWeight d)
  let b := fun _ : Fin d ↦ pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ))
  exact {
    kernel := K
    rew := fun r ↦ if r = 0 then 0 else 1
    rew_mem := by intro r; split_ifs <;> norm_num
    init := init
    b := b
    e := fun x ↦ pmfOfRealWeight (lowerBanditPolicyWeight eta target x)
    law := finitePathPMF K init b
    law_generated := finitePathPMF_apply K init b }

/-- Every probability policy has the same constant-row state transition. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the policy](hyp:p), this establishes [the lower bandit finite policy kernel result](goal). -/
-- @node: lower_bandit_finite_policy_kernel
lemma lower_bandit_finite_policy_kernel {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (p : Fin d → PMF Bool) :
    finitePolicyKernel (lowerBanditFinite (T := T) hd word target gamma eta) p =
      fun _ s' ↦ lowerBanditStateWeight d s' := by
  funext s s'
  unfold finitePolicyKernel
  rw [show (∑ a : Bool, (p s.1 a).toReal *
      (∑ r : Fin 2, (lowerBanditFinite (T := T) hd word target gamma eta).kernel
        s a (r, s')).toReal) = ∑ a : Bool, (p s.1 a).toReal *
      (∑ r : Fin 2, (lowerBanditKernel hd word gamma s a (r, s')).toReal) by
    simp only [lowerBanditFinite]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    exact ENNReal.toReal_sum (fun r _ ↦ PMF.apply_ne_top _ _) ]
  simp_rw [lower_bandit_kernel_state_marginal hd word gamma hg0 hg1]
  rw [← Finset.sum_mul, sum_pmf_toReal_eq_one, one_mul]

/-- A constant-row kernel sends every probability vector to its row vector. For
[the code dimension](hyp:d), [the initial distribution](hyp:nu), and
[the initial distribution assumption](hyp:hnu), this establishes
[the lower bandit apply constant kernel result](goal). -/
-- @node: lower_bandit_apply_constant_kernel
lemma lower_bandit_apply_constant_kernel {d : Nat} (nu : JointState d 1 → ℝ)
    (hnu : ProbabilityVector nu) :
    applyKernel nu (fun _ s' ↦ lowerBanditStateWeight d s') = lowerBanditStateWeight d := by
  funext s'
  simp only [applyKernel, ← Finset.sum_mul, hnu.2, one_mul]

/-- The uniform vector is stationary for the constant-row kernel. For
[the code dimension](hyp:d) and [the code dimension assumption](hyp:hd), this establishes
[the lower bandit constant stationary result](goal). -/
-- @node: lower_bandit_constant_stationary
lemma lower_bandit_constant_stationary {d : Nat} (hd : 0 < d) :
    IsStationary (fun _ s' : JointState d 1 ↦ lowerBanditStateWeight d s')
      (lowerBanditStateWeight d) := by
  refine ⟨lower_bandit_state_probability hd, ?_⟩
  intro s'
  exact congrFun (lower_bandit_apply_constant_kernel _ (lower_bandit_state_probability hd)) s'

/-- The totalized stationary-law choice equals the unique uniform invariant law. For
[the code dimension](hyp:d) and [the code dimension assumption](hyp:hd), this establishes
[the lower bandit stationary law equality result](goal). -/
-- @node: lower_bandit_stationary_law_eq
lemma lower_bandit_stationary_law_eq {d : Nat} (hd : 0 < d) :
    stationaryLaw (fun _ s' : JointState d 1 ↦ lowerBanditStateWeight d s') =
      lowerBanditStateWeight d := by
  have hs := stationaryLaw_isStationary_of_exists
    ⟨_, lower_bandit_constant_stationary hd⟩
  funext s'
  exact (hs.2 s').symm.trans
    (congrFun (lower_bandit_apply_constant_kernel _ hs.1) s')

/-- The bandit state kernel has zero contraction for arbitrary starting laws. For
[the code dimension](hyp:d), [the contraction factor](hyp:alpha),
[the action assumption](hyp:ha), [the initial distribution](hyp:nu), [the nu'](hyp:nu'),
[the initial distribution assumption](hyp:hnu), and
[the initial distribution alternate assumption](hyp:hnu'), this establishes
[the lower bandit constant contraction result](goal). -/
-- @node: lower_bandit_constant_contraction
lemma lower_bandit_constant_contraction {d : Nat} (alpha : ℝ) (ha : 0 ≤ alpha)
    (nu nu' : JointState d 1 → ℝ) (hnu : ProbabilityVector nu)
    (hnu' : ProbabilityVector nu') :
    tvNorm (applyKernel nu (fun _ s' ↦ lowerBanditStateWeight d s') -
      applyKernel nu' (fun _ s' ↦ lowerBanditStateWeight d s')) ≤ alpha * tvNorm (nu - nu') := by
  rw [lower_bandit_apply_constant_kernel nu hnu, lower_bandit_apply_constant_kernel nu' hnu']
  simp only [sub_self, tvNorm, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero]
  exact mul_nonneg ha (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))

/-- PMF normalization preserves the equation (40) policy weights. For
[the code dimension](hyp:d), [the signal parameter](hyp:eta), [the eta0 assumption](hyp:heta0),
[the eta1 assumption](hyp:heta1), [the word](hyp:word), [the observed state](hyp:x), and
[the action](hyp:a), this establishes
[the lower bandit policy probability mass function to real result](goal). -/
-- @node: lower_bandit_policy_pmf_toReal
lemma lower_bandit_policy_pmf_toReal {d : Nat} (eta : ℝ) (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1) (word : Fin d → Bool) (x : Fin d) (a : Bool) :
    (pmfOfRealWeight (lowerBanditPolicyWeight eta word x) a).toReal =
      lowerBanditPolicyWeight eta word x a := by
  have hp := lower_bandit_policy_vector eta heta0 heta1 word x
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hp.1 hp.2 a,
    ENNReal.toReal_ofReal (hp.1 a)]

/-- The common logging policy assigns probability one half to either action. For
[the action](hyp:a), this establishes
[the lower bandit behavior probability mass function to real result](goal). -/
-- @node: lower_bandit_behavior_pmf_toReal
lemma lower_bandit_behavior_pmf_toReal (a : Bool) :
    (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal = 1 / 2 := by
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ (by intro a; norm_num)
    (by simp) a]
  norm_num

/-- Binary reward decoding keeps every kernel reward inside the unit interval. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the state](hyp:s), and [the action](hyp:a), this establishes
[the lower bandit reward unit result](goal). -/
-- @node: lower_bandit_reward_unit
lemma lower_bandit_reward_unit {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (s : JointState d 1) (a : Bool) :
    (embed (lowerBanditFinite (T := T) hd word target gamma eta)).K s a
      ((Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ) = 0 := by
  let F := lowerBanditFinite (T := T) hd word target gamma eta
  change ((F.kernel s a).map (fun q ↦ (F.rew q.1, q.2))).toMeasure _ = 0
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) (by measurability)]
  have hpre : (fun q : Fin 2 × JointState d 1 ↦ (F.rew q.1, q.2)) ⁻¹'
      ((Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ) = ∅ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ,
      and_true, Set.mem_empty_iff_false, iff_false]
    change ¬ ¬ ((if q.1 = 0 then (0 : ℝ) else 1) ∈ Set.Icc 0 1)
    split_ifs <;> norm_num
  rw [hpre, measure_empty]

/-- The fully observed family shares its logging rule and revealed target list. -/
-- @node: lowerBanditExperiment
noncomputable def lowerBanditExperiment (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (v : Fin M) (gamma eta : ℝ) : ModelIndex T M :=
  let raw := embed (lowerBanditFinite (T := T) hd (code v) (code v) gamma eta)
  { list_size := hM
    nX := d
    nH := 1
    Mx := {
      K := raw.K
      b := raw.b
      E := fun j x a ↦ (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal
      init := raw.init
      law := raw.law
      law_isProbability := raw.law_isProbability }
    target_policies := by
      intro j x
      constructor
      · intro a; exact ENNReal.toReal_nonneg
      · change (∑ a : Bool, (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal) = 1
        rw [← ENNReal.toReal_sum (fun a _ ↦ PMF.apply_ne_top _ a)]
        have hsum : (∑ a : Bool, pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a) = 1 := by
          simpa only [tsum_fintype] using ( pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x)).tsum_coe
        rw [hsum, ENNReal.toReal_one]
    kernel_law := embed_pomdpKernelLaw _
    reward_unit := lower_bandit_reward_unit hd (code v) (code v) gamma eta }

/-- The policy kernels of the decoded model still redraw the uniform state. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the policy](hyp:p), this establishes [the lower bandit embed policy kernel result](goal). -/
-- @node: lower_bandit_embed_policy_kernel
lemma lower_bandit_embed_policy_kernel {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (p : Fin d → PMF Bool) :
    policyKernel (embed (lowerBanditFinite (T := T) hd word target gamma eta))
      (fun x a ↦ (p x a).toReal) = fun _ s' ↦ lowerBanditStateWeight d s' := by
  rw [embed_policyKernel_eq, lower_bandit_finite_policy_kernel hd word target gamma eta hg0 hg1]

/-- The actual trajectory starts from the same stationary uniform state law. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), and [the g1 assumption](hyp:hg1),
this establishes [the lower bandit stationary start result](goal). -/
-- @node: lower_bandit_stationary_start
lemma lower_bandit_stationary_start {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) :
    StationaryStart (embed (lowerBanditFinite (T := T) hd word target gamma eta)) := by
  let : NeZero d := ⟨hd.ne'⟩
  let F := lowerBanditFinite (T := T) hd word target gamma eta
  have hk : policyKernel (embed F) (embed F).b =
      fun _ s' ↦ lowerBanditStateWeight d s' :=
    lower_bandit_embed_policy_kernel hd word target gamma eta hg0 hg1 F.b
  have hi : (embed F).init = lowerBanditStateWeight d := by
    let : NeZero d := ⟨hd.ne'⟩
    funext s
    have hp := lower_bandit_state_probability hd
    change (pmfOfRealWeight (lowerBanditStateWeight d) s).toReal = _
    rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hp.1 hp.2 s,
      ENNReal.toReal_ofReal (hp.1 s)]
  apply embed_stationaryStart F
  · rw [hi, hk]
    exact lower_bandit_constant_stationary hd
  · rw [hk, lower_bandit_stationary_law_eq hd, hi]

/-- The distinct codewords yield distinct supplied target policies. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the binary code assumption](hyp:hcode),
[the codeword index](hyp:v), [the rate parameter](hyp:gamma), [the signal parameter](hyp:eta),
[the eta0 assumption](hyp:heta0), and [the eta1 assumption](hyp:heta1), this establishes
[the lower bandit supplied list result](goal). -/
-- @node: lower_bandit_supplied_list
lemma lower_bandit_supplied_list (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (hcode : CodeSeparated code) (v : Fin M)
    (gamma eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    SuppliedList (lowerBanditExperiment T M d hd hM code v gamma eta) := by
  intro j k hjk
  apply hcode.1
  apply lower_bandit_policy_injective eta heta0
  funext x
  have h := congrArg (fun p ↦ p x true) hjk
  simpa only [lowerBanditExperiment, lower_bandit_policy_pmf_toReal eta heta0.le heta1,
    lowerBanditPolicyWeight, if_true] using h

/-- Each code policy obeys the common action-ratio envelope. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the action-overlap factor](hyp:L),
[the eta0 assumption](hyp:heta0), [the eta1 assumption](hyp:heta1), and
[the action-overlap factor assumption](hyp:hL), this establishes
[the lower bandit action overlap model result](goal). -/
-- @node: lower_bandit_action_overlap_model
lemma lower_bandit_action_overlap_model (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (v : Fin M) (gamma eta L : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hL : 1 + eta ≤ L) :
    ListActionOverlap (lowerBanditExperiment T M d hd hM code v gamma eta) L := by
  intro j
  change PolicyVector
    (fun x a ↦ (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal) ∧
    ∀ (x : Fin d) (a : Bool),
      (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal ≤
      L * (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal
  constructor
  · simpa only [lowerBanditExperiment, ListPomdpExperiment.toRaw,
      lower_bandit_policy_pmf_toReal eta heta0 heta1] using
      lower_bandit_policy_vector eta heta0 heta1 (code j)
  · intro x a
    change (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal ≤
      L * (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal
    rw [lower_bandit_policy_pmf_toReal eta heta0 heta1, lower_bandit_behavior_pmf_toReal]
    have h := lower_bandit_action_overlap eta L heta0 hL (code j x)
    cases a <;> simp only [lowerBanditPolicyWeight, Bool.false_eq_true, if_false, if_true] <;>
      linarith [h.1, h.2]

/-- Behavior and each listed target have zero state-kernel contraction. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the contraction factor](hyp:alpha),
[the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and [the action assumption](hyp:ha),
this establishes [the lower bandit uniform contraction result](goal). -/
-- @node: lower_bandit_uniform_contraction
lemma lower_bandit_uniform_contraction (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (v : Fin M) (gamma eta alpha : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16) (ha : 0 ≤ alpha) :
    ListUniformContraction (lowerBanditExperiment T M d hd hM code v gamma eta) alpha := by
  intro j
  let F := lowerBanditFinite (T := T) hd (code v) (code j) gamma eta
  change UniformContraction alpha (embed F)
  intro p hp nu nu' hnu hnu'
  rcases hp with rfl | rfl
  · change tvNorm (applyKernel nu (policyKernel (embed F) (fun x a ↦ (F.b x a).toReal)) -
      applyKernel nu' (policyKernel (embed F) (fun x a ↦ (F.b x a).toReal))) ≤ _
    rw [lower_bandit_embed_policy_kernel hd (code v) (code j) gamma eta hg0 hg1 F.b]
    exact lower_bandit_constant_contraction alpha ha nu nu' hnu hnu'
  · change tvNorm (applyKernel nu (policyKernel (embed F) (fun x a ↦ (F.e x a).toReal)) -
      applyKernel nu' (policyKernel (embed F) (fun x a ↦ (F.e x a).toReal))) ≤ _
    rw [lower_bandit_embed_policy_kernel hd (code v) (code j) gamma eta hg0 hg1 F.e]
    exact lower_bandit_constant_contraction alpha ha nu nu' hnu hnu'

/-- The target and behavior stationary laws coincide, so every radius is legal. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the latent-overlap radius](hyp:C),
[the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the latent-overlap radius assumption](hyp:hC), this establishes
[the lower bandit stationary overlap result](goal). -/
-- @node: lower_bandit_stationary_overlap
lemma lower_bandit_stationary_overlap (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (v : Fin M) (gamma eta C : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16) (hC : 1 ≤ C) :
    ListLatentStationaryOverlap (lowerBanditExperiment T M d hd hM code v gamma eta) C := by
  refine ⟨hC, fun j ↦ ⟨hC, ?_⟩⟩
  intro s
  change stationaryLaw (policyKernel
    (embed (lowerBanditFinite (T := T) hd (code v) (code j) gamma eta))
    (fun x a ↦ (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal)) s ≤
    C * stationaryLaw (policyKernel
    (embed (lowerBanditFinite (T := T) hd (code v) (code j) gamma eta))
    (fun x a ↦ (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal)) s
  rw [lower_bandit_embed_policy_kernel hd (code v) (code j) gamma eta hg0 hg1,
    lower_bandit_embed_policy_kernel hd (code v) (code j) gamma eta hg0 hg1,
    lower_bandit_stationary_law_eq hd]
  exact (le_mul_of_one_le_left ((lower_bandit_state_probability hd).1 s) hC)

/-- The fully observed bandit code belongs to every certified-overlap class. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the binary code assumption](hyp:hcode),
[the codeword index](hyp:v), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the g0 assumption](hyp:hg0),
[the g1 assumption](hyp:hg1), [the eta0 assumption](hyp:heta0),
[the eta1 assumption](hyp:heta1), and [the action-overlap factor assumption](hyp:hL), this
establishes [the lower bandit membership result](goal). -/
-- @node: lower_bandit_membership
lemma lower_bandit_membership (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (hcode : CodeSeparated code) (v : Fin M)
    (t0 zeta C gamma eta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hL : 1 + eta ≤ policyFactor zeta) :
    PolicyListClass t0 zeta C (lowerBanditExperiment T M d hd hM code v gamma eta) := by
  refine ⟨ht0, hzeta, hC, ⟨hd, by change 0 < (1 : Nat); omega⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact embed_sequentialIgnorability
      (lowerBanditFinite (T := T) hd (code v) (code v) gamma eta)
  · exact lower_bandit_stationary_start hd (code v) (code v) gamma eta hg0 hg1
  · exact lower_bandit_uniform_contraction T M d hd hM code v gamma eta _ hg0 hg1
      (Real.exp_pos _).le
  · exact lower_bandit_action_overlap_model T M d hd hM code v gamma eta _ heta0.le heta1 hL
  · exact lower_bandit_stationary_overlap T M d hd hM code v gamma eta C hg0 hg1 hC
  · exact lower_bandit_supplied_list T M d hd hM code hcode v gamma eta heta0 heta1

/-- The common kernel's conditional reward mean is exactly equation (41). For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1),
[the state](hyp:s), and [the action](hyp:a), this establishes
[the lower bandit kernel reward mean result](goal). -/
-- @node: lower_bandit_kernel_reward_mean
lemma lower_bandit_kernel_reward_mean {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (s : JointState d 1) (a : Bool) :
    (∑ q : Fin 2 × JointState d 1, (lowerBanditKernel hd word gamma s a q).toReal *
      (if q.1 = 0 then (0 : ℝ) else 1)) = lowerBanditRewardMean gamma (word s.1) a := by
  simp_rw [lower_bandit_kernel_toReal hd word gamma hg0 hg1]
  rw [Fintype.sum_prod_type]
  have hrow (r : Fin 2) :
      (∑ s' : JointState d 1, lowerBanditRewardWeight gamma (word s.1) a r *
        lowerBanditStateWeight d s' * (if r = 0 then (0 : ℝ) else 1)) =
      lowerBanditRewardWeight gamma (word s.1) a r * (if r = 0 then (0 : ℝ) else 1) := by
    simp_rw [mul_right_comm _ (lowerBanditStateWeight d _)]
    rw [← Finset.mul_sum, (lower_bandit_state_probability hd).2, mul_one]
  simp_rw [hrow]
  simp [Fin.sum_univ_two, lowerBanditRewardWeight]

/-- Averaging under a code target recovers the stationary value in equation (42). For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1),
[the eta0 assumption](hyp:heta0), and [the eta1 assumption](hyp:heta1), this establishes
[the lower bandit finite target value result](goal). -/
-- @node: lower_bandit_finite_target_value
lemma lower_bandit_finite_target_value {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    finiteTargetValue (lowerBanditFinite (T := T) hd word target gamma eta) =
      lowerBanditCodeValue eta gamma word target := by
  unfold finiteTargetValue
  rw [lower_bandit_finite_policy_kernel hd word target gamma eta hg0 hg1,
    lower_bandit_stationary_law_eq hd]
  change (∑ s : JointState d 1, lowerBanditStateWeight d s *
    ∑ a : Bool, (pmfOfRealWeight (lowerBanditPolicyWeight eta target s.1) a).toReal *
      ∑ q : Fin 2 × JointState d 1, (lowerBanditKernel hd word gamma s a q).toReal *
        (if q.1 = 0 then (0 : ℝ) else 1)) = _
  simp_rw [lower_bandit_kernel_reward_mean hd word gamma hg0 hg1,
    lower_bandit_policy_pmf_toReal eta heta0 heta1]
  rw [Fintype.sum_prod_type]
  simp only [lowerBanditStateWeight, Fin.sum_univ_one, Fintype.univ_bool, Finset.sum_insert,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton,
    lowerBanditPolicyWeight, lowerBanditRewardMean, Bool.false_eq_true,
    if_false, if_true, mul_one, mul_neg_one]
  rw [← Finset.mul_sum]
  convert lower_bandit_code_value_mean hd eta gamma word target using 1
  congr 1

/-- The assembled model has the displayed stationary value for every supplied policy. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the candidate index](hyp:j),
[the rate parameter](hyp:gamma), [the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0),
[the g1 assumption](hyp:hg1), [the eta0 assumption](hyp:heta0), and
[the eta1 assumption](hyp:heta1), this establishes [the lower bandit policy value result](goal). -/
-- @node: lower_bandit_policy_value
lemma lower_bandit_policy_value (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (v j : Fin M) (gamma eta : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    policyValue (lowerBanditExperiment T M d hd hM code v gamma eta) j =
      lowerBanditCodeValue eta gamma (code v) (code j) := by
  change targetValue (embed (lowerBanditFinite (T := T) hd (code v) (code j) gamma eta)) = _
  rw [embed_targetValue_eq]
  exact lower_bandit_finite_target_value hd (code v) (code j) gamma eta hg0 hg1 heta0 heta1

/-- Code separation supplies the actual model's regret gap in equation (43). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the binary code assumption](hyp:hcode),
[the codeword index](hyp:v), [the candidate index](hyp:j), [the jv assumption](hyp:hjv),
[the rate parameter](hyp:gamma), [the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0),
[the g1 assumption](hyp:hg1), [the eta0 assumption](hyp:heta0), and
[the eta1 assumption](hyp:heta1), this establishes [the lower bandit model gap result](goal). -/
-- @node: lower_bandit_model_gap
lemma lower_bandit_model_gap (T M d : Nat) (hd : 0 < d) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (hcode : CodeSeparated code) (v j : Fin M)
    (hjv : j ≠ v) (gamma eta : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    gamma * eta / 2 ≤
      policyValue (lowerBanditExperiment T M d hd hM code v gamma eta) v -
      policyValue (lowerBanditExperiment T M d hd hM code v gamma eta) j := by
  rw [lower_bandit_policy_value T M d hd hM code v v gamma eta hg0 hg1 heta0 heta1,
    lower_bandit_policy_value T M d hd hM code v j gamma eta hg0 hg1 heta0 heta1]
  exact lower_bandit_separated_gap code hcode hd eta gamma heta0 hg0 v j hjv.symm

end CausalSmith.Stat.PomdpPolicyclassRegret
