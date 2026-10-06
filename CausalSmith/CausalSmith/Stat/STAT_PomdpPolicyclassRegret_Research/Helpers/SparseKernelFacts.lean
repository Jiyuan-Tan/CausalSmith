module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthWeights
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparsePacking

/-! # Kernel facts for the sparse common-kernel packing -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Both alphabets in the sparse experiment are nonempty. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse packing finite state result](goal). -/
-- @node: sparse_packing_finite_state
lemma sparse_packing_finite_state (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool)
    (hCode : CodeSeparated code) (v : Fin M) :
    FiniteState (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v) := by
  change 0 < d * hdepth Q ∧ 0 < 2 * (Q + 1)
  constructor <;> simp [hdepth, hd]

/-- The sparse path draws each action from its displayed behavior rule. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse packing sequential ignorability result](goal). -/
-- @node: sparse_packing_sequential_ignorability
lemma sparse_packing_sequential_ignorability (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool)
    (hCode : CodeSeparated code) (v : Fin M) :
    ListSequentialIgnorability
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v) := by
  change SequentialIgnorability
    (embed (sparseFinite (T := T) hd t0 zeta C code v false))
  exact embed_sequentialIgnorability _

/-- The normalized stationary mass at terminal depth dominates its unnormalized geometric mass.
For [the hidden-depth scale](hyp:Q), [the contraction coefficient](hyp:α),
[the α0 assumption](hyp:hα0), and [the α1 assumption](hyp:hα1), this establishes
[the sparse terminal depth mass lower result](goal). -/
-- @node: sparse_terminal_depth_mass_lower
lemma sparse_terminal_depth_mass_lower (Q : Nat) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (1 - α) * α ^ Q ≤ (1 - α) * α ^ Q / (1 - α ^ (Q + 1)) := by
  have hpow : α ^ (Q + 1) < 1 := pow_lt_one₀ hα0 hα1 (by omega)
  have hden : 0 < 1 - α ^ (Q + 1) := by linarith
  have hbase : 0 ≤ (1 - α) * α ^ Q :=
    mul_nonneg (by linarith) (pow_nonneg hα0 _)
  apply (le_div_iff₀ hden).2
  nlinarith [mul_nonneg hbase (pow_nonneg hα0 (Q + 1))]

/-- The exact terminal-depth value formula and code separation imply the uniform gap coefficient
used in the packing theorem. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the binary code](hyp:code), [the code assumption](hyp:hCode),
[the codeword index](hyp:v), [the observed word](hyp:w), [the vw assumption](hyp:hvw),
[the hidden-depth scale](hyp:Q), [the hidden-depth scale assumption](hyp:hQ),
[the code dimension assumption](hyp:hd), [the c](hyp:c), [the q](hyp:q),
[the contraction coefficient](hyp:α), [the policy](hyp:p), [the c assumption](hyp:hc),
[the q assumption](hyp:hq), [the α0 assumption](hyp:hα0), [the α1 assumption](hyp:hα1),
[the p0 assumption](hyp:hp0), and [the p1 assumption](hyp:hp1), this establishes
[the sparse terminal value gap numeric result](goal). -/
-- @node: sparse_terminal_value_gap_numeric
lemma sparse_terminal_value_gap_numeric {M d : Nat}
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code)
    (v w : Fin M) (hvw : v ≠ w) (Q : Nat) (hQ : 1 ≤ Q)
    (hd : 0 < d) (c q α p : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (c * q / 4) * ((1 - α) * α ^ Q / (1 - α ^ (Q + 1))) *
      (1 - (1 - (1 - p) * (hammingDistance code v w : ℝ) /
        ((d : ℝ) * hdepth Q)) ^ Q) ≥
      (c * (1 - α) * (1 - Real.exp (-(1 - p) / 8)) / 4) * q * α ^ Q := by
  let κ := 1 - Real.exp (-(1 - p) / 8)
  let mass := (1 - α) * α ^ Q / (1 - α ^ (Q + 1))
  let gap := 1 - (1 - (1 - p) * (hammingDistance code v w : ℝ) /
    ((d : ℝ) * hdepth Q)) ^ Q
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    have he : Real.exp (-(1 - p) / 8) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hmass : (1 - α) * α ^ Q ≤ mass :=
    sparse_terminal_depth_mass_lower Q α hα0 hα1
  have hbase : 0 ≤ (1 - α) * α ^ Q :=
    mul_nonneg (by linarith) (pow_nonneg hα0 _)
  have hgap : κ ≤ gap :=
    sparse_separated_code_gap code hCode v w hvw Q hQ hd p hp0 hp1.le
  have hstep1 : (c * q / 4) * ((1 - α) * α ^ Q) * κ ≤
      (c * q / 4) * mass * κ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by positivity)) hκ
  have hstep2 : (c * q / 4) * mass * κ ≤
      (c * q / 4) * mass * gap := by
    exact mul_le_mul_of_nonneg_left hgap
      (mul_nonneg (by positivity) (le_trans hbase hmass))
  change (c * q / 4) * mass * gap ≥ _
  calc
    (c * (1 - α) * κ / 4) * q * α ^ Q =
        (c * q / 4) * ((1 - α) * α ^ Q) * κ := by ring
    _ ≤ (c * q / 4) * mass * κ := hstep1
    _ ≤ (c * q / 4) * mass * gap := hstep2

/-- The common behavior rule has its displayed Bernoulli weights. For
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q), [the observed state](hyp:x), and
[the action](hyp:a), this establishes
[the sparse behavior probability mass function to real result](goal). -/
-- @node: sparse_behavior_pmf_toReal
lemma sparse_behavior_pmf_toReal (zeta : ℝ) (hzeta : 0 < zeta)
    (d Q : Nat) (x : Fin (d * hdepth Q)) (a : Bool) :
    (sparseBehaviorPMF zeta d Q x a).toReal = sparseBehaviorWeight zeta a := by
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  have hnonneg : ∀ b : Bool, 0 ≤ sparseBehaviorWeight zeta b := by
    intro b
    cases b <;> simp [sparseBehaviorWeight] <;> linarith
  have hsum : ∑ b : Bool, sparseBehaviorWeight zeta b = 1 := by
    simp [sparseBehaviorWeight]
  change (pmfOfRealWeight (sparseBehaviorWeight zeta) a).toReal = _
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hnonneg hsum a,
    ENNReal.toReal_ofReal (hnonneg a)]

/-- Every listed target is dominated by `L` times the common behavior rule. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), [the code assumption](hyp:hCode), and [the codeword index](hyp:v),
this establishes [the sparse packing action overlap result](goal). -/
-- @node: sparse_packing_action_overlap
lemma sparse_packing_action_overlap (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (hzeta : 0 < zeta)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    ListActionOverlap
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v)
      (policyFactor zeta) := by
  intro j
  change (∀ x : Fin (d * hdepth Q),
      (∀ a : Bool, 0 ≤ (sparseTargetPMF hd zeta code j x a).toReal) ∧
        ∑ a : Bool, (sparseTargetPMF hd zeta code j x a).toReal = 1) ∧
    ∀ (x : Fin (d * hdepth Q)) (a : Bool),
      (sparseTargetPMF hd zeta code j x a).toReal ≤
        policyFactor zeta * (sparseBehaviorPMF zeta d Q x a).toReal
  constructor
  · intro x
    constructor
    · intro a
      positivity
    · simp only [sparse_target_pmf_toReal hd zeta hzeta code]
      by_cases hx : exceptionalContext hd code j x
      · simp [sparseTargetWeight, sparseBehaviorWeight, hx]
      · simp [sparseTargetWeight, hx]
  · intro x a
    rw [sparse_target_pmf_toReal hd zeta hzeta code,
      sparse_behavior_pmf_toReal zeta hzeta]
    have hL : 1 < policyFactor zeta := by
      unfold policyFactor
      exact Real.one_lt_exp_iff.mpr hzeta
    have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
    have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by linarith)).mpr hL.le
    by_cases hx : exceptionalContext hd code j x
    · cases a <;> simp [sparseTargetWeight, sparseBehaviorWeight, hx] <;> nlinarith
    · cases a <;> simp [sparseTargetWeight, sparseBehaviorWeight, hx] <;>
        nlinarith [inv_mul_cancel₀ (show policyFactor zeta ≠ 0 by linarith)]

/-- The terminal reward signal lies strictly between zero and one quarter. For
[the mixing scale](hyp:t0) and [the mixing scale assumption](hyp:ht0), this establishes
[the sparse signal bounds result](goal). -/
-- @node: sparse_signal_bounds
lemma sparse_signal_bounds (t0 : ℝ) (ht0 : 0 < t0) :
    0 < sparseSignal t0 ∧ sparseSignal t0 < 1 / 4 := by
  have hα0 : 0 < mixingAlpha t0 := Real.exp_pos _
  have hα1 : mixingAlpha t0 < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hinv : 0 < 1 / t0 := by positivity
    linarith
  unfold sparseSignal
  constructor <;> linarith

/-- The two displayed reward weights are nonnegative Bernoulli probabilities. For
[the mixing scale](hyp:t0), [the mixing scale assumption](hyp:ht0),
[the hidden-depth scale](hyp:Q), [the stated assumption](hyp:h), and [the reward symbol](hyp:r),
this establishes [the sparse reward weight nonnegativity result](goal). -/
-- @node: sparse_reward_weight_nonneg
lemma sparse_reward_weight_nonneg (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (h : Fin (2 * (Q + 1))) (r : Fin 2) :
    0 ≤ sparseRewardWeight t0 Q h r := by
  have hc := sparse_signal_bounds t0 ht0
  unfold sparseRewardWeight signValue
  fin_cases r <;> split_ifs <;> norm_num <;> linarith

/-- Summing the fair or terminal reward probabilities gives unit mass. For
[the mixing scale](hyp:t0), [the hidden-depth scale](hyp:Q), and [the stated assumption](hyp:h),
this establishes [the sparse reward weight sum result](goal). -/
-- @node: sparse_reward_weight_sum
lemma sparse_reward_weight_sum (t0 : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) :
    ∑ r : Fin 2, sparseRewardWeight t0 Q h r = 1 := by
  by_cases hh : hiddenDepth Q h = Q
  · simp [Fin.sum_univ_two, sparseRewardWeight, hh]
    ring
  · simp [sparseRewardWeight, hh]

/-- The mean decoded reward is fair away from terminal depth and has the prescribed
sign-dependent signal at terminal depth. For [the mixing scale](hyp:t0),
[the hidden-depth scale](hyp:Q), and [the stated assumption](hyp:h), this establishes
[the sparse reward weight mean result](goal). -/
-- @node: sparse_reward_weight_mean
lemma sparse_reward_weight_mean (t0 : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) :
    ∑ r : Fin 2, (if r = 0 then (0 : ℝ) else 1) *
      sparseRewardWeight t0 Q h r =
      1 / 2 + sparseSignal t0 * signValue (hiddenSign Q h) *
        (if hiddenDepth Q h = Q then 1 else 0) / 2 := by
  simp [Fin.sum_univ_two, sparseRewardWeight]
  ring

/-- PMF normalization preserves the displayed reward probabilities. For
[the mixing scale](hyp:t0), [the mixing scale assumption](hyp:ht0),
[the hidden-depth scale](hyp:Q), [the stated assumption](hyp:h), and [the reward symbol](hyp:r),
this establishes [the sparse reward probability mass function to real result](goal). -/
-- @node: sparse_reward_pmf_toReal
lemma sparse_reward_pmf_toReal (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (h : Fin (2 * (Q + 1))) (r : Fin 2) :
    (pmfOfRealWeight (sparseRewardWeight t0 Q h) r).toReal =
      sparseRewardWeight t0 Q h r := by
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
    (sparse_reward_weight_nonneg t0 ht0 Q h)
    (sparse_reward_weight_sum t0 Q h) r,
    ENNReal.toReal_ofReal (sparse_reward_weight_nonneg t0 ht0 Q h r)]

/-- The reset sign mean is a valid bias for every admissible radius. For
[the latent-overlap radius](hyp:C) and [the latent-overlap radius assumption](hyp:hC), this
establishes [the sparse epsilon bounds result](goal). -/
-- @node: sparse_epsilon_bounds
lemma sparse_epsilon_bounds (C : ℝ) (hC : 1 ≤ C) :
    0 ≤ sparseEpsilon C ∧ sparseEpsilon C ≤ 1 / 2 := by
  have hCpos : 0 < C := by linarith
  have hq0 : 0 ≤ (C - 1) / C := div_nonneg (by linarith) hCpos.le
  have hq1 : (C - 1) / C ≤ 1 := (div_le_one hCpos).mpr (by linarith)
  change 0 ≤ ((C - 1) / C) / 2 ∧ ((C - 1) / C) / 2 ≤ 1 / 2
  constructor <;> linarith

/-- Reset sign probabilities are nonnegative for both reference and alternative laws. For
[the latent-overlap radius](hyp:C), [the latent-overlap radius assumption](hyp:hC),
[the fair-reference flag](hyp:fair), and [the observed prefix](hyp:u), this establishes
[the sparse reset sign weight nonnegativity result](goal). -/
-- @node: sparse_reset_sign_weight_nonneg
lemma sparse_reset_sign_weight_nonneg (C : ℝ) (hC : 1 ≤ C) (fair u : Bool) :
    0 ≤ resetSignWeight C fair u := by
  have he := sparse_epsilon_bounds C hC
  cases fair <;> cases u <;> simp [resetSignWeight, signValue] <;> linarith

/-- The sparse transition has nonnegative state weights. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the state](hyp:s), [the successor state](hyp:s'), and [the action](hyp:a), this establishes
[the sparse state weight nonnegativity result](goal). -/
-- @node: sparse_state_weight_nonneg
lemma sparse_state_weight_nonneg {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s s' : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    0 ≤ sparseStateWeight hd t0 C code v fair s s' a := by
  have hα0 : 0 ≤ mixingAlpha t0 := (mixingAlpha_pos ht0).le
  have hα1 : 0 ≤ 1 - mixingAlpha t0 := sub_nonneg.mpr (mixingAlpha_lt_one ht0).le
  have hr := sparse_reset_sign_weight_nonneg C hC fair (hiddenSign Q s'.2)
  unfold sparseStateWeight
  dsimp only
  split_ifs <;> positivity

/-- The existing depth/sign enumeration also decodes the sparse hidden depth. For
[the hidden-depth scale](hyp:Q) and [the z](hyp:z), this establishes
[the sparse hidden depth enumeration result](goal). -/
-- @node: sparse_hidden_depth_enumeration
lemma sparse_hidden_depth_enumeration (Q : Nat) (z : Fin (Q + 1) × Fin 2) :
    hiddenDepth Q (depthSignEquiv Q z) = z.1.val := by
  exact latentDepth_depthSignEquiv Q z

/-- The existing depth/sign enumeration also decodes the sparse sign bit. For
[the hidden-depth scale](hyp:Q) and [the candidate index](hyp:j), this establishes
[the sparse hidden sign enumeration result](goal). -/
-- @node: sparse_hidden_sign_enumeration
lemma sparse_hidden_sign_enumeration (Q : Nat) (j : Fin (Q + 1)) :
    hiddenSign Q (depthSignEquiv Q (j, 0)) = false ∧
      hiddenSign Q (depthSignEquiv Q (j, 1)) = true := by
  exact ⟨latentSign_depthSignEquiv_zero Q j, latentSign_depthSignEquiv_one Q j⟩

/-- Summing over the new sign leaves the reset or advance depth mass and one uniform-context
factor. This covers retained and redrawn signs alike. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the fair-reference flag](hyp:fair), [the state](hyp:s), [the action](hyp:a), [the x'](hyp:x'),
and [the j'](hyp:j'), this establishes [the sparse state weight sum at depth result](goal). -/
-- @node: sparse_state_weight_sum_at_depth
lemma sparse_state_weight_sum_at_depth {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (x' : Fin (d * hdepth Q)) (j' : Fin (Q + 1)) :
    (∑ u' : Fin 2, sparseStateWeight hd t0 C code v fair s
      (x', depthSignEquiv Q (j', u')) a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        (if hiddenDepth Q s.2 = Q then
          if j'.val = 0 then 1 else 0
        else
          (if j'.val = 0 then 1 - mixingAlpha t0 else 0) +
            (if j'.val = hiddenDepth Q s.2 + 1 then mixingAlpha t0 else 0)) := by
  classical
  rw [Fin.sum_univ_two]
  by_cases hterm : hiddenDepth Q s.2 = Q <;>
    by_cases hj0 : j'.val = 0 <;>
    by_cases hjnext : j'.val = hiddenDepth Q s.2 + 1 <;>
    by_cases hretain : retentionIndicator hd code v s.1 a = 1 <;>
    cases fair <;> generalize hu : hiddenSign Q s.2 = u <;> cases u <;>
    simp [sparseStateWeight, sparse_hidden_depth_enumeration,
      (sparse_hidden_sign_enumeration Q j').1,
      (sparse_hidden_sign_enumeration Q j').2,
      resetSignWeight, signValue, hu, hterm, hj0, hjnext, hretain] <;> ring

/-- Every sparse transition row has total mass one before PMF normalization. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the codeword index](hyp:v), [the fair-reference flag](hyp:fair), [the state](hyp:s), and
[the action](hyp:a), this establishes [the sparse state weight sum result](goal). -/
-- @node: sparse_state_weight_sum
lemma sparse_state_weight_sum {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    ∑ s', sparseStateWeight hd t0 C code v fair s s' a = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  have hhidden (x' : Fin (d * hdepth Q)) :
      (∑ h', sparseStateWeight hd t0 C code v fair s (x', h') a) =
        ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
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
  simp_rw [hhidden]
  have hn : (0 : ℝ) < (d * hdepth Q : Nat) := by
    exact_mod_cast (Nat.mul_pos hd (show 0 < hdepth Q by simp [hdepth]))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (ne_of_gt hn)

/-- The joint reward/transition product has total mass one, so its normalization does not change
the common-kernel construction. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the fair-reference flag](hyp:fair), [the state](hyp:s), and [the action](hyp:a), this
establishes [the sparse kernel weight sum result](goal). -/
-- @node: sparse_kernel_weight_sum
lemma sparse_kernel_weight_sum {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    (∑ p : Fin 2 × JointState (d * hdepth Q) (2 * (Q + 1)),
      (if fair then (1 / 2 : ℝ) else sparseRewardWeight t0 Q s.2 p.1) *
        sparseStateWeight hd t0 C code v fair s p.2 a) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sparse_state_weight_sum, mul_one]
  cases fair
  · exact sparse_reward_weight_sum t0 Q s.2
  · norm_num

/-- The kernel's PMF stores exactly the paper's independent reward and state-transition factors.
For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the state](hyp:s), [the action](hyp:a), and [the policy](hyp:p), this establishes
[the sparse kernel to real result](goal). -/
-- @node: sparse_kernel_toReal
lemma sparse_kernel_toReal {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool)
    (p : Fin 2 × JointState (d * hdepth Q) (2 * (Q + 1))) :
    (sparseKernel hd t0 C code v fair s a p).toReal =
      (if fair then (1 / 2 : ℝ) else sparseRewardWeight t0 Q s.2 p.1) *
        sparseStateWeight hd t0 C code v fair s p.2 a := by
  let : NeZero (d * hdepth Q) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
  have hnonneg : ∀ p : Fin 2 × JointState (d * hdepth Q) (2 * (Q + 1)),
      0 ≤ (if fair then (1 / 2 : ℝ) else sparseRewardWeight t0 Q s.2 p.1) *
        sparseStateWeight hd t0 C code v fair s p.2 a := by
    intro p
    apply mul_nonneg
    · cases fair
      · exact sparse_reward_weight_nonneg t0 ht0 Q s.2 p.1
      · norm_num
    · exact sparse_state_weight_nonneg hd t0 C ht0 hC code v fair s p.2 a
  unfold sparseKernel
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hnonneg
    (sparse_kernel_weight_sum hd t0 C code v fair s a) p,
    ENNReal.toReal_ofReal (hnonneg p)]

/-- Marginalizing the reward recovers the stated sparse transition weights. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the state](hyp:s), [the successor state](hyp:s'), and [the action](hyp:a), this establishes
[the sparse kernel state marginal result](goal). -/
-- @node: sparse_kernel_state_marginal
lemma sparse_kernel_state_marginal {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s s' : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    (∑ r : Fin 2, (sparseKernel hd t0 C code v fair s a (r, s')).toReal) =
      sparseStateWeight hd t0 C code v fair s s' a := by
  simp_rw [sparse_kernel_toReal hd t0 C ht0 hC code v fair]
  rw [← Finset.sum_mul]
  suffices hmass : (∑ r : Fin 2,
      if fair then (1 / 2 : ℝ) else sparseRewardWeight t0 Q s.2 r) = 1 by
    rw [hmass, one_mul]
  cases fair
  · exact sparse_reward_weight_sum t0 Q s.2
  · norm_num

/-- The actual alternative kernel has the terminal reward regression in (22), independently of
the action and of the next state. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the state](hyp:s), and [the action](hyp:a), this establishes
[the sparse kernel reward mean result](goal). -/
-- @node: sparse_kernel_reward_mean
lemma sparse_kernel_reward_mean {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    (∑ p : Fin 2 × JointState (d * hdepth Q) (2 * (Q + 1)),
      (if p.1 = 0 then (0 : ℝ) else 1) *
        (sparseKernel hd t0 C code v false s a p).toReal) =
      1 / 2 + sparseSignal t0 * signValue (hiddenSign Q s.2) *
        (if hiddenDepth Q s.2 = Q then 1 else 0) / 2 := by
  simp_rw [sparse_kernel_toReal hd t0 C ht0 hC code v false,
    Bool.false_eq_true, if_false, ← mul_assoc]
  rw [Fintype.sum_prod_type]
  dsimp only
  calc
    _ = ∑ r : Fin 2, ((if r = 0 then (0 : ℝ) else 1) *
        sparseRewardWeight t0 Q s.2 r) *
        (∑ s', sparseStateWeight hd t0 C code v false s s' a) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = _ := by
      simp only [sparse_state_weight_sum, mul_one]
      exact sparse_reward_weight_mean t0 Q s.2

/-- Decoding the binary reward symbols preserves the terminal conditional mean. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), [the state](hyp:s), and
[the action](hyp:a), this establishes [the sparse packing conditional reward mean result](goal). -/
-- @node: sparse_packing_conditional_reward_mean
lemma sparse_packing_conditional_reward_mean (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    (∫ y, y.1 ∂((sparsePackingExperiment T M d Q hd hDim hM
      t0 zeta C code hCode v).Mx.K s a)) =
      1 / 2 + sparseSignal t0 * signValue (hiddenSign Q s.2) *
        (if hiddenDepth Q s.2 = Q then 1 else 0) / 2 := by
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  change (∫ y, y.1 ∂(((F.kernel s a).map
    (fun p ↦ (F.rew p.1, p.2))).toMeasure)) = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
    measurable_fst.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  simpa only [F, sparseFinite, mul_comm] using
    sparse_kernel_reward_mean hd t0 C ht0 hC code v s a

/-- Every listed policy has the same statewise reward regression, since only the terminal hidden
sign enters the reward kernel. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), [the candidate index](hyp:j), and
[the state](hyp:s), this establishes [the sparse packing reward regression result](goal). -/
-- @node: sparse_packing_reward_regression
lemma sparse_packing_reward_regression (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v j : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) :
    listRewardRegression
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v)
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E j) s =
      1 / 2 + sparseSignal t0 * signValue (hiddenSign Q s.2) *
        (if hiddenDepth Q s.2 = Q then 1 else 0) / 2 := by
  unfold listRewardRegression
  simp_rw [sparse_packing_conditional_reward_mean T M d Q hd hDim hM
    t0 zeta C ht0 hC code hCode v]
  rw [← Finset.sum_mul]
  have hmass : (∑ a : Bool,
      (sparsePackingExperiment T M d Q hd hDim hM
        t0 zeta C code hCode v).Mx.E j s.1 a) = 1 := by
    change (∑ a : Bool, (sparseTargetPMF hd zeta code j s.1 a).toReal) = 1
    simp only [sparse_target_pmf_toReal hd zeta hzeta code]
    by_cases hx : exceptionalContext hd code j s.1
    · simp [sparseTargetWeight, sparseBehaviorWeight, hx]
    · simp [sparseTargetWeight, hx]
  rw [hmass, one_mul]

/-- The decoded target transition matrix is the action average of the explicit sparse state
weights. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the dim assumption](hyp:hDim),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), [the candidate index](hyp:j),
[the state](hyp:s), and [the successor state](hyp:s'), this establishes
[the sparse packing policy kernel result](goal). -/
-- @node: sparse_packing_policy_kernel
lemma sparse_packing_policy_kernel (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v j : Fin M)
    (s s' : JointState (d * hdepth Q) (2 * (Q + 1))) :
    listPolicyKernel
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v)
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E j)
      s s' = ∑ a : Bool, sparseTargetWeight hd zeta code j s.1 a *
        sparseStateWeight hd t0 C code v false s s' a := by
  change policyKernel
    (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false))
    (fun x a ↦ (sparseTargetPMF hd zeta code j x a).toReal) s s' = _
  rw [embed_policyKernel_eq]
  unfold finitePolicyKernel
  simp only [sparseFinite]
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _)]
  simp_rw [sparse_kernel_state_marginal hd t0 C ht0 hC code v false,
    sparse_target_pmf_toReal hd zeta hzeta code]

end CausalSmith.Stat.PomdpPolicyclassRegret
