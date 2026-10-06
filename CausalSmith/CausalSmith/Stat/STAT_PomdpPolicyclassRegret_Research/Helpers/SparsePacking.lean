module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Basic
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteEncoding
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BinaryCode
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Sparse-context common-kernel packing experiment

The finite-symbol kernel below is shared across all candidates within one
environment. The construction specializes the sibling finite-path PMF device
to a context coordinate and a signed hidden-depth coordinate.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @env: S3
variable {M : Nat} (Q : Nat) (v : Fin M)
/-- [the hdepth quantity](goal) is defined from [the hidden-depth scale](hyp:Q). -/

def hdepth (Q : Nat) : Nat := max 2 Q
  -- @realizes hdepth(maximum of two and Q) @realizes Qdepth(depth argument)

-- @node: hdepth_ratio_lower
/-- For [the hidden-depth scale](hyp:Q) and [the hidden-depth scale assumption](hyp:hQ), this
establishes [the hdepth ratio lower result](goal). -/
lemma hdepth_ratio_lower (Q : Nat) (hQ : 1 ≤ Q) :
    (1 / 2 : ℝ) ≤ (Q : ℝ) / hdepth Q := by
  have hhpos : 0 < hdepth Q := by simp [hdepth]
  have hhbound : hdepth Q ≤ 2 * Q := by simp [hdepth]; omega
  have hhpos' : (0 : ℝ) < hdepth Q := by exact_mod_cast hhpos
  have hhbound' : (hdepth Q : ℝ) ≤ 2 * Q := by exact_mod_cast hhbound
  apply (le_div_iff₀ hhpos').2
  linarith
/-- [the context index object](goal) is defined from [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd), and
[the observed state](hyp:x). -/


def contextIndex {d Q : Nat} (hd : 0 < d)
    (x : Fin (d * hdepth Q)) : Fin d :=
  ⟨x.val / hdepth Q, by
    have hh : 0 < hdepth Q := by simp [hdepth]
    exact (Nat.div_lt_iff_lt_mul hh).2 x.isLt⟩
/-- [the exceptional context predicate](goal) is defined from
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), and [the observed state](hyp:x). -/

def exceptionalContext {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) : Prop :=
  x.val % hdepth Q = if code v (contextIndex hd x) then 1 else 0
  -- @realizes E_v(sparse code-selected context slots)

/-- Every code coordinate has a context at the slot selected by a word. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), and [the i](hyp:i), this establishes
[the sparse exceptional context witness result](goal). -/
-- @node: sparse_exceptional_context_witness
lemma sparse_exceptional_context_witness {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M) (i : Fin d) :
    ∃ x : Fin (d * hdepth Q),
      contextIndex hd x = i ∧ exceptionalContext hd code v x := by
  let r : Nat := if code v i then 1 else 0
  have hr : r < hdepth Q := by
    dsimp [r]
    split_ifs <;> simp [hdepth]
  let x : Fin (d * hdepth Q) :=
    ⟨i.val * hdepth Q + r, by
      have hi := i.isLt
      have hh : 0 < hdepth Q := by simp [hdepth]
      have hmul : i.val * hdepth Q + hdepth Q ≤ d * hdepth Q := by
        simpa [add_mul] using
          (Nat.mul_le_mul_right (hdepth Q) (Nat.succ_le_of_lt hi))
      omega⟩
  refine ⟨x, ?_, ?_⟩
  · apply Fin.ext
    dsimp [x, contextIndex]
    rw [add_comm, Nat.add_mul_div_right _ _ (by simp [hdepth])]
    simp [Nat.div_eq_of_lt hr]
  · dsimp [exceptionalContext, x]
    rw [show contextIndex hd x = i by
      apply Fin.ext
      dsimp [x, contextIndex]
      rw [add_comm, Nat.add_mul_div_right _ _ (by simp [hdepth])]
      simp [Nat.div_eq_of_lt hr]]
    dsimp [r]
    simpa [Nat.mul_add_mod] using Nat.mod_eq_of_lt hr

/-- A differing code bit produces a context exceptional for exactly one word. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed word](hyp:w),
[the i](hyp:i), and [the bit assumption](hyp:hbit), this establishes
[the sparse exceptional context separates result](goal). -/
-- @node: sparse_exceptional_context_separates
lemma sparse_exceptional_context_separates {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v w : Fin M) (i : Fin d)
    (hbit : code v i ≠ code w i) :
    ∃ x : Fin (d * hdepth Q),
      exceptionalContext hd code v x ∧ ¬ exceptionalContext hd code w x := by
  obtain ⟨x, hxidx, hxv⟩ := sparse_exceptional_context_witness hd code v i
  refine ⟨x, hxv, ?_⟩
  intro hxw
  have hslots : (if code v i then 1 else 0 : Nat) =
      (if code w i then 1 else 0 : Nat) := by
    simpa only [exceptionalContext, hxidx] using hxv.symm.trans hxw
  cases hv : code v i <;> cases hw : code w i <;>
    simp_all

/-- Distinct words in a separated code have distinct exceptional context sets. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the code assumption](hyp:hCode), [the codeword index](hyp:v),
[the observed word](hyp:w), and [the vw assumption](hyp:hvw), this establishes
[the sparse exceptional context separates code result](goal). -/
-- @node: sparse_exceptional_context_separates_code
lemma sparse_exceptional_context_separates_code {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code)
    (v w : Fin M) (hvw : v ≠ w) :
    ∃ x : Fin (d * hdepth Q),
      exceptionalContext hd code v x ∧ ¬ exceptionalContext hd code w x := by
  have hdiff : ∃ i : Fin d, code v i ≠ code w i := by
    by_contra h
    push Not at h
    apply hvw
    apply hCode.1
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hdiff
  exact sparse_exceptional_context_separates hd code v w i hi
/-- [the retention indicator quantity](goal) is defined from
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x), and
[the action](hyp:a). -/

noncomputable def retentionIndicator {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (a : Bool) : ℝ :=
  by classical exact if a = true ∨ exceptionalContext hd code v x then 1 else 0
/-- [the hidden depth quantity](goal) is defined from [the hidden-depth scale](hyp:Q) and
[the stated assumption](hyp:h). -/

def hiddenDepth (Q : Nat) (h : Fin (2 * (Q + 1))) : Nat := h.val / 2
/-- [the hidden sign object](goal) is defined from [the hidden-depth scale](hyp:Q) and
[the stated assumption](hyp:h). -/

def hiddenSign (Q : Nat) (h : Fin (2 * (Q + 1))) : Bool :=
  decide (h.val % 2 = 1)
/-- [the sign value quantity](goal) is defined from [the observed prefix](hyp:u). -/

def signValue (u : Bool) : ℝ := if u then 1 else -1
/-- [the sparse epsilon quantity](goal) is defined from [the latent-overlap radius](hyp:C). -/

noncomputable def sparseEpsilon (C : ℝ) : ℝ := overlapRadius C / 2
  -- @realizes epsilon(q/2)
/-- [the sparse signal quantity](goal) is defined from [the mixing scale](hyp:t0). -/

noncomputable def sparseSignal (t0 : ℝ) : ℝ := (1 - mixingAlpha t0) / 4
  -- @realizes c0((1-alpha)/4)
/-- [the reset sign weight quantity](goal) is defined from [the latent-overlap radius](hyp:C),
[the fair-reference flag](hyp:fair), and [the observed prefix](hyp:u). -/

noncomputable def resetSignWeight (C : ℝ) (fair u : Bool) : ℝ :=
  (1 + signValue u * (if fair then 0 else sparseEpsilon C)) / 2
/-- [the sparse behavior weight quantity](goal) is defined from
[the policy-overlap scale](hyp:zeta) and [the action](hyp:a). -/

noncomputable def sparseBehaviorWeight (zeta : ℝ) (a : Bool) : ℝ :=
  if a then (policyFactor zeta)⁻¹ else 1 - (policyFactor zeta)⁻¹
/-- [the sparse target weight quantity](goal) is defined from
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the binary code](hyp:code), [the codeword index](hyp:v),
[the observed state](hyp:x), and [the action](hyp:a). -/

noncomputable def sparseTargetWeight {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (a : Bool) : ℝ :=
  by classical exact if exceptionalContext hd code v x then sparseBehaviorWeight zeta a
    else if a then 1 else 0

/-- The raw target action weights distinguish the codewords. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), and [the code assumption](hyp:hCode), this establishes
[the sparse target weight injective result](goal). -/
-- @node: sparse_target_weight_injective
lemma sparse_target_weight_injective {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (hzeta : 0 < zeta)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) :
    Function.Injective (fun v : Fin M ↦ sparseTargetWeight (Q := Q) hd zeta code v) := by
  intro v w heq
  by_contra hvw
  obtain ⟨x, hxv, hxw⟩ :=
    sparse_exceptional_context_separates_code (Q := Q) hd code hCode v w hvw
  have hcell := congrArg (fun f ↦ f x false) heq
  simp only [sparseTargetWeight, hxv, hxw, ↓reduceIte,
    sparseBehaviorWeight] at hcell
  simp at hcell
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hzeta
  have hinv : (policyFactor zeta)⁻¹ < 1 :=
    (inv_lt_one₀ (by linarith)).mpr hL
  linarith
/-- [the sparse state weight quantity](goal) is defined from
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the codeword index](hyp:v), [the fair-reference flag](hyp:fair), [the state](hyp:s),
[the successor state](hyp:s'), and [the action](hyp:a). -/

noncomputable def sparseStateWeight {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (fair : Bool) (s s' : JointState (d * hdepth Q) (2 * (Q + 1)))
    (a : Bool) : ℝ :=
  let j := hiddenDepth Q s.2
  let j' := hiddenDepth Q s'.2
  let u := hiddenSign Q s.2
  let u' := hiddenSign Q s'.2
  let newContext := ((d * hdepth Q : Nat) : ℝ)⁻¹
  let reset := resetSignWeight C fair u'
  newContext *
    if j = Q then
      if j' = 0 then reset else 0
    else
      (if j' = 0 then (1 - mixingAlpha t0) * reset else 0) +
        (if j' = j + 1 then mixingAlpha t0 *
          (if retentionIndicator hd code v s.1 a = 1 then
            if u' = u then 1 else 0 else 1 / 2) else 0)
  -- @realizes K_v(common environment kernel, reset and retention transitions)
/-- [the sparse reward weight quantity](goal) is defined from [the mixing scale](hyp:t0),
[the hidden-depth scale](hyp:Q), [the stated assumption](hyp:h), and [the reward symbol](hyp:r). -/

noncomputable def sparseRewardWeight (t0 : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (r : Fin 2) : ℝ :=
  (1 + (if r = 0 then -1 else 1 : ℝ) * sparseSignal t0 *
    signValue (hiddenSign Q h) * (if hiddenDepth Q h = Q then 1 else 0)) / 2
/-- [the sparse kernel object](goal) is defined from [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
and [the fair-reference flag](hyp:fair). -/

noncomputable def sparseKernel {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (fair : Bool) : JointState (d * hdepth Q) (2 * (Q + 1)) → Bool →
      PMF (Fin 2 × JointState (d * hdepth Q) (2 * (Q + 1))) :=
  by
    letI : NeZero (d * hdepth Q) := ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
    exact fun s a ↦ pmfOfRealWeight fun p ↦
      (if fair then (1 / 2 : ℝ) else sparseRewardWeight t0 Q s.2 p.1) *
        sparseStateWeight hd t0 C code v fair s p.2 a
/-- [the sparse behavior probability mass function object](goal) is defined from
[the policy-overlap scale](hyp:zeta), [the code dimension](hyp:d), and
[the hidden-depth scale](hyp:Q). -/

noncomputable def sparseBehaviorPMF (zeta : ℝ) (d Q : Nat) :
    Fin (d * hdepth Q) → PMF Bool :=
  fun _ ↦ pmfOfRealWeight (sparseBehaviorWeight zeta)
/-- [the sparse target probability mass function object](goal) is defined from
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the binary code](hyp:code), and
[the codeword index](hyp:v). -/

noncomputable def sparseTargetPMF {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) :
    Fin (d * hdepth Q) → PMF Bool :=
  fun x ↦ pmfOfRealWeight (sparseTargetWeight hd zeta code v x)

/-- The target action weights already sum to one, so PMF normalization is inert. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x), and
[the action](hyp:a), this establishes
[the sparse target probability mass function to real result](goal). -/
-- @node: sparse_target_pmf_toReal
lemma sparse_target_pmf_toReal {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (hzeta : 0 < zeta)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (a : Bool) :
    (sparseTargetPMF hd zeta code v x a).toReal =
      sparseTargetWeight hd zeta code v x a := by
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  have hnonneg : ∀ b : Bool, 0 ≤ sparseTargetWeight hd zeta code v x b := by
    intro b
    classical
    by_cases hx : exceptionalContext hd code v x
    · cases b <;> simp [sparseTargetWeight, sparseBehaviorWeight, hx] <;> linarith
    · cases b <;> simp [sparseTargetWeight, hx]
  have hsum : ∑ b : Bool, sparseTargetWeight hd zeta code v x b = 1 := by
    classical
    by_cases hx : exceptionalContext hd code v x
    · simp [sparseTargetWeight, sparseBehaviorWeight, hx]
    · simp [sparseTargetWeight, hx]
  change (pmfOfRealWeight (sparseTargetWeight hd zeta code v x) a).toReal = _
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hnonneg hsum a,
    ENNReal.toReal_ofReal (hnonneg a)]

/-- Normalized target policies remain distinct across codewords. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), and [the code assumption](hyp:hCode), this establishes
[the sparse target probability mass function injective result](goal). -/
-- @node: sparse_target_pmf_injective
lemma sparse_target_pmf_injective {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (hzeta : 0 < zeta)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) :
    Function.Injective (fun v : Fin M ↦
      fun x a ↦ (sparseTargetPMF (Q := Q) hd zeta code v x a).toReal) := by
  intro v w heq
  apply sparse_target_weight_injective (Q := Q) hd zeta hzeta code hCode
  funext x a
  have hcell := congrArg (fun f ↦ f x a) heq
  simpa [sparse_target_pmf_toReal hd zeta hzeta code] using hcell
/-- [the sparse transition quantity](goal) is defined from [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the state](hyp:s), and [the successor state](hyp:s'). -/

noncomputable def sparseTransition {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (fair : Bool) (s s' : JointState (d * hdepth Q) (2 * (Q + 1))) : ℝ :=
  ∑ a : Bool, (sparseBehaviorPMF zeta d Q s.1 a).toReal *
    ∑ r : Fin 2, (sparseKernel hd t0 C code v fair s a (r, s')).toReal
/-- [the sparse init object](goal) is defined from [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), and
[the fair-reference flag](hyp:fair). -/

noncomputable def sparseInit {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (fair : Bool) : PMF (JointState (d * hdepth Q) (2 * (Q + 1))) :=
  by
    letI : NeZero (d * hdepth Q) := ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
    exact pmfOfRealWeight (stationaryLaw (sparseTransition hd t0 zeta C code v fair))
/-- [the sparse finite object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
and [the fair-reference flag](hyp:fair). -/

noncomputable def sparseFinite {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (fair : Bool) : FiniteRewardModel T (d * hdepth Q) (2 * (Q + 1)) 2 := by
  letI : NeZero (d * hdepth Q) := ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
  letI : NeZero (2 * (Q + 1)) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
  let K := sparseKernel (Q := Q) hd t0 C code v fair
  let init := sparseInit (Q := Q) hd t0 zeta C code v fair
  let b := sparseBehaviorPMF zeta d Q
  exact {
    kernel := K
    rew := fun r ↦ if r = 0 then 0 else 1
    rew_mem := by intro r; fin_cases r <;> norm_num
    init := init
    b := b
    e := sparseTargetPMF hd zeta code v
    law := finitePathPMF K init b
    law_generated := finitePathPMF_apply K init b }
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), the state, and
the action, this establishes [the sparse reward unit result](goal). -/

lemma sparse_reward_unit {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) :
    ∀ s a, (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).K s a
      ((Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ) = 0 := by
  intro s a
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  change ((F.kernel s a).map (fun p ↦ (F.rew p.1, p.2))).toMeasure
    ((Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ) = 0
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _)
    (by measurability)]
  have hpre : (fun p : Fin 2 × JointState (d * hdepth Q) (2 * (Q + 1)) ↦
      (F.rew p.1, p.2)) ⁻¹'
      ((Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ) = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_compl_iff,
      Set.mem_Icc, Set.mem_univ, and_true, Set.mem_empty_iff_false, iff_false]
    have hrew : F.rew p.1 = 0 ∨ F.rew p.1 = 1 := by
      have hp : p.1 = 0 ∨ p.1 = 1 := by omega
      rcases hp with hp | hp <;> simp [hp, F, sparseFinite]
    exact not_not.mpr (hrew.elim (by intro h; simp [h]) (by intro h; simp [h]))
  rw [hpre, measure_empty]
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), and [the codeword index](hyp:v), this establishes
[the sparse list kernel law result](goal). -/

lemma sparse_list_kernel_law {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) :
    PomdpKernelLaw
      ({ K := (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).K
         b := (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).b
         e := (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).b
         init := (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).init
         law := (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).law
         law_isProbability := (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)).law_isProbability } :
       RawPomdpExperiment T (d * hdepth Q) (2 * (Q + 1))) := by
  exact embed_pomdpKernelLaw (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)

-- @node: def:sparse-packing
/-- [the sparse packing experiment object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v). -/
noncomputable def sparsePackingExperiment (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool)
    (hCode : CodeSeparated code) (v : Fin M) :
    ModelIndex T M :=
  let F := sparseFinite (T := T) hd t0 zeta C code v false
  let raw := embed F
  let Mx : ListPomdpExperiment T M (d * hdepth Q) (2 * (Q + 1)) := {
    K := raw.K
    b := raw.b
    E := fun j x a ↦ (sparseTargetPMF hd zeta code j x a).toReal
    init := raw.init
    law := raw.law
    law_isProbability := raw.law_isProbability }
  { list_size := hM
    nX := d * hdepth Q
    nH := 2 * (Q + 1)
    Mx := Mx
    target_policies := by
      intro j x
      constructor
      · intro a; exact ENNReal.toReal_nonneg
      · change (∑ a : Bool, (sparseTargetPMF (Q := Q) hd zeta code j x a).toReal) = 1
        rw [← ENNReal.toReal_sum (fun a _ ↦ PMF.apply_ne_top _ a)]
        have hsum : (∑ a : Bool, sparseTargetPMF (Q := Q) hd zeta code j x a) = 1 := by
          simpa only [tsum_fintype] using ( sparseTargetPMF (Q := Q) hd zeta code j x).tsum_coe
        rw [hsum, ENNReal.toReal_one]
    kernel_law := by simpa [Mx, ListPomdpExperiment.toRawB, F, raw] using
      sparse_list_kernel_law (T := T) (Q := Q) hd t0 zeta C code v
    reward_unit := by simpa [Mx, F, raw] using
      sparse_reward_unit (T := T) (Q := Q) hd t0 zeta C code v }
  -- @realizes K_v(common kernel for every listed policy) @realizes Elist(same revealed policy list across environments)

/-- The revealed list in the sparse experiment has no repeated policy. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), [the code assumption](hyp:hCode), and [the codeword index](hyp:v),
this establishes [the sparse packing supplied list result](goal). -/
-- @node: sparse_packing_supplied_list
lemma sparse_packing_supplied_list (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (hzeta : 0 < zeta)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    SuppliedList (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v) := by
  simpa [SuppliedList, sparsePackingExperiment] using
    sparse_target_pmf_injective (Q := Q) hd zeta hzeta code hCode
/-- [the sparse reference law object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), and
[the binary code](hyp:code). -/

noncomputable def sparseReferenceLaw (T M d Q : Nat) (hd : 0 < d)
    (hM : 0 < M) (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) :
    Measure (ObsView T (d * hdepth Q)) :=
  obsLaw (embed (sparseFinite (T := T) hd t0 zeta C code ⟨0, hM⟩ true))
  -- @realizes P0(fair-reward observed reference law)

/-- The exponential step in the sparse packing value separation (23). For
[the hidden-depth scale](hyp:Q), [the policy](hyp:p), [the lambda](hyp:lambda),
[the lambda0 assumption](hyp:hlambda0), [the lambda1 assumption](hyp:hlambda1), and
[the value gap assumption](hyp:hgap), this establishes [the sparse gap power result](goal). -/
-- @node: sparse_gap_power
lemma sparse_gap_power (Q : Nat) (p lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hgap : (1 - p) / 8 ≤ (Q : ℝ) * (1 - lambda)) :
    1 - Real.exp (-(1 - p) / 8) ≤ 1 - lambda ^ Q := by
  have hpow : lambda ^ Q ≤ Real.exp (-(Q : ℝ) * (1 - lambda)) := by
    calc
      lambda ^ Q = (1 - (1 - lambda)) ^ Q := by ring
      _ ≤ (Real.exp (-(1 - lambda))) ^ Q :=
        pow_le_pow_left₀ (by nlinarith)
          (Real.one_sub_le_exp_neg (1 - lambda)) Q
      _ = Real.exp ((Q : ℝ) * (-(1 - lambda))) :=
        (Real.exp_nat_mul (-(1 - lambda)) Q).symm
      _ = Real.exp (-(Q : ℝ) * (1 - lambda)) := by congr 1 <;> ring
  have hexp : Real.exp (-(Q : ℝ) * (1 - lambda)) ≤
      Real.exp (-(1 - p) / 8) := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith

/-- Code separation and the depth-to-width ratio give the value-gap factor. For
[the hidden-depth scale](hyp:Q), [the code dimension](hyp:d), [the d](hyp:D),
[the policy](hyp:p), [the hidden-depth scale assumption](hyp:hQ),
[the code dimension assumption](hyp:hd), [the p0 assumption](hyp:hp0),
[the p1 assumption](hyp:hp1), [the dlo assumption](hyp:hDlo), and
[the dhi assumption](hyp:hDhi), this establishes [the sparse code gap power result](goal). -/
-- @node: sparse_code_gap_power
lemma sparse_code_gap_power (Q d D : Nat) (p : ℝ)
    (hQ : 1 ≤ Q) (hd : 0 < d) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hDlo : (d : ℝ) / 4 ≤ D) (hDhi : D ≤ d) :
    1 - Real.exp (-(1 - p) / 8) ≤
      1 - (1 - (1 - p) * (D : ℝ) / ((d : ℝ) * hdepth Q)) ^ Q := by
  let lambda : ℝ := 1 - (1 - p) * (D : ℝ) / ((d : ℝ) * hdepth Q)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hhpos : (0 : ℝ) < hdepth Q := by
    exact_mod_cast (show 0 < hdepth Q by simp [hdepth])
  have hDhi' : (D : ℝ) ≤ d := by exact_mod_cast hDhi
  have hden : 0 < (d : ℝ) * hdepth Q := mul_pos hdpos hhpos
  have hprod0 : 0 ≤ (1 - p) * (D : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hprodhi : (1 - p) * (D : ℝ) ≤ (d : ℝ) * hdepth Q := by
    have hh : (2 : ℝ) ≤ hdepth Q := by
      exact_mod_cast (show 2 ≤ hdepth Q by simp [hdepth])
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hDhi')]
  have hlambda0 : 0 ≤ lambda := by
    dsimp [lambda]
    exact sub_nonneg.mpr ((div_le_one hden).mpr hprodhi)
  have hlambda1 : lambda ≤ 1 := by
    dsimp [lambda]
    exact sub_le_self _ (div_nonneg hprod0 (le_of_lt hden))
  have hgap : (1 - p) / 8 ≤ (Q : ℝ) * (1 - lambda) := by
    have hratio := hdepth_ratio_lower Q hQ
    have hwidth : (hdepth Q : ℝ) ≤ 2 * Q := by
      have h := (le_div_iff₀ hhpos).mp hratio
      linarith
    have hdim : (d : ℝ) ≤ 4 * D := by linarith [hDlo]
    have hsize : (d : ℝ) * hdepth Q ≤ 8 * (Q : ℝ) * D := by
      calc
        (d : ℝ) * hdepth Q ≤ (4 * D) * hdepth Q :=
          mul_le_mul_of_nonneg_right hdim (le_of_lt hhpos)
        _ ≤ (4 * D) * (2 * Q) :=
          mul_le_mul_of_nonneg_left hwidth (by positivity)
        _ = 8 * (Q : ℝ) * D := by ring
    have hgap' : (1 - p) / 8 ≤
        (Q : ℝ) * ((1 - p) * (D : ℝ) / ((d : ℝ) * hdepth Q)) := by
      have hmain : (1 - p) / 8 ≤
          ((Q : ℝ) * ((1 - p) * D)) / ((d : ℝ) * hdepth Q) := by
        apply (le_div_iff₀ hden).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hsize)]
      convert hmain using 1 <;> ring
    convert hgap' using 1 <;> dsimp [lambda] <;> ring
  exact sparse_gap_power Q p lambda hlambda0 hlambda1 hgap

/-- The separated binary code supplies the terminal value-gap estimate. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), [the observed word](hyp:w),
[the vw assumption](hyp:hvw), [the hidden-depth scale](hyp:Q),
[the hidden-depth scale assumption](hyp:hQ), [the code dimension assumption](hyp:hd),
[the policy](hyp:p), [the p0 assumption](hyp:hp0), and [the p1 assumption](hyp:hp1), this
establishes [the sparse separated code gap result](goal). -/
-- @node: sparse_separated_code_gap
lemma sparse_separated_code_gap {M d : Nat}
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code)
    (v w : Fin M) (hvw : v ≠ w) (Q : Nat) (hQ : 1 ≤ Q)
    (hd : 0 < d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - Real.exp (-(1 - p) / 8) ≤
      1 - (1 - (1 - p) * (hammingDistance code v w : ℝ) /
        ((d : ℝ) * hdepth Q)) ^ Q := by
  apply sparse_code_gap_power Q d (hammingDistance code v w) p hQ hd hp0 hp1
  · exact hCode.2 v w hvw
  · unfold hammingDistance
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun i : Fin d ↦ code v i ≠ code w i) Finset.univ)

/-- The context dilution factor in the KL calculation costs at most `exp (L - 1)`. For
[the hidden-depth scale](hyp:Q), [the action-overlap factor](hyp:L), and
[the action-overlap factor assumption](hyp:hL), this establishes
[the sparse retention pow bound result](goal). -/
-- @node: sparse_retention_pow_bound
lemma sparse_retention_pow_bound (Q : Nat) (L : ℝ) (hL : 1 ≤ L) :
    (L⁻¹ + (1 - L⁻¹) / (hdepth Q : ℝ)) ^ Q ≤
      Real.exp (L - 1) * (L⁻¹) ^ Q := by
  have hLpos : 0 < L := by linarith
  have hhpos : (0 : ℝ) < hdepth Q := by
    exact_mod_cast (show 0 < hdepth Q by simp [hdepth])
  have hQh : (Q : ℝ) ≤ hdepth Q := by
    exact_mod_cast (show Q ≤ hdepth Q by simp [hdepth])
  have hfac : L⁻¹ + (1 - L⁻¹) / (hdepth Q : ℝ) =
      L⁻¹ * (1 + (L - 1) / (hdepth Q : ℝ)) := by
    field_simp
  have hx : 0 ≤ (L - 1) / (hdepth Q : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hhpos)
  have hexp : (1 + (L - 1) / (hdepth Q : ℝ)) ^ Q ≤
      Real.exp ((Q : ℝ) * ((L - 1) / (hdepth Q : ℝ))) := by
    calc
      _ ≤ (Real.exp ((L - 1) / (hdepth Q : ℝ))) ^ Q := by
        apply pow_le_pow_left₀ (by linarith [hx])
        simpa [add_comm] using Real.add_one_le_exp ((L - 1) / (hdepth Q : ℝ))
      _ = _ := by rw [← Real.exp_nat_mul]
  have harg : (Q : ℝ) * ((L - 1) / (hdepth Q : ℝ)) ≤ L - 1 := by
    calc
      (Q : ℝ) * ((L - 1) / (hdepth Q : ℝ)) = Q * (L - 1) / hdepth Q := by ring
      _ ≤ L - 1 := (div_le_iff₀ hhpos).mpr (by
        nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hQh)])
  rw [hfac, mul_pow]
  have hbound := (hexp.trans (Real.exp_le_exp.mpr harg))
  nlinarith [pow_nonneg (inv_nonneg.mpr (le_of_lt hLpos)) Q]

/-- The stationary sign weights of a target with greater retention remain within the required
overlap radius of the behavior sign weights. For [the latent-overlap radius](hyp:C),
[the policy](hyp:p), [the lambda](hyp:lambda), [the reward symbol](hyp:r),
[the latent-overlap radius assumption](hyp:hC), [the policy assumption](hyp:hp),
[the plambda assumption](hyp:hplambda), [the lambda assumption](hyp:hlambda), and
[the observed prefix](hyp:u), this establishes [the sparse sign weight overlap result](goal). -/
-- @node: sparse_sign_weight_overlap
lemma sparse_sign_weight_overlap (C p lambda : ℝ) (r : Nat)
    (hC : 1 < C) (hp : 0 ≤ p) (hplambda : p ≤ lambda)
    (hlambda : lambda ≤ 1) (u : Bool) :
    1 + signValue u * sparseEpsilon C * lambda ^ r ≤
      C * (1 + signValue u * sparseEpsilon C * p ^ r) := by
  have hCpos : 0 < C := by linarith
  have heps0 : 0 ≤ sparseEpsilon C := by
    change 0 ≤ ((C - 1) / C) / 2
    exact div_nonneg (div_nonneg (by linarith) hCpos.le) (by norm_num)
  have heps_half : sparseEpsilon C ≤ 1 / 2 := by
    change ((C - 1) / C) / 2 ≤ 1 / 2
    have hq : (C - 1) / C ≤ 1 := (div_le_one hCpos).mpr (by linarith)
    linarith
  have heps_C : sparseEpsilon C ≤ C - 1 := by
    change ((C - 1) / C) / 2 ≤ C - 1
    have hq : (C - 1) / C ≤ C - 1 := div_le_self (by linarith) hC.le
    linarith
  have hp0 : 0 ≤ p ^ r := pow_nonneg hp _
  have hp1 : p ^ r ≤ 1 := pow_le_one₀ hp (hplambda.trans hlambda)
  have hlambda0 : 0 ≤ lambda := le_trans hp hplambda
  have hlambda1 : lambda ^ r ≤ 1 := pow_le_one₀ hlambda0 hlambda
  have hpow : p ^ r ≤ lambda ^ r := pow_le_pow_left₀ hp hplambda r
  cases u
  · simp only [signValue, Bool.false_eq_true, ↓reduceIte]
    have hbase : 0 ≤ 1 - sparseEpsilon C * p ^ r := by
      nlinarith [mul_nonneg heps0 hp0, mul_le_mul_of_nonneg_left hp1 heps0]
    have horder : 1 - sparseEpsilon C * lambda ^ r ≤
        1 - sparseEpsilon C * p ^ r := by
      nlinarith [mul_le_mul_of_nonneg_left hpow heps0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC.le) hbase]
  · simp only [signValue, ↓reduceIte, one_mul]
    have hbase : 0 ≤ 1 + sparseEpsilon C * p ^ r := by positivity
    have htarget : 1 + sparseEpsilon C * lambda ^ r ≤ C := by
      nlinarith [mul_le_mul_of_nonneg_left hlambda1 heps0]
    nlinarith [mul_nonneg hCpos.le (mul_nonneg heps0 hp0)]

end CausalSmith.Stat.PomdpPolicyclassRegret
