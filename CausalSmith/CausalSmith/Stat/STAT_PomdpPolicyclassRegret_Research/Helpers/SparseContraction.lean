module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseKernelFacts
public import Causalean.Mathlib.Probability.Certified.FiniteKernel

/-! # Common-reset contraction of the sparse packing

The reset distribution minorizes every action-conditioned row, so averaging
under behavior or any listed policy preserves the same contraction factor.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Every sparse row contains the common fresh-context, depth-zero reset law with mass at least
one minus alpha. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the state](hyp:s), [the successor state](hyp:s'), and [the action](hyp:a), this establishes
[the sparse state weight reset minorization result](goal). -/
-- @node: sparse_state_weight_reset_minorization
lemma sparse_state_weight_reset_minorization {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s s' : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    (1 - mixingAlpha t0) *
      (((d * hdepth Q : Nat) : ℝ)⁻¹ *
        (if hiddenDepth Q s'.2 = 0 then
          resetSignWeight C fair (hiddenSign Q s'.2) else 0)) ≤
      sparseStateWeight hd t0 C code v fair s s' a := by
  have hα0 := (mixingAlpha_pos ht0).le
  have hα1 := (mixingAlpha_lt_one ht0).le
  have hr := sparse_reset_sign_weight_nonneg C hC fair (hiddenSign Q s'.2)
  have hn : 0 ≤ ((d * hdepth Q : Nat) : ℝ)⁻¹ := by positivity
  unfold sparseStateWeight
  dsimp only
  split_ifs <;> nlinarith [mul_nonneg hn hr,
    mul_nonneg hn hα0, mul_nonneg (mul_nonneg hn hα0) hr]

/-- The fresh-context reset law is a probability vector. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the fair-reference flag](hyp:fair), this establishes
[the sparse reset probability vector result](goal). -/
-- @node: sparse_reset_probability_vector
lemma sparse_reset_probability_vector {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool) :
    ProbabilityVector (fun s' : JointState (d * hdepth Q) (2 * (Q + 1)) ↦
      ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        (if hiddenDepth Q s'.2 = 0 then
          resetSignWeight C fair (hiddenSign Q s'.2) else 0)) := by
  let s : JointState (d * hdepth Q) (2 * (Q + 1)) :=
    (⟨0, Nat.mul_pos hd (by simp [hdepth])⟩, ⟨2 * Q, by omega⟩)
  have hs : hiddenDepth Q s.2 = Q := by simp [s, hiddenDepth]
  constructor
  · intro s'
    dsimp only
    split_ifs
    · exact mul_nonneg (by positivity)
        (sparse_reset_sign_weight_nonneg C hC fair _)
    · simp
  · simpa only [sparseStateWeight, hs, if_pos] using
      sparse_state_weight_sum hd t0 C code v fair s false

/-- Averaging the sparse rows under any probability policy preserves the common reset
minorization and hence contracts total variation by alpha. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the policy](hyp:p), [the policy assumption](hyp:hp), the initial distribution, and
the nu', this establishes [the sparse policy weight contraction result](goal). -/
-- @node: sparse_policy_weight_contraction
lemma sparse_policy_weight_contraction {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p) :
    ∀ nu nu', ProbabilityVector nu → ProbabilityVector nu' →
      tvNorm (applyKernel nu (fun s s' ↦ ∑ a : Bool,
          p s.1 a * sparseStateWeight hd t0 C code v fair s s' a) -
        applyKernel nu' (fun s s' ↦ ∑ a : Bool,
          p s.1 a * sparseStateWeight hd t0 C code v fair s s' a)) ≤
        mixingAlpha t0 * tvNorm (nu - nu') := by
  classical
  let P := fun s s' ↦ ∑ a : Bool,
    p s.1 a * sparseStateWeight hd t0 C code v fair s s' a
  let R := fun s' : JointState (d * hdepth Q) (2 * (Q + 1)) ↦
    ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      (if hiddenDepth Q s'.2 = 0 then
        resetSignWeight C fair (hiddenSign Q s'.2) else 0)
  have hP :
      Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStochasticMatrix P := by
    constructor
    · intro s s'
      exact Finset.sum_nonneg fun a _ ↦ mul_nonneg ((hp s.1).1 a)
        (sparse_state_weight_nonneg hd t0 C ht0 hC code v fair s s' a)
    · intro s
      dsimp [P]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sparse_state_weight_sum, mul_one]
      exact (hp s.1).2
  have hminor : Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Minorizes
      P (1 - mixingAlpha t0) R := by
    refine ⟨sparse_reset_probability_vector hd t0 C hC code v fair,
      sub_nonneg.mpr (mixingAlpha_lt_one ht0).le,
      by linarith [mixingAlpha_pos ht0], ?_⟩
    intro s s'
    calc
      (1 - mixingAlpha t0) * R s' =
          ∑ a : Bool, p s.1 a * ((1 - mixingAlpha t0) * R s') := by
        rw [← Finset.sum_mul, (hp s.1).2, one_mul]
      _ ≤ P s s' := Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_left
          (sparse_state_weight_reset_minorization hd t0 C ht0 hC code v fair s s' a)
          ((hp s.1).1 a)
  have hc :=
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.contractsL1_of_minorization
      hP hminor
  intro nu nu' hnu hnu'
  have hh := hc nu nu' hnu hnu'
  dsimp [Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.l1Distance,
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovStep,
    Matrix.vecMul, dotProduct] at hh
  dsimp [P] at hh
  dsimp [tvNorm, applyKernel, P]
  nlinarith only [hh]

/-- Decoding rewards leaves the explicit action-averaged sparse transition matrix unchanged for
any policy. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the dim assumption](hyp:hDim),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the code assumption](hyp:hCode), [the codeword index](hyp:v),
[the policy](hyp:p), [the state](hyp:s), and [the successor state](hyp:s'), this establishes
[the sparse packing policy kernel weight result](goal). -/
-- @node: sparse_packing_policy_kernel_weight
lemma sparse_packing_policy_kernel_weight (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M)
    (p : Fin (d * hdepth Q) → Bool → ℝ)
    (s s' : JointState (d * hdepth Q) (2 * (Q + 1))) :
    listPolicyKernel
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v)
      p s s' = ∑ a : Bool, p s.1 a *
        sparseStateWeight hd t0 C code v false s s' a := by
  change policyKernel
    (embed (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)) p s s' = _
  unfold policyKernel
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  have hmarg : (embed F).K s a (Prod.snd ⁻¹' {s'}) =
      ∑ r : Fin 2, F.kernel s a (r, s') := by
    change ((F.kernel s a).map (fun q ↦ (F.rew q.1, q.2))).toMeasure
      (Prod.snd ⁻¹' {s'}) = _
    rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _)
      ((MeasurableSet.singleton s').preimage measurable_snd),
      PMF.toMeasure_apply_fintype, Fintype.sum_prod_type]
    classical
    simp only [Set.indicator_apply]
    simp
  change ((embed F).K s a (Prod.snd ⁻¹' {s'})).toReal = _
  rw [hmarg, ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _)]
  exact sparse_kernel_state_marginal hd t0 C ht0 hC code v false s s' a

/-- Behavior and all listed targets share the alpha contraction factor from their common reset
distribution. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the dim assumption](hyp:hDim),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse packing uniform contraction result](goal). -/
-- @node: sparse_packing_uniform_contraction
lemma sparse_packing_uniform_contraction (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    ListUniformContraction
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v)
      (mixingAlpha t0) := by
  intro j p hp
  have hpvec : PolicyVector p := by
    rcases hp with rfl | rfl
    · change PolicyVector (fun x a ↦ (sparseBehaviorPMF zeta d Q x a).toReal)
      intro x
      constructor
      · intro a; positivity
      · simp_rw [sparse_behavior_pmf_toReal zeta hzeta]
        simp [sparseBehaviorWeight]
    · exact (sparse_packing_action_overlap T M d Q hd hDim hM
        t0 zeta C hzeta code hCode v j).1
  change ∀ nu nu', ProbabilityVector nu → ProbabilityVector nu' →
    tvNorm (applyKernel nu
        (listPolicyKernel (sparsePackingExperiment T M d Q hd hDim hM
          t0 zeta C code hCode v) p) -
      applyKernel nu'
        (listPolicyKernel (sparsePackingExperiment T M d Q hd hDim hM
          t0 zeta C code hCode v) p)) ≤ mixingAlpha t0 * tvNorm (nu - nu')
  have heq : listPolicyKernel
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v) p =
      fun s s' ↦ ∑ a : Bool, p s.1 a *
        sparseStateWeight hd t0 C code v false s s' a := by
    funext s s'
    exact sparse_packing_policy_kernel_weight T M d Q hd hDim hM
      t0 zeta C ht0 hC code hCode v p s s'
  rw [heq]
  exact sparse_policy_weight_contraction hd t0 C ht0 hC code v false p hpvec

end CausalSmith.Stat.PomdpPolicyclassRegret
