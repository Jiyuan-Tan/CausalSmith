module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseContraction
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels

/-! # Stationary initialization of the sparse common-kernel experiment

The common-reset contraction supplies a stationary probability vector. The
construction's initial PMF preserves that vector, so the observed log starts
from the behavior stationary law as required by the packing roadmap.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open scoped BigOperators
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Averaging the explicit sparse transition weights under a probability policy gives
probability rows. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the policy](hyp:p), [the policy assumption](hyp:hp), and [the state](hyp:s), this establishes
[the sparse policy weight probability result](goal). -/
-- @node: sparse_policy_weight_probability
lemma sparse_policy_weight_probability {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) :
    ProbabilityVector (fun s' ↦ ∑ a : Bool,
      p s.1 a * sparseStateWeight hd t0 C code v fair s s' a) := by
  constructor
  · intro s'
    exact Finset.sum_nonneg fun a _ ↦ mul_nonneg ((hp s.1).1 a)
      (sparse_state_weight_nonneg hd t0 C ht0 hC code v fair s s' a)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sparse_state_weight_sum, mul_one]
    exact (hp s.1).2

/-- The totalized stationary-law selector is a genuine stationary probability vector for every
sparse probability policy. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the binary code](hyp:code), [the codeword index](hyp:v), [the fair-reference flag](hyp:fair),
[the policy](hyp:p), and [the policy assumption](hyp:hp), this establishes
[the sparse policy weight stationary result](goal). -/
-- @node: sparse_policy_weight_stationary
lemma sparse_policy_weight_stationary {M d Q : Nat} (hd : 0 < d)
    (t0 C : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p) :
    IsStationary (fun s s' ↦ ∑ a : Bool,
      p s.1 a * sparseStateWeight hd t0 C code v fair s s' a)
      (stationaryLaw (fun s s' ↦ ∑ a : Bool,
        p s.1 a * sparseStateWeight hd t0 C code v fair s s' a)) := by
  apply stationaryLaw_isStationary_of_exists
  exact exists_stationary_of_contraction _
    (sparse_policy_weight_probability hd t0 C ht0 hC code v fair p hp)
    _ (sparse_reset_probability_vector hd t0 C hC code v fair)
    (mixingAlpha t0) (mixingAlpha_pos ht0).le (mixingAlpha_lt_one ht0)
    (sparse_policy_weight_contraction hd t0 C ht0 hC code v fair p hp)

/-- The behavior transition used to construct the initial PMF is exactly its explicit action
average. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the fair-reference flag](hyp:fair), this establishes
[the sparse transition weight equality result](goal). -/
-- @node: sparse_transition_weight_eq
lemma sparse_transition_weight_eq {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool) :
    sparseTransition (Q := Q) hd t0 zeta C code v fair =
      fun s s' ↦ ∑ a : Bool, sparseBehaviorWeight zeta a *
        sparseStateWeight hd t0 C code v fair s s' a := by
  funext s s'
  unfold sparseTransition
  simp_rw [sparse_kernel_state_marginal hd t0 C ht0 hC code v fair,
    sparse_behavior_pmf_toReal zeta hzeta]

/-- The behavior stationary vector exists even before initialization is verified, using only the
common-reset construction. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the fair-reference flag](hyp:fair), this establishes
[the sparse transition stationary result](goal). -/
-- @node: sparse_transition_stationary
lemma sparse_transition_stationary {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool) :
    IsStationary (sparseTransition (Q := Q) hd t0 zeta C code v fair)
      (stationaryLaw (sparseTransition (Q := Q) hd t0 zeta C code v fair)) := by
  rw [sparse_transition_weight_eq (Q := Q) hd t0 zeta C ht0 hzeta hC code v fair]
  apply sparse_policy_weight_stationary (Q := Q) hd t0 C ht0 hC code v fair
    (fun _ a ↦ sparseBehaviorWeight zeta a)
  intro x
  constructor
  · intro a
    change 0 ≤ sparseBehaviorWeight zeta a
    rw [← sparse_behavior_pmf_toReal zeta hzeta d Q x a]
    positivity
  · simp [sparseBehaviorWeight]

/-- PMF normalization leaves the selected behavior stationary vector unchanged at
initialization. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the fair-reference flag](hyp:fair), and [the state](hyp:s), this
establishes [the sparse init to real result](goal). -/
-- @node: sparse_init_toReal
lemma sparse_init_toReal {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (fair : Bool)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) :
    (sparseInit hd t0 zeta C code v fair s).toReal =
      stationaryLaw (sparseTransition hd t0 zeta C code v fair) s := by
  have hs := (sparse_transition_stationary (Q := Q) hd t0 zeta C ht0 hzeta hC code v fair).1
  let : NeZero (d * hdepth Q) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
  unfold sparseInit
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hs.1 hs.2 s,
    ENNReal.toReal_ofReal (hs.1 s)]

/-- The sparse packing trajectory starts from its derived behavior stationary law, including the
initial full-state window. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the dim assumption](hyp:hDim),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse packing stationary start result](goal). -/
-- @node: sparse_packing_stationary_start
lemma sparse_packing_stationary_start (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    ListStationaryStart
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v) := by
  let : NeZero (d * hdepth Q) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
  let : NeZero (2 * (Q + 1)) := ⟨by omega⟩
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  have hk : policyKernel (embed F) (embed F).b =
      sparseTransition hd t0 zeta C code v false := by
    change policyKernel (embed F) (fun x a ↦ (F.b x a).toReal) = _
    rw [embed_policyKernel_eq F F.b]
    funext s s'
    unfold finitePolicyKernel sparseTransition
    simp only [F, sparseFinite]
    simp_rw [ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _)]
  have hsel : stationaryLaw (policyKernel (embed F) (embed F).b) =
      (embed F).init := by
    rw [hk]
    funext s
    exact (sparse_init_toReal hd t0 zeta C ht0 hzeta hC code v false s).symm
  change StationaryStart (embed F)
  apply embed_stationaryStart F
  · rw [← hsel, hk]
    exact sparse_transition_stationary hd t0 zeta C ht0 hzeta hC code v false
  · exact hsel

end CausalSmith.Stat.PomdpPolicyclassRegret
