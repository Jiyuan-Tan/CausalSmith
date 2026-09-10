import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Basic
import Mathlib.Data.Real.Basic

set_option linter.style.longLine false

/-! The explicit rational rank-deficient model from the paper. -/

open scoped BigOperators Matrix
open Finset

namespace CausalSmith.SCM.ProxyTargetspanTransport

private noncomputable def witnessPi : Fin 2 → ℝ := ![1 / 2, 1 / 2]
private noncomputable def witnessS : Matrix (Fin 3) (Fin 2) ℝ :=
  !![9 / 19, 1 / 12; 2 / 19, 2 / 3; 8 / 19, 1 / 4]
private noncomputable def witnessM : Matrix (Fin 3) (Fin 3) ℝ :=
  !![4 / 5, 1 / 10, 1 / 10; 1 / 10, 4 / 5, 1 / 10; 1 / 10, 1 / 10, 4 / 5]
private noncomputable def witnessA : Fin 2 → Fin 3 → ℝ :=
  fun x u => if x = 1 then ![1 / 10, 3 / 5, 1 / 5] u else 1 - ![1 / 10, 3 / 5, 1 / 5] u
private noncomputable def witnessF : Fin 2 → Fin 2 → Fin 3 → Fin 3 → ℝ :=
  fun x y u w =>
    let p := 1 / 5 + (x : ℝ) / 5 + (u : ℝ) / 20 + (w : ℝ) / 100
    if y = 1 then p else 1 - p
private noncomputable def witnessQ : Fin 3 → ℝ := ![1197 / 5837, 2436 / 5837, 2204 / 5837]

-- @node: def:rank-deficient-success-witness
set_option maxHeartbeats 1000000 in
-- The fully expanded finite normalization checks need more than the default heartbeat budget.
/-- This declaration provides [the explicit positive finite latent-shift model with a rank-deficient conditional proxy matrix but valid target-span identification](goal). -/
noncomputable def rankDeficientSuccessWitness :
    LatentShiftSCM (Fin 2) (Fin 3) (Fin 3) (Fin 2) (Fin 2) where
  environment_nonempty := by infer_instance
  treatment_nonempty := by infer_instance
  latent_card := by decide
  proxy_card := by decide
  outcome_card := by decide
  pi := witnessPi
  S := witnessS
  M := witnessM
  a := witnessA
  f := witnessF
  q := witnessQ
  PM := fun e u w x y => witnessPi e * witnessS u e * witnessM w u * witnessA x u * witnessF x y u w
  QM := fun u w x y => witnessQ u * witnessM w u * witnessA x u * witnessF x y u w
  pi_nonneg := by
    intro e
    fin_cases e <;> norm_num [witnessPi]
  pi_sum := by norm_num [witnessPi, Fin.sum_univ_succ]
  S_nonneg := by
    intro u e
    fin_cases u <;> fin_cases e <;> norm_num [witnessS]
  S_col := by
    intro e
    fin_cases e <;> norm_num [witnessS, Fin.sum_univ_succ]
  M_nonneg := by
    intro w u
    fin_cases w <;> fin_cases u <;> norm_num [witnessM]
  M_col := by
    intro u
    fin_cases u <;> norm_num [witnessM, Fin.sum_univ_succ]
  a_nonneg := by
    intro x u
    fin_cases x <;> fin_cases u <;> norm_num [witnessA]
  a_col := by
    intro u
    fin_cases u <;> norm_num [witnessA, Fin.sum_univ_succ]
  f_nonneg := by
    intro x y u w
    fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases w <;>
      norm_num [witnessF]
  f_col := by
    intro x u w
    fin_cases x <;> fin_cases u <;> fin_cases w <;>
      norm_num [witnessF, Fin.sum_univ_succ]
  q_nonneg := by
    intro u
    fin_cases u <;> norm_num [witnessQ]
  q_sum := by norm_num [witnessQ, Fin.sum_univ_succ]
  PM_nonneg := by
    intro e u w x y
    fin_cases e <;> fin_cases u <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
      norm_num [witnessPi, witnessS, witnessM, witnessA, witnessF]
  PM_sum := by
    norm_num [witnessPi, witnessS, witnessM, witnessA, witnessF,
      Fin.sum_univ_succ]
  QM_nonneg := by
    intro u w x y
    fin_cases u <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
      norm_num [witnessQ, witnessM, witnessA, witnessF]
  QM_sum := by
    norm_num [witnessQ, witnessM, witnessA, witnessF, Fin.sum_univ_succ]
-- @realizes \mathcal M^{\star}(explicit rational SCM)

/-- [the designated two-by-two proxy minor of the explicit witness has the stated nonzero determinant](goal). -/
lemma rankDeficientSuccessWitness_proxy_det : rankDeficientSuccessWitness.M.det = 49 / 100 := by
  simp [rankDeficientSuccessWitness, witnessM, Matrix.det_fin_three]
  norm_num

-- @node: rankDeficientSuccessWitness_positive
/-- [the explicit rank-deficient witness satisfies the positive latent-shift model conditions](goal). -/
lemma rankDeficientSuccessWitness_positive :
    PositiveLatentShiftClass rankDeficientSuccessWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e u w x y
    rfl
  · intro u w x y
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; fin_cases e <;> norm_num [rankDeficientSuccessWitness, witnessPi]
    · intro u e
      fin_cases u <;> fin_cases e <;> norm_num [rankDeficientSuccessWitness, witnessS]
    · intro w u
      fin_cases w <;> fin_cases u <;> norm_num [rankDeficientSuccessWitness, witnessM]
    · intro x u
      fin_cases x <;> fin_cases u <;> norm_num [rankDeficientSuccessWitness, witnessA]
    · intro x y u w
      fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases w <;>
        norm_num [rankDeficientSuccessWitness, witnessF]
    · intro u; fin_cases u <;> norm_num [rankDeficientSuccessWitness, witnessQ]
  · apply Matrix.rank_of_det_ne_zero
    rw [rankDeficientSuccessWitness_proxy_det]
    norm_num

-- @node: rankDeficientSuccessWitness_condProxy_rank
/-- [the explicit witness's conditional proxy matrix has rank two rather than latent dimension three](goal). -/
lemma rankDeficientSuccessWitness_condProxy_rank (x : Fin 2) :
    (condProxyMatrix rankDeficientSuccessWitness x).rank = 2 := by
  have hi : Function.Injective (condProxyMatrix rankDeficientSuccessWitness x).mulVec := by
    intro v v' hv
    have h0 := congrFun hv (0 : Fin 3)
    have h1 := congrFun hv (1 : Fin 3)
    fin_cases x <;>
      norm_num [condProxyMatrix, observedLaw, rankDeficientSuccessWitness, witnessPi,
        witnessS, witnessM, witnessA, witnessF, Matrix.mulVec, Fin.sum_univ_succ] at h0 h1
    all_goals
      funext e
      fin_cases e <;> norm_num [div_eq_mul_inv] at h0 h1 ⊢ <;> linarith
  rw [Matrix.mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span] at hi
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols] at hi
  norm_num at hi ⊢
  exact hi.symm

-- @node: rankDeficientSuccessWitness_latentPosterior_zero
/-- [the witness latent posterior for the first environment equals the stated vector](goal). -/
lemma rankDeficientSuccessWitness_latentPosterior_zero :
    latentPosterior rankDeficientSuccessWitness 0 =
      !![9 / 17, 9 / 65; 8 / 153, 32 / 65; 64 / 153, 24 / 65] := by
  ext u e
  fin_cases u <;> fin_cases e <;>
    norm_num [latentPosterior, sourceTreatmentProb, rankDeficientSuccessWitness,
      witnessS, witnessA, Fin.sum_univ_succ]

-- @node: rankDeficientSuccessWitness_latentPosterior_one
/-- [the witness latent posterior for the second environment equals the stated vector](goal). -/
lemma rankDeficientSuccessWitness_latentPosterior_one :
    latentPosterior rankDeficientSuccessWitness 1 =
      !![9 / 37, 1 / 55; 12 / 37, 48 / 55; 16 / 37, 6 / 55] := by
  ext u e
  fin_cases u <;> fin_cases e <;>
    norm_num [latentPosterior, sourceTreatmentProb, rankDeficientSuccessWitness,
      witnessS, witnessA, Fin.sum_univ_succ]

-- @node: rankDeficientSuccessWitness_target_span
/-- [the explicit rank-deficient witness nevertheless satisfies the target-span condition for every treatment](goal). -/
lemma rankDeficientSuccessWitness_target_span (x : Fin 2) :
    (balancingFiber (condProxyMatrix rankDeficientSuccessWitness x)
      (targetProxyVector rankDeficientSuccessWitness)).Nonempty := by
  fin_cases x
  · refine ⟨![153 / 898, 745 / 898], ?_⟩
    have hR : (latentPosterior rankDeficientSuccessWitness 0).mulVec
        ![153 / 898, 745 / 898] = rankDeficientSuccessWitness.q := by
      rw [rankDeficientSuccessWitness_latentPosterior_zero]
      ext u
      fin_cases u <;> norm_num [rankDeficientSuccessWitness, witnessQ,
        Matrix.mulVec, Fin.sum_univ_two]
    have hfac := observable_factorization rankDeficientSuccessWitness
      rankDeficientSuccessWitness_positive 0 0
    change (condProxyMatrix rankDeficientSuccessWitness 0).mulVec
      ![153 / 898, 745 / 898] = targetProxyVector rankDeficientSuccessWitness
    rw [hfac.1, ← Matrix.mulVec_mulVec, hR, hfac.2.1]
  · refine ⟨![4847 / 5837, 990 / 5837], ?_⟩
    have hR : (latentPosterior rankDeficientSuccessWitness 1).mulVec
        ![4847 / 5837, 990 / 5837] = rankDeficientSuccessWitness.q := by
      rw [rankDeficientSuccessWitness_latentPosterior_one]
      ext u
      fin_cases u <;> norm_num [rankDeficientSuccessWitness, witnessQ,
        Matrix.mulVec, Fin.sum_univ_two]
    have hfac := observable_factorization rankDeficientSuccessWitness
      rankDeficientSuccessWitness_positive 1 0
    change (condProxyMatrix rankDeficientSuccessWitness 1).mulVec
      ![4847 / 5837, 990 / 5837] = targetProxyVector rankDeficientSuccessWitness
    rw [hfac.1, ← Matrix.mulVec_mulVec, hR, hfac.2.1]

end CausalSmith.SCM.ProxyTargetspanTransport
