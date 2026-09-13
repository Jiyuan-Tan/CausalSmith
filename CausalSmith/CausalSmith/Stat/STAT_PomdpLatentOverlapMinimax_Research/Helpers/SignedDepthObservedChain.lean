import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedLawChainRule
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedFilter

set_option linter.style.longLine false

/-!
# Signed-depth observed-chain bridges

This module connects the generic finite-word chain rule to the chronological signed-depth
path representation.
-/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Remove the deterministic observed-state coordinate from a singleton-state observed word. -/
def signedDepthObservedActions {k : Nat} (w : FiniteObsView k 1 2) : ObsPrefix k :=
  fun i ↦ ((w i).2.1, (w i).2.2)

/-- Summing all one-symbol extensions of a fixed observed prefix leaves its likelihood mass
unchanged. [the stated conclusion](goal). -/
lemma sum_finiteFixedPrefixWeight_extensions {k nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) :
    (∑ ar : Bool × Fin nR, ∑ rho : Fin (k + 2) → JointState nX nH,
      finiteFixedPrefixWeight kernel p b (Fin.snoc o ar) rho) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b o sigma := by
  classical
  rw [Finset.sum_comm]
  rw [Fintype.sum_equiv (finiteStatePrefixLastEquiv k nX nH)
    (fun rho ↦ ∑ ar : Bool × Fin nR,
      finiteFixedPrefixWeight kernel p b (Fin.snoc o ar) rho)
    (fun z ↦ ∑ ar : Bool × Fin nR,
      finiteFixedPrefixWeight kernel p b (Fin.snoc o ar) (Fin.snoc z.1 z.2))]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro sigma _
    simp_rw [finiteFixedPrefixWeight_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [Finset.sum_comm]
    have hfactor (ar : Bool × Fin nR) (s' : JointState nX nH) :
        finiteFixedPrefixWeight kernel p b o sigma *
            (b (sigma (Fin.last k)).1 ar.1).toReal *
              (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal =
          finiteFixedPrefixWeight kernel p b o sigma *
            ((b (sigma (Fin.last k)).1 ar.1).toReal *
              (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal) := by ring
    simp_rw [hfactor]
    have hpull :
        (∑ ar : Bool × Fin nR, ∑ s' : JointState nX nH,
          finiteFixedPrefixWeight kernel p b o sigma *
            ((b (sigma (Fin.last k)).1 ar.1).toReal *
              (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal)) =
          finiteFixedPrefixWeight kernel p b o sigma *
            ∑ ar : Bool × Fin nR, ∑ s' : JointState nX nH,
              (b (sigma (Fin.last k)).1 ar.1).toReal *
                (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ar _
      rw [Finset.mul_sum]
    rw [hpull]
    have hinner :
        (∑ ar : Bool × Fin nR, ∑ s' : JointState nX nH,
          (b (sigma (Fin.last k)).1 ar.1).toReal *
            (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal) = 1 := by
      rw [Fintype.sum_prod_type]
      calc
      (∑ a : Bool, ∑ r : Fin nR, ∑ s' : JointState nX nH,
          (b (sigma (Fin.last k)).1 a).toReal *
            (kernel (sigma (Fin.last k)) a (r, s')).toReal) =
          ∑ a : Bool, (b (sigma (Fin.last k)).1 a).toReal *
            ∑ rs : Fin nR × JointState nX nH,
              (kernel (sigma (Fin.last k)) a rs).toReal := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            simp_rw [Finset.mul_sum]
      _ = ∑ a : Bool, (b (sigma (Fin.last k)).1 a).toReal := by
            apply Finset.sum_congr rfl
            intro a _
            rw [sum_pmf_toReal_eq_one, mul_one]
      _ = 1 := sum_pmf_toReal_eq_one _
    rw [hinner, mul_one]
  · intro rho
    rw [show Fin.snoc ((finiteStatePrefixLastEquiv k nX nH rho).1)
      ((finiteStatePrefixLastEquiv k nX nH rho).2) = rho from
        (finiteStatePrefixLastEquiv k nX nH).symm_apply_apply rho]

/-- The mass of one fixed action/reward extension is the preceding state-prefix mass times
the corresponding behavior and one-step kernel marginal. [the stated conclusion](goal). -/
lemma sum_finiteFixedPrefixWeight_fixedExtension {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) (a : Bool) (r : Fin nR) :
    (∑ rho : Fin (k + 2) → JointState nX nH,
      finiteFixedPrefixWeight kernel p b (Fin.snoc o (a, r)) rho) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b o sigma *
          (b (sigma (Fin.last k)).1 a).toReal *
            ∑ s' : JointState nX nH, (kernel (sigma (Fin.last k)) a (r, s')).toReal := by
  classical
  rw [Fintype.sum_equiv (finiteStatePrefixLastEquiv k nX nH)
    (fun rho ↦ finiteFixedPrefixWeight kernel p b (Fin.snoc o (a, r)) rho)
    (fun z ↦ finiteFixedPrefixWeight kernel p b (Fin.snoc o (a, r))
      (Fin.snoc z.1 z.2))]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro sigma _
    simp_rw [finiteFixedPrefixWeight_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Finset.mul_sum]
  · intro rho
    rw [show Fin.snoc ((finiteStatePrefixLastEquiv k nX nH rho).1)
      ((finiteStatePrefixLastEquiv k nX nH rho).2) = rho from
        (finiteStatePrefixLastEquiv k nX nH).symm_apply_apply rho]

/-- The real mass of a signed-depth observed word is its fixed-observation chronological
state-prefix likelihood sum. [the stated conclusion](goal). -/
lemma signedDepth_obsPMF_toReal_eq_fixedPrefix {k Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (w : FiniteObsView k 1 2) :
    ((signedDepthFinite k t0 zeta C Q v).obsPMF w).toReal =
      ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        finiteFixedPrefixWeight
          (signedDepthFinite k t0 zeta C Q v).kernel
          (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
          (signedDepthFinite k t0 zeta C Q v).b
          (signedDepthObservedActions w) sigma := by
  classical
  unfold FiniteRewardModel.obsPMF
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · rw [tsum_fintype, Fintype.sum_prod_type]
    simp only [apply_ite, ENNReal.toReal_zero]
    simp_rw [finiteRewardModel_law_toReal]
    let o : Fin k → Bool × Fin 2 := signedDepthObservedActions w
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single o]
    · apply Finset.sum_congr rfl
      intro sigma _
      have hproj : w = finObsProj (sigma, o) := by
        funext i
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      simp only [hproj, if_true]
      rfl
    · intro o' _ hne
      apply Finset.sum_eq_zero
      intro sigma _
      have hnot : w ≠ finObsProj (sigma, o') := by
        intro heq
        apply hne
        funext i
        have hi := congrFun heq i
        simpa [finObsProj, o, signedDepthObservedActions] using (congrArg Prod.snd hi).symm
      simp [hnot]
    · simp
  · intro tau
    split <;> simp [PMF.apply_ne_top]

/-- Marginalizing the final epoch of a signed-depth observed law gives the preceding-horizon
signed-depth observed law. [the stated conclusion](goal). -/
lemma signedDepth_observed_horizon_projective {k Q : Nat} (t0 zeta C : ℝ) (v : Bool) :
    Causalean.Mathlib.InformationTheory.FiniteWordChainRule.prefixPMF
      (signedDepthFinite (k + 1) t0 zeta C Q v).obsPMF =
      (signedDepthFinite k t0 zeta C Q v).obsPMF := by
  classical
  apply PMF.ext
  intro w
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Causalean.Mathlib.InformationTheory.FiniteWordChainRule.prefixPMF_apply,
    ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _)]
  simp_rw [signedDepth_obsPMF_toReal_eq_fixedPrefix]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_one]
  have hactions (ar : Bool × Fin 2) :
      signedDepthObservedActions
        (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.appendSymbol w (0, ar)) =
        Fin.snoc (signedDepthObservedActions w) ar := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [signedDepthObservedActions,
        Causalean.Mathlib.InformationTheory.FiniteWordChainRule.appendSymbol]
    · simp [signedDepthObservedActions,
        Causalean.Mathlib.InformationTheory.FiniteWordChainRule.appendSymbol]
  simp_rw [hactions]
  simp only [signedDepthFinite]
  change (∑ ar : Bool × Fin 2,
      ∑ rho : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
        finiteFixedPrefixWeight
          (signedDepthFinite k t0 zeta C Q v).kernel
          (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
          (signedDepthFinite k t0 zeta C Q v).b
          (Fin.snoc (signedDepthObservedActions w) ar) rho) = _
  exact sum_finiteFixedPrefixWeight_extensions
    (signedDepthFinite k t0 zeta C Q v).kernel
    (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
    (signedDepthFinite k t0 zeta C Q v).b (signedDepthObservedActions w)

/-- A shorter-horizon observed-word mass is the public strict-prefix mass in any horizon with
one additional epoch. [the stated conclusion](goal). -/
lemma signedDepth_obsPMF_toReal_eq_prefixMass {k Q : Nat} (t0 zeta C : ℝ) (v : Bool)
    (w : FiniteObsView k 1 2) :
    ((signedDepthFinite k t0 zeta C Q v).obsPMF w).toReal =
      prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k))
        (signedDepthObservedActions w) := by
  rw [signedDepth_obsPMF_toReal_eq_fixedPrefix]
  have h := prefixMass_eq_finiteFixedPrefixWeight_sum 1 k (by omega)
    t0 zeta C Q v (signedDepthObservedActions w)
  simpa only [signedDepthFinite] using h.symm

/-- Every strict observed prefix has positive chronological likelihood under the signed-depth
model.  This is the real-valued form of full support used to cancel conditional denominators. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_prefixMass_pos {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool) (o : ObsPrefix k) :
    0 < prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k)) o := by
  let w : FiniteObsView k 1 2 := fun i ↦ (0, o i)
  have hp : 0 < (signedDepthFinite k t0 zeta C Q v).obsPMF w :=
    signedDepth_fullSupportObs ht0 hzeta hC w
  have hreal : 0 < ((signedDepthFinite k t0 zeta C Q v).obsPMF w).toReal :=
    ENNReal.toReal_pos hp.ne' (PMF.apply_ne_top _ _)
  have hw : signedDepthObservedActions w = o := by
    funext i
    rfl
  rw [signedDepth_obsPMF_toReal_eq_prefixMass, hw] at hreal
  exact hreal

/-- A fixed signed-depth action/reward extension is behavior mass times the affine
two-point reward mass determined by the terminal signed filter moment. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_fixedExtensionMass {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : ObsPrefix k) (a : Bool) (r : Fin 2) :
    (∑ rho : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
      finiteFixedPrefixWeight
        (signedDepthFinite k t0 zeta C Q v).kernel
        (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
        (signedDepthFinite k t0 zeta C Q v).b (Fin.snoc o (a, r)) rho) =
      signedDepthBehaviourWeight zeta a *
        ((∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
            finiteFixedPrefixWeight
              (signedDepthFinite k t0 zeta C Q v).kernel
              (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
              (signedDepthFinite k t0 zeta C Q v).b o sigma) +
          (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
            (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
              if latentDepth Q (sigma (Fin.last k)).2 = Q then
                signedValue (latentSign Q (sigma (Fin.last k)).2) *
                  finiteFixedPrefixWeight
                    (signedDepthFinite k t0 zeta C Q v).kernel
                    (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
                    (signedDepthFinite k t0 zeta C Q v).b o sigma else 0)) / 2 := by
  classical
  rw [sum_finiteFixedPrefixWeight_fixedExtension]
  have hb (s : JointState 1 (2 * (Q + 1))) :
      ((signedDepthFinite k t0 zeta C Q v).b s.1 a).toReal =
        signedDepthBehaviourWeight zeta a := by
    have hs : s.1 = 0 := Fin.eq_zero _
    simpa [hs] using signedDepthFinite_b_toReal (T := k) (Q := Q) hzeta v a
  have hkernel (s : JointState 1 (2 * (Q + 1)))
      (p : Fin 2 × JointState 1 (2 * (Q + 1))) :
      ((signedDepthFinite k t0 zeta C Q v).kernel s a p).toReal =
        signedDepthRewardWeight t0 Q v s.2 p.1 *
          signedDepthStateWeight t0 C Q s.2 a p.2.2 := by
    have hs : s = (0, s.2) := by
      apply Prod.ext
      · exact Fin.eq_zero _
      · rfl
    rw [hs]
    exact signedDepthFinite_kernel_toReal (T := k) (zeta := zeta) ht0 hC.le v s.2 a p
  simp_rw [hb, hkernel]
  have hsumkernel (h : Fin (2 * (Q + 1))) :
      (∑ s' : JointState 1 (2 * (Q + 1)),
        signedDepthRewardWeight t0 Q v h r *
          signedDepthStateWeight t0 C Q h a s'.2) =
        signedDepthRewardWeight t0 Q v h r := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_nsmul]
    rw [← Finset.mul_sum, sum_signedDepthStateWeight, mul_one]
  simp_rw [hsumkernel]
  have hfactor :
      (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        finiteFixedPrefixWeight
            (signedDepthFinite k t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
            (signedDepthFinite k t0 zeta C Q v).b o sigma *
          signedDepthBehaviourWeight zeta a *
          signedDepthRewardWeight t0 Q v (sigma (Fin.last k)).2 r) =
        signedDepthBehaviourWeight zeta a *
          ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
            finiteFixedPrefixWeight
                (signedDepthFinite k t0 zeta C Q v).kernel
                (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
                (signedDepthFinite k t0 zeta C Q v).b o sigma *
              signedDepthRewardWeight t0 Q v (sigma (Fin.last k)).2 r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma _
    ring
  rw [hfactor]
  have hterm (sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1))) :
      finiteFixedPrefixWeight
          (signedDepthFinite k t0 zeta C Q v).kernel
          (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
          (signedDepthFinite k t0 zeta C Q v).b o sigma *
          signedDepthRewardWeight t0 Q v (sigma (Fin.last k)).2 r =
        (finiteFixedPrefixWeight
            (signedDepthFinite k t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
            (signedDepthFinite k t0 zeta C Q v).b o sigma +
          (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
            (if latentDepth Q (sigma (Fin.last k)).2 = Q then
              signedValue (latentSign Q (sigma (Fin.last k)).2) *
                finiteFixedPrefixWeight
                  (signedDepthFinite k t0 zeta C Q v).kernel
                  (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
                  (signedDepthFinite k t0 zeta C Q v).b o sigma else 0)) / 2 := by
    unfold signedDepthRewardWeight
    by_cases hQ : latentDepth Q (sigma (Fin.last k)).2 = Q
    all_goals
      by_cases hr : r = 0 <;> simp [hQ, hr] <;> ring
  have hrepl :
      (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        finiteFixedPrefixWeight
            (signedDepthFinite k t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
            (signedDepthFinite k t0 zeta C Q v).b o sigma *
          signedDepthRewardWeight t0 Q v (sigma (Fin.last k)).2 r) =
        ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
          (finiteFixedPrefixWeight
              (signedDepthFinite k t0 zeta C Q v).kernel
              (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
              (signedDepthFinite k t0 zeta C Q v).b o sigma +
            (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
              (if latentDepth Q (sigma (Fin.last k)).2 = Q then
                signedValue (latentSign Q (sigma (Fin.last k)).2) *
                  finiteFixedPrefixWeight
                    (signedDepthFinite k t0 zeta C Q v).kernel
                    (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
                    (signedDepthFinite k t0 zeta C Q v).b o sigma else 0)) / 2 := by
    apply Finset.sum_congr rfl
    intro sigma _
    exact hterm sigma
  rw [hrepl]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  ring

/-- The chronological terminal signed moment is the conditional reward mean multiplied by
the prefix likelihood (after restoring the common signed reward amplitude). [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_terminalMoment_eq_conditionalRewardMean_mul_prefixMass
    {k Q : Nat} {t0 zeta C : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (v : Bool) (o : ObsPrefix k) :
    signedValue v * c0 t0 *
        (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
          if latentDepth Q (sigma (Fin.last k)).2 = Q then
            signedValue (latentSign Q (sigma (Fin.last k)).2) *
              finiteFixedPrefixWeight
                (signedDepthFinite (1 + k) t0 zeta C Q v).kernel
                (fun s ↦ ((signedDepthFinite (1 + k) t0 zeta C Q v).init s).toReal)
                (signedDepthFinite (1 + k) t0 zeta C Q v).b o sigma else 0) =
      conditionalRewardMean (1 + k) t0 zeta C Q v
          (⟨k, by omega⟩ : Fin (1 + k)) o *
        prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k)) o := by
  rw [← sum_terminalSignedFilterMass_eq_sum_fixedPrefix]
  rw [signedDepth_terminalMass_invariant ht0 hzeta hC]
  rw [conditionalRewardMean_signedDepth_all ht0 hzeta hC]
  have hterm := terminalPrefixMass_eq_sum_signedDepthFilterMass 1 k (by omega)
    t0 zeta C Q v o
  rw [← hterm]
  have hp := signedDepth_prefixMass_pos (Q := Q) ht0 hzeta hC v o
  simp only [filterQuantities, signedDepthActionFactor]
  field_simp [ne_of_gt hp]

/-- The fixed next-symbol mass is behavior mass times the Rademacher reward likelihood whose
mean is the already identified finite-prefix conditional reward mean. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_fixedExtensionMass_conditional {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : ObsPrefix k) (a : Bool) (r : Fin 2) :
    (∑ rho : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
      finiteFixedPrefixWeight
        (signedDepthFinite k t0 zeta C Q v).kernel
        (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
        (signedDepthFinite k t0 zeta C Q v).b (Fin.snoc o (a, r)) rho) =
      signedDepthBehaviourWeight zeta a *
        (prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k)) o +
          (if r = 0 then (-1 : ℝ) else 1) *
            conditionalRewardMean (1 + k) t0 zeta C Q v
              (⟨k, by omega⟩ : Fin (1 + k)) o *
            prefixMass (1 + k) t0 zeta C Q v
              (⟨k, by omega⟩ : Fin (1 + k)) o) / 2 := by
  rw [signedDepth_fixedExtensionMass ht0 hzeta hC]
  have hp := prefixMass_eq_finiteFixedPrefixWeight_sum 1 k (by omega)
    t0 zeta C Q v o
  have hp' :
      (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        finiteFixedPrefixWeight
          (signedDepthFinite k t0 zeta C Q v).kernel
          (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
          (signedDepthFinite k t0 zeta C Q v).b o sigma) =
        prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k)) o := by
    simpa only [signedDepthFinite] using hp.symm
  rw [hp']
  have hm := signedDepth_terminalMoment_eq_conditionalRewardMean_mul_prefixMass
    (Q := Q) ht0 hzeta hC v o
  have hm' :
      signedValue v * c0 t0 *
          (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
            if latentDepth Q (sigma (Fin.last k)).2 = Q then
              signedValue (latentSign Q (sigma (Fin.last k)).2) *
                finiteFixedPrefixWeight
                  (signedDepthFinite k t0 zeta C Q v).kernel
                  (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
                  (signedDepthFinite k t0 zeta C Q v).b o sigma else 0) =
        conditionalRewardMean (1 + k) t0 zeta C Q v
            (⟨k, by omega⟩ : Fin (1 + k)) o *
          prefixMass (1 + k) t0 zeta C Q v
            (⟨k, by omega⟩ : Fin (1 + k)) o := by
    simpa only [signedDepthFinite] using hm
  rw [show (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
      (∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        if latentDepth Q (sigma (Fin.last k)).2 = Q then
          signedValue (latentSign Q (sigma (Fin.last k)).2) *
            finiteFixedPrefixWeight
              (signedDepthFinite k t0 zeta C Q v).kernel
              (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
              (signedDepthFinite k t0 zeta C Q v).b o sigma else 0) =
      (if r = 0 then (-1 : ℝ) else 1) *
        (signedValue v * c0 t0 *
          ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
            if latentDepth Q (sigma (Fin.last k)).2 = Q then
              signedValue (latentSign Q (sigma (Fin.last k)).2) *
                finiteFixedPrefixWeight
                  (signedDepthFinite k t0 zeta C Q v).kernel
                  (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
                  (signedDepthFinite k t0 zeta C Q v).b o sigma else 0) by ring,
    hm']
  ring

/-- Pointwise real-mass form of the signed-depth conditional next-observation law.  The
singleton observed state is deterministic, the behavior action factor is common to both signs,
and the reward coordinate is the two-point law with the finite-prefix conditional mean. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_observedNextPMF_toReal {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (w : FiniteObsView k 1 2) (x : Fin 1 × Bool × Fin 2) :
    (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF
      (signedDepthFinite (k + 1) t0 zeta C Q v).obsPMF w x).toReal =
      signedDepthBehaviourWeight zeta x.2.1 *
        (1 + (if x.2.2 = 0 then (-1 : ℝ) else 1) *
          conditionalRewardMean (1 + k) t0 zeta C Q v
            (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)) / 2 := by
  let p := (signedDepthFinite (k + 1) t0 zeta C Q v).obsPMF
  have hprefix : Causalean.Mathlib.InformationTheory.FiniteWordChainRule.prefixPMF p w =
      (signedDepthFinite k t0 zeta C Q v).obsPMF w := by
    dsimp [p]
    rw [signedDepth_observed_horizon_projective (k := k) (Q := Q) t0 zeta C v]
  have hpobs : 0 < (signedDepthFinite k t0 zeta C Q v).obsPMF w :=
    signedDepth_fullSupportObs ht0 hzeta hC w
  have hpne : Causalean.Mathlib.InformationTheory.FiniteWordChainRule.prefixPMF p w ≠ 0 := by
    rw [hprefix]
    exact hpobs.ne'
  rw [Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF, dif_neg hpne,
    PMF.ofFintype_apply, ENNReal.toReal_div]
  have hactions :
      signedDepthObservedActions
        (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.appendSymbol w x) =
        Fin.snoc (signedDepthObservedActions w) (x.2.1, x.2.2) := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [signedDepthObservedActions,
        Causalean.Mathlib.InformationTheory.FiniteWordChainRule.appendSymbol]
    · simp [signedDepthObservedActions,
        Causalean.Mathlib.InformationTheory.FiniteWordChainRule.appendSymbol]
  rw [signedDepth_obsPMF_toReal_eq_fixedPrefix, hactions]
  change (∑ rho : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
      finiteFixedPrefixWeight
        (signedDepthFinite (k + 1) t0 zeta C Q v).kernel
        (fun s ↦ ((signedDepthFinite (k + 1) t0 zeta C Q v).init s).toReal)
        (signedDepthFinite (k + 1) t0 zeta C Q v).b
        (Fin.snoc (signedDepthObservedActions w) (x.2.1, x.2.2)) rho) /
      (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.prefixPMF p w).toReal = _
  have hext := signedDepth_fixedExtensionMass_conditional (Q := Q)
    ht0 hzeta hC v (signedDepthObservedActions w) x.2.1 x.2.2
  change (∑ rho : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
      finiteFixedPrefixWeight
        (signedDepthFinite (k + 1) t0 zeta C Q v).kernel
        (fun s ↦ ((signedDepthFinite (k + 1) t0 zeta C Q v).init s).toReal)
        (signedDepthFinite (k + 1) t0 zeta C Q v).b
        (Fin.snoc (signedDepthObservedActions w) (x.2.1, x.2.2)) rho) =
      signedDepthBehaviourWeight zeta x.2.1 *
        (prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k))
            (signedDepthObservedActions w) +
          (if x.2.2 = 0 then (-1 : ℝ) else 1) *
            conditionalRewardMean (1 + k) t0 zeta C Q v
              (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) *
            prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k))
              (signedDepthObservedActions w)) / 2 at hext
  rw [hext, hprefix, signedDepth_obsPMF_toReal_eq_prefixMass]
  have hp := signedDepth_prefixMass_pos (Q := Q) ht0 hzeta hC v
    (signedDepthObservedActions w)
  field_simp [ne_of_gt hp]

/-- Summing the two reward extensions at a fixed action cancels the signed reward tilt. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma sum_reward_signedDepth_fixedExtensionMass {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : ObsPrefix k) (a : Bool) :
    (∑ r : Fin 2, ∑ rho : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
      finiteFixedPrefixWeight
        (signedDepthFinite k t0 zeta C Q v).kernel
        (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
        (signedDepthFinite k t0 zeta C Q v).b (Fin.snoc o (a, r)) rho) =
      signedDepthBehaviourWeight zeta a *
        ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
          finiteFixedPrefixWeight
            (signedDepthFinite k t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
            (signedDepthFinite k t0 zeta C Q v).b o sigma := by
  simp_rw [signedDepth_fixedExtensionMass ht0 hzeta hC]
  rw [Fin.sum_univ_two]
  simp
  ring

/-- Marginalizing all rewards from a prescribed action history leaves the product of behavior
weights.  The proof peels the last reward symbol and uses the preceding cancellation lemma. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma sum_rewards_signedDepth_prefixMass {Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool) :
    ∀ (k : Nat) (a : Fin k → Bool),
      (∑ rseq : Fin k → Fin 2,
        ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
          finiteFixedPrefixWeight
            (signedDepthFinite k t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite k t0 zeta C Q v).init s).toReal)
            (signedDepthFinite k t0 zeta C Q v).b
            (fun i ↦ (a i, rseq i)) sigma) =
        ∏ i : Fin k, signedDepthBehaviourWeight zeta (a i) := by
  intro k
  induction k with
  | zero =>
      intro a
      simp only [Fintype.sum_unique]
      simp only [finiteFixedPrefixWeight]
      simp
      change (∑ sigma : Fin 1 → JointState 1 (2 * (Q + 1)),
        ((signedDepthFinite 0 t0 zeta C Q v).init (sigma 0)).toReal) = 1
      rw [Fintype.sum_equiv (finiteStatePrefixZeroEquiv 1 (2 * (Q + 1)))
        (fun sigma ↦ ((signedDepthFinite 0 t0 zeta C Q v).init (sigma 0)).toReal)
        (fun s ↦ ((signedDepthFinite 0 t0 zeta C Q v).init s).toReal)]
      · rw [Fintype.sum_prod_type, Fin.sum_univ_one]
        simp_rw [signedDepthFinite_init_toReal ht0 hzeta hC.le]
        exact sum_signedDepthInitWeight ht0 Q
      · intro sigma
        simp [finiteStatePrefixZeroEquiv]
  | succ k ih =>
      intro a
      let a0 : Fin k → Bool := fun i ↦ a i.castSucc
      let alast : Bool := a (Fin.last k)
      let e : (Fin (k + 1) → Fin 2) ≃ (Fin k → Fin 2) × Fin 2 :=
        Causalean.Mathlib.InformationTheory.FiniteWordChainRule.lastCoordinateSplit k
      rw [Fintype.sum_equiv e
        (fun rseq ↦ ∑ sigma : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
          finiteFixedPrefixWeight
            (signedDepthFinite (k + 1) t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite (k + 1) t0 zeta C Q v).init s).toReal)
            (signedDepthFinite (k + 1) t0 zeta C Q v).b
            (fun i ↦ (a i, rseq i)) sigma)
        (fun z ↦ ∑ sigma : Fin (k + 2) → JointState 1 (2 * (Q + 1)),
          finiteFixedPrefixWeight
            (signedDepthFinite (k + 1) t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite (k + 1) t0 zeta C Q v).init s).toReal)
            (signedDepthFinite (k + 1) t0 zeta C Q v).b
            (Fin.snoc (fun i ↦ (a0 i, z.1 i)) (alast, z.2)) sigma)]
      · rw [Fintype.sum_prod_type]
        simp_rw [show (signedDepthFinite (k + 1) t0 zeta C Q v).kernel =
            (signedDepthFinite k t0 zeta C Q v).kernel by rfl,
          show (signedDepthFinite (k + 1) t0 zeta C Q v).init =
            (signedDepthFinite k t0 zeta C Q v).init by rfl,
          show (signedDepthFinite (k + 1) t0 zeta C Q v).b =
            (signedDepthFinite k t0 zeta C Q v).b by rfl]
        simp_rw [sum_reward_signedDepth_fixedExtensionMass ht0 hzeta hC v]
        rw [← Finset.mul_sum, ih a0]
        rw [Fin.prod_univ_castSucc]
        simp only [a0, alast]
        ring
      · intro rseq
        apply Finset.sum_congr rfl
        intro sigma _
        congr 2
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [e, Causalean.Mathlib.InformationTheory.FiniteWordChainRule.lastCoordinateSplit,
            alast]
        · simp [e, Causalean.Mathlib.InformationTheory.FiniteWordChainRule.lastCoordinateSplit,
            a0]

/-- Public `prefixMass` form of the action-history marginal. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma sum_rewards_prefixMass_eq_behaviorProduct {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (a : Fin k → Bool) :
    (∑ rseq : Fin k → Fin 2,
      prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k))
        (fun i ↦ (a i, rseq i))) =
      ∏ i : Fin k, signedDepthBehaviourWeight zeta (a i) := by
  simp_rw [prefixMass_eq_finiteFixedPrefixWeight_sum 1 k (by omega)]
  simpa only [signedDepthFinite] using
    sum_rewards_signedDepth_prefixMass (Q := Q) ht0 hzeta hC v k a

/-- Under the product behavior law, forcing every action in a finite index set to be `true`
has probability `policyFactor zeta⁻¹` to the cardinality of that set. [the stated conclusion](goal). -/
lemma sum_behaviorProduct_mul_trueIndicator {k : Nat} (zeta : ℝ)
    (S : Finset (Fin k)) :
    (∑ a : Fin k → Bool,
      (∏ i : Fin k, signedDepthBehaviourWeight zeta (a i)) *
        (∏ j ∈ S, if a j then (1 : ℝ) else 0)) =
      (1 / policyFactor zeta) ^ S.card := by
  classical
  have hpoint (a : Fin k → Bool) :
      (∏ i : Fin k, signedDepthBehaviourWeight zeta (a i)) *
          (∏ j ∈ S, if a j then (1 : ℝ) else 0) =
        ∏ i : Fin k, (signedDepthBehaviourWeight zeta (a i) *
          (if i ∈ S then (if a i then (1 : ℝ) else 0) else 1)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    simp
  simp_rw [hpoint]
  let f : Fin k → Bool → ℝ := fun i a ↦ signedDepthBehaviourWeight zeta a *
    (if i ∈ S then (if a then (1 : ℝ) else 0) else 1)
  change (∑ x : Fin k → Bool, ∏ i : Fin k, f i (x i)) = _
  rw [← Fintype.prod_sum f]
  have hone (i : Fin k) :
      (∑ a : Bool, signedDepthBehaviourWeight zeta a *
        (if i ∈ S then (if a then (1 : ℝ) else 0) else 1)) =
        if i ∈ S then 1 / policyFactor zeta else 1 := by
    by_cases hi : i ∈ S
    · simp [hi, signedDepthBehaviourWeight]
    · simp only [hi, ↓reduceIte, mul_one]
      exact sum_signedDepthBehaviourWeight zeta
  simp only [f]
  simp_rw [hone]
  simp

/-- Pointwise unzip of action and reward histories. -/
def obsPrefixActionRewardEquiv (k : Nat) :
    ObsPrefix k ≃ (Fin k → Bool) × (Fin k → Fin 2) where
  toFun o := (fun i ↦ (o i).1, fun i ↦ (o i).2)
  invFun z := fun i ↦ (z.1 i, z.2 i)
  left_inv o := by
    funext i
    apply Prod.ext <;> rfl
  right_inv z := by ext <;> rfl

/-- The final window of length `min Q k` has exactly that many indices. [the stated conclusion](goal). -/
lemma card_recentWindow (k Q : Nat) :
    (Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val)).card = min Q k := by
  classical
  by_cases hzero : min Q k = 0
  · have hempty : Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val) = ∅ := by
      ext j
      simp [hzero]
    simp [hempty, hzero]
  · have hpos : 0 < min Q k := Nat.pos_of_ne_zero hzero
    have hle : min Q k ≤ k := min_le_right _ _
    let first : Fin k := ⟨k - min Q k, by omega⟩
    have hset : Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val) =
        Finset.Ici first := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      change k - min Q k ≤ j.val ↔ k - min Q k ≤ j.val
      rfl
    rw [hset, Fin.card_Ici]
    simp [first]
    omega

/-- Exact reduction of the rare-action second moment to the scalar behavior product. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma rareAction_secondMoment_eq {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool) :
    (∑ o : ObsPrefix k,
      prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k)) o *
        signedDepthActionFactor zeta Q o ^ 2) =
      policyFactor zeta ^ (2 * (-(Q - min Q k : ℤ))) *
        (1 / policyFactor zeta) ^
          (Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val)).card := by
  classical
  let S := Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val)
  rw [Fintype.sum_equiv (obsPrefixActionRewardEquiv k)
    (fun o ↦ prefixMass (1 + k) t0 zeta C Q v
      (⟨k, by omega⟩ : Fin (1 + k)) o * signedDepthActionFactor zeta Q o ^ 2)
    (fun z ↦ prefixMass (1 + k) t0 zeta C Q v
      (⟨k, by omega⟩ : Fin (1 + k)) (fun i ↦ (z.1 i, z.2 i)) *
        signedDepthActionFactor zeta Q (fun i ↦ (z.1 i, z.2 i)) ^ 2)]
  · rw [Fintype.sum_prod_type]
    simp only [signedDepthActionFactor]
    change (∑ a : Fin k → Bool, ∑ rseq : Fin k → Fin 2,
      prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k))
          (fun i ↦ (a i, rseq i)) *
        (policyFactor zeta ^ (-(Q - min Q k : ℤ)) *
          ∏ j ∈ S, if a j then (1 : ℝ) else 0) ^ 2) = _
    have hind (a : Fin k → Bool) :
        (∏ j ∈ S, if a j then (1 : ℝ) else 0) ^ 2 =
          ∏ j ∈ S, if a j then (1 : ℝ) else 0 := by
      have hzeroone : (∏ j ∈ S, if a j then (1 : ℝ) else 0) = 0 ∨
          (∏ j ∈ S, if a j then (1 : ℝ) else 0) = 1 := by
        by_cases h : ∀ j ∈ S, a j
        · right
          apply Finset.prod_eq_one
          intro j hj
          simp [h j hj]
        · left
          push_neg at h
          obtain ⟨j, hj, hfalse⟩ := h
          exact Finset.prod_eq_zero hj (by simp [hfalse])
      rcases hzeroone with h | h <;> simp [h]
    simp_rw [mul_pow, hind]
    simp_rw [← Finset.sum_mul]
    simp_rw [sum_rewards_prefixMass_eq_behaviorProduct ht0 hzeta hC v]
    have hfactor (a : Fin k → Bool) :
        (∏ i : Fin k, signedDepthBehaviourWeight zeta (a i)) *
            ((policyFactor zeta ^ (-(Q - min Q k : ℤ))) ^ 2 *
              ∏ j ∈ S, if a j then (1 : ℝ) else 0) =
          (policyFactor zeta ^ (-(Q - min Q k : ℤ))) ^ 2 *
            ((∏ i : Fin k, signedDepthBehaviourWeight zeta (a i)) *
              ∏ j ∈ S, if a j then (1 : ℝ) else 0) := by ring
    simp_rw [hfactor]
    rw [← Finset.mul_sum]
    rw [sum_behaviorProduct_mul_trueIndicator zeta S]
    simp only [S]
    rw [show policyFactor zeta ^ (2 * (-(Q - min Q k : ℤ))) *
        (1 / policyFactor zeta) ^
          (Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val)).card =
      (1 / policyFactor zeta) ^
          (Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val)).card *
        policyFactor zeta ^ (2 * (-(Q - min Q k : ℤ))) by ring]
    rw [mul_comm]
    apply congrArg (fun y : ℝ ↦
      (1 / policyFactor zeta) ^
        (Finset.univ.filter (fun j : Fin k ↦ k - min Q k ≤ j.val)).card * y)
    rw [← zpow_ofNat, ← zpow_mul]
    congr 1
    ring
  · intro o
    have ho : (fun i ↦ (((obsPrefixActionRewardEquiv k) o).1 i,
        ((obsPrefixActionRewardEquiv k) o).2 i)) = o := by
      funext i
      apply Prod.ext <;> rfl
    rw [ho]

/-- The rare-action second moment is at most the inverse `Q`-th policy factor, uniformly in
the observed-prefix length. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma rareAction_secondMoment_le {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool) :
    (∑ o : ObsPrefix k,
      prefixMass (1 + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (1 + k)) o *
        signedDepthActionFactor zeta Q o ^ 2) ≤
      policyFactor zeta ^ (-(Q : ℤ)) := by
  rw [rareAction_secondMoment_eq ht0 hzeta hC v, card_recentWindow]
  have hLpos : 0 < policyFactor zeta := by
    rw [policyFactor]
    exact Real.exp_pos zeta
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, Real.one_le_exp_iff]
    exact hzeta.le
  have hinv : (1 / policyFactor zeta) ^ min Q k =
      policyFactor zeta ^ (-((min Q k : Nat) : ℤ)) := by
    rw [one_div, ← zpow_natCast, inv_zpow, ← zpow_neg]
  rw [hinv, ← zpow_add₀ hLpos.ne']
  apply zpow_le_zpow_right₀ hL
  have hmin : min Q k ≤ Q := min_le_left _ _
  push_cast
  omega

end CausalSmith.Stat.PomdpLatentOverlapMinimax
