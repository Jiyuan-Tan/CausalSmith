import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepth
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FinitePrefixMarginal
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.TerminalPosteriorBound

set_option linter.style.longLine false

/-! # Finite observed-prefix filter for the signed-depth family -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The finite observed action/reward prefix strictly before epoch `t`. -/
abbrev ObsPrefix (t : Nat) := Fin t → Bool × Fin 2
  -- @realizes \(\mathcal F_{t-1}^{\mathrm{obs}}\)(finite observed-prefix carrier)

/-- Project a finite path to its action/reward prefix. -/
def observedPrefix {T nX nH : Nat} (t : Fin T)
    (tau : FiniteTrajectory T nX nH 2) : ObsPrefix t.val :=
  fun j ↦ tau.2 (prefixIndex t j)

/-- Taking real masses in a generated finite model recovers its chronological real path weight. [the stated conclusion](goal). -/
lemma finiteRewardModel_law_toReal {T nX nH nR : Nat}
    (M : FiniteRewardModel T nX nH nR) (tau : FiniteTrajectory T nX nH nR) :
    (M.law tau).toReal =
      finitePathWeightFrom M.kernel (fun s ↦ (M.init s).toReal) M.b tau := by
  rw [M.law_generated tau, ENNReal.toReal_mul, ENNReal.toReal_prod]
  unfold finitePathWeightFrom
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [ENNReal.toReal_mul]

/-- At the canonical cut after `k` epochs, the public observed prefix is the chronological fixed
prefix used by finite-prefix marginalization. [the h U condition](hyp:hU). [the stated conclusion](goal). -/
lemma observedPrefix_eq_finiteObservedPrefixExtra {U k nX nH : Nat} (hU : 0 < U)
    (tau : FiniteTrajectory (U + k) nX nH 2) :
    observedPrefix (⟨k, by omega⟩ : Fin (U + k)) tau =
      finiteObservedPrefixExtra U k tau := by
  funext j
  rfl

/-- One epoch before the suffix, the public prefix is the restriction of the chronological
`k+1`-coordinate prefix to its first `k` coordinates. [the stated conclusion](goal). -/
lemma observedPrefix_eq_finiteObservedPrefixBeforeNext {U k nX nH : Nat}
    (tau : FiniteTrajectory (U + (k + 1)) nX nH 2) :
    observedPrefix (⟨k, by omega⟩ : Fin (U + (k + 1))) tau =
      fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc := by
  funext j
  rfl

/-- Prefix probability under a signed-depth finite witness. -/
noncomputable def prefixMass (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) : ℝ :=
  ∑ tau : FiniteTrajectory T 1 (2 * (Q + 1)) 2,
    if observedPrefix t tau = o then (signedDepthFinite T t0 zeta C Q v).law tau |>.toReal else 0

/-- Joint prefix/terminal-depth probability. -/
noncomputable def terminalPrefixMass (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) : ℝ :=
  ∑ tau : FiniteTrajectory T 1 (2 * (Q + 1)) 2,
    if observedPrefix t tau = o ∧ latentDepth Q (tau.1 t.castSucc).2 = Q
    then (signedDepthFinite T t0 zeta C Q v).law tau |>.toReal else 0

/-- A signed-depth observed-prefix mass is exactly its chronological finite state-prefix
likelihood sum. [the h U condition](hyp:hU). [the stated conclusion](goal). -/
lemma prefixMass_eq_finiteFixedPrefixWeight_sum (U k : Nat) (hU : 0 < U)
    (t0 zeta C : ℝ) (Q : Nat) (v : Bool) (o : ObsPrefix k) :
    prefixMass (U + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (U + k)) o =
      ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        finiteFixedPrefixWeight
          (signedDepthFinite (U + k) t0 zeta C Q v).kernel
          (fun s ↦ ((signedDepthFinite (U + k) t0 zeta C Q v).init s).toReal)
          (signedDepthFinite (U + k) t0 zeta C Q v).b o sigma := by
  classical
  unfold prefixMass
  simp_rw [finiteRewardModel_law_toReal,
    observedPrefix_eq_finiteObservedPrefixExtra hU]
  exact sum_finitePathWeightFrom_fixedPrefix
    (signedDepthFinite (U + k) t0 zeta C Q v).kernel
    (signedDepthFinite (U + k) t0 zeta C Q v).b k U
    (fun s ↦ ((signedDepthFinite (U + k) t0 zeta C Q v).init s).toReal) o

/-- The terminal-depth joint prefix mass is the same likelihood sum restricted by the exact
terminal-depth predicate at the cut state. [the h U condition](hyp:hU). [the stated conclusion](goal). -/
lemma terminalPrefixMass_eq_finiteFixedPrefixWeight_sum (U k : Nat) (hU : 0 < U)
    (t0 zeta C : ℝ) (Q : Nat) (v : Bool) (o : ObsPrefix k) :
    terminalPrefixMass (U + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (U + k)) o =
      ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        if latentDepth Q (sigma (Fin.last k)).2 = Q then
          finiteFixedPrefixWeight
            (signedDepthFinite (U + k) t0 zeta C Q v).kernel
            (fun s ↦ ((signedDepthFinite (U + k) t0 zeta C Q v).init s).toReal)
            (signedDepthFinite (U + k) t0 zeta C Q v).b o sigma else 0 := by
  classical
  unfold terminalPrefixMass
  simp_rw [finiteRewardModel_law_toReal,
    observedPrefix_eq_finiteObservedPrefixExtra hU]
  exact sum_finitePathWeightFrom_fixedPrefix_indicator
    (signedDepthFinite (U + k) t0 zeta C Q v).kernel
    (signedDepthFinite (U + k) t0 zeta C Q v).b k U
    (fun s ↦ ((signedDepthFinite (U + k) t0 zeta C Q v).init s).toReal) o
    (fun s ↦ latentDepth Q s.2 = Q)

/-- Prefix mass is the sum of the unnormalized signed-depth filter over hidden states. [the h U condition](hyp:hU). [the stated conclusion](goal). -/
lemma prefixMass_eq_sum_signedDepthFilterMass (U k : Nat) (hU : 0 < U)
    (t0 zeta C : ℝ) (Q : Nat) (v : Bool) (o : ObsPrefix k) :
    prefixMass (U + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (U + k)) o =
      ∑ h : Fin (2 * (Q + 1)), signedDepthFilterMass (U + k) t0 zeta C Q v o h := by
  rw [prefixMass_eq_finiteFixedPrefixWeight_sum U k hU]
  rw [← sum_finiteTerminalStatePrefixMass]
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp [signedDepthFilterMass]

/-- Terminal-prefix mass is the terminal-depth restriction of the unnormalized hidden filter. [the h U condition](hyp:hU). [the stated conclusion](goal). -/
lemma terminalPrefixMass_eq_sum_signedDepthFilterMass (U k : Nat) (hU : 0 < U)
    (t0 zeta C : ℝ) (Q : Nat) (v : Bool) (o : ObsPrefix k) :
    terminalPrefixMass (U + k) t0 zeta C Q v (⟨k, by omega⟩ : Fin (U + k)) o =
      ∑ h : Fin (2 * (Q + 1)),
        if latentDepth Q h = Q then signedDepthFilterMass (U + k) t0 zeta C Q v o h else 0 := by
  rw [terminalPrefixMass_eq_finiteFixedPrefixWeight_sum U k hU]
  rw [← sum_finiteTerminalStatePrefixMass_indicator
    (P := fun s : JointState 1 (2 * (Q + 1)) ↦ latentDepth Q s.2 = Q)]
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp [signedDepthFilterMass]

/-- A finite observed prefix has nonnegative mass. [the stated conclusion](goal). -/
lemma prefixMass_nonneg (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) :
    0 ≤ prefixMass T t0 zeta C Q v t o := by
  classical
  unfold prefixMass
  exact Finset.sum_nonneg fun tau _ ↦ by split_ifs <;> positivity

/-- The joint terminal-depth/prefix mass is nonnegative. [the stated conclusion](goal). -/
lemma terminalPrefixMass_nonneg (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) :
    0 ≤ terminalPrefixMass T t0 zeta C Q v t o := by
  classical
  unfold terminalPrefixMass
  exact Finset.sum_nonneg fun tau _ ↦ by split_ifs <;> positivity

/-- Restricting a prefix event to terminal depth cannot increase its mass. [the stated conclusion](goal). -/
lemma terminalPrefixMass_le_prefixMass (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) :
    terminalPrefixMass T t0 zeta C Q v t o ≤
      prefixMass T t0 zeta C Q v t o := by
  classical
  unfold terminalPrefixMass prefixMass
  apply Finset.sum_le_sum
  intro tau _
  by_cases hp : observedPrefix t tau = o
  · simp only [hp, true_and, if_true]
    split_ifs <;> first | rfl | positivity
  · simp [hp]

/-- The record collecting the three finite observed-filter quantities. -/
structure FilterQuantities (T Q : Nat) where
  prefixLen : Fin T → Nat
  terminalPosterior : (t : Fin T) → ObsPrefix t.val → ℝ
  actionFactor : (t : Fin T) → ObsPrefix t.val → ℝ

-- @node: def:filter-quantities
/-- The prefix length, predictive terminal posterior, and rare-action-history factor. -/
noncomputable def filterQuantities (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool) :
    FilterQuantities T Q where
  prefixLen t := min Q t.val
    -- @realizes \(\ell_t\)(min(Q,t-1))
  terminalPosterior t o :=
    terminalPrefixMass T t0 zeta C Q v t o / prefixMass T t0 zeta C Q v t o
    -- @realizes \(q_t^v\)(finite conditional terminal-depth probability)
  actionFactor t o :=
    policyFactor zeta ^ (-(Q - min Q t.val : ℤ)) *
      ∏ j ∈ Finset.univ.filter (fun j : Fin t.val ↦ t.val - min Q t.val ≤ j.val),
        if (o j).1 then 1 else 0
    -- @realizes \(a_t^{(Q)}\)(rare-action history factor)

/-- The totalized terminal posterior lies in `[0,1]`, including zero-mass prefixes. [the stated conclusion](goal). -/
lemma terminalPosterior_mem_Icc (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) :
    (filterQuantities T t0 zeta C Q v).terminalPosterior t o ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (terminalPrefixMass_nonneg T t0 zeta C Q v t o)
      (prefixMass_nonneg T t0 zeta C Q v t o)
  · by_cases ho : 0 < prefixMass T t0 zeta C Q v t o
    · exact (div_le_one ho).2
        (terminalPrefixMass_le_prefixMass T t0 zeta C Q v t o)
    · have hprefix : prefixMass T t0 zeta C Q v t o = 0 := by
        exact le_antisymm (le_of_not_gt ho) (prefixMass_nonneg T t0 zeta C Q v t o)
      have hterminal : terminalPrefixMass T t0 zeta C Q v t o = 0 := by
        apply le_antisymm
        · simpa [hprefix] using terminalPrefixMass_le_prefixMass T t0 zeta C Q v t o
        · exact terminalPrefixMass_nonneg T t0 zeta C Q v t o
      simp [filterQuantities, hprefix, hterminal]

/-- Conditional mean of the next observed real reward given a finite prefix. -/
noncomputable def conditionalRewardMean (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) : ℝ :=
  (∑ tau : FiniteTrajectory T 1 (2 * (Q + 1)) 2,
    if observedPrefix t tau = o then
      (signedDepthFinite T t0 zeta C Q v).rew (tau.2 t).2 *
        ((signedDepthFinite T t0 zeta C Q v).law tau).toReal
    else 0) / prefixMass T t0 zeta C Q v t o

/-- At a canonical cut with at least one remaining epoch, the exact finite conditional reward
mean is the signed amplitude times the action-history factor and terminal posterior. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma conditionalRewardMean_signedDepth {U k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : ObsPrefix k) :
    conditionalRewardMean (U + (k + 1)) t0 zeta C Q v
        (⟨k, by omega⟩ : Fin (U + (k + 1))) o =
      signedValue v * c0 t0 * epsC C *
        (filterQuantities (U + (k + 1)) t0 zeta C Q v).actionFactor
          (⟨k, by omega⟩ : Fin (U + (k + 1))) o *
        (filterQuantities (U + (k + 1)) t0 zeta C Q v).terminalPosterior
          (⟨k, by omega⟩ : Fin (U + (k + 1))) o := by
  have hnum :
      (∑ tau : FiniteTrajectory (U + (k + 1)) 1 (2 * (Q + 1)) 2,
        if observedPrefix (⟨k, by omega⟩ : Fin (U + (k + 1))) tau = o then
          (signedDepthFinite (U + (k + 1)) t0 zeta C Q v).rew (tau.2 ⟨k, by omega⟩).2 *
            ((signedDepthFinite (U + (k + 1)) t0 zeta C Q v).law tau).toReal
        else 0) =
      signedValue v * c0 t0 *
        ∑ h : Fin (2 * (Q + 1)),
          if latentDepth Q h = Q then signedValue (latentSign Q h) *
            signedDepthFilterMass (U + (k + 1)) t0 zeta C Q v o h else 0 := by
    calc
      _ = ∑ tau : FiniteTrajectory (U + (k + 1)) 1 (2 * (Q + 1)) 2,
          if (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o then
            finitePathWeightFrom
              (signedDepthFinite (U + (k + 1)) t0 zeta C Q v).kernel
              (fun s ↦ ((signedDepthFinite (U + (k + 1)) t0 zeta C Q v).init s).toReal)
              (signedDepthFinite (U + (k + 1)) t0 zeta C Q v).b tau *
                (if (finiteObservedPrefixExtra U (k + 1) tau (Fin.last k)).2 = 0 then
                  (-1 : ℝ) else 1)
          else 0 := by
            apply Finset.sum_congr rfl
            intro tau _
            rw [observedPrefix_eq_finiteObservedPrefixBeforeNext,
              finiteRewardModel_law_toReal]
            by_cases ho :
                (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o
            · simp [ho, signedDepthFinite]
              have hr : tau.2 (⟨k, by omega⟩ : Fin (U + (k + 1))) =
                  finiteObservedPrefixExtra U (k + 1) tau (Fin.last k) := by
                rfl
              rw [hr]
            · simp [ho]
      _ = _ := signedDepth_prefix_nextRewardNumerator ht0 hzeta hC v o
  rw [conditionalRewardMean, hnum]
  rw [signedDepth_terminalMass_invariant ht0 hzeta hC]
  have hterminal :
      terminalPrefixMass (U + (k + 1)) t0 zeta C Q v
          (⟨k, by omega⟩ : Fin (U + (k + 1))) o =
        ∑ h : Fin (2 * (Q + 1)),
          if latentDepth Q h = Q then
            signedDepthFilterMass (U + (k + 1)) t0 zeta C Q v o h else 0 := by
    have hterm := terminalPrefixMass_eq_sum_signedDepthFilterMass (U + 1) k (by omega)
      t0 zeta C Q v o
    convert hterm using 1
    · congr 1
      · omega
      · apply (Fin.heq_ext_iff (by omega)).2
        rfl
    · apply Finset.sum_congr rfl
      intro h _
      by_cases hQ : latentDepth Q h = Q <;> simp [hQ]
      congr 1 <;> omega
  rw [← hterminal]
  simp only [filterQuantities, signedDepthActionFactor]
  ring

/-- The exact signed-depth conditional reward identity holds at every finite horizon and epoch. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma conditionalRewardMean_signedDepth_all {T Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) :
    conditionalRewardMean T t0 zeta C Q v t o =
      signedValue v * c0 t0 * epsC C *
        (filterQuantities T t0 zeta C Q v).actionFactor t o *
        (filterQuantities T t0 zeta C Q v).terminalPosterior t o := by
  rcases t with ⟨k, hk⟩
  obtain ⟨U, hT⟩ : ∃ U : Nat, T = U + (k + 1) := ⟨T - (k + 1), by omega⟩
  subst T
  exact conditionalRewardMean_signedDepth (U := U) (Q := Q) ht0 hzeta hC v o

end CausalSmith.Stat.PomdpLatentOverlapMinimax
