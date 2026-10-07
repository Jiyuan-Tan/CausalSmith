module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CappedRisk

/-! # Monotonicity between capped and unrestricted audited minimax risks. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory

/-- Every unrestricted audited-risk range is bounded above. -/
lemma bddAbove_range_auditedRisk {T : Nat} {t0 zeta eta : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T) :
    BddAbove (Set.range (auditedRisk (t0 := t0) (zeta := zeta) eta est)) := by
  refine ⟨4, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact auditedRisk_le_four heta est i

/-- Restricting the model class by a complete-state cardinality cap cannot
increase the minimax risk. -/
lemma cappedMinimaxRisk_le_auditedMinimaxRisk (T N : Nat) {t0 zeta eta : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    cappedMinimaxRisk T N t0 zeta eta ≤ auditedMinimaxRisk T t0 zeta eta := by
  let Small := {i : HWIndex T t0 zeta // i.nX * i.nH ≤ N}
  unfold cappedMinimaxRisk auditedMinimaxRisk
  let zeroEst : AuditedEstimator T := ⟨fun _ _ _ _ _ _ => 0, by
    constructor
    · intros
      fun_prop
    · intros
      norm_num⟩
  letI : Nonempty (AuditedEstimator T) := ⟨zeroEst⟩
  refine Causalean.Stat.minimaxValue_le_minimaxValue
    (risk := fun (est : AuditedEstimator T) (i : Small) => auditedRisk eta est i.1)
    (risk' := fun (est : AuditedEstimator T) (i : HWIndex T t0 zeta) =>
      auditedRisk eta est i) ?_ ?_
  · exact Causalean.Stat.bddBelow_range_worstCaseRisk fun est i =>
      auditedRisk_nonneg est i.1
  intro est
  refine ⟨est, ?_⟩
  by_cases hsmall : Nonempty Small
  · letI : Nonempty Small := hsmall
    apply Causalean.Stat.worstCaseRisk_le
    intro i
    exact Causalean.Stat.le_worstCaseRisk
      (bddAbove_range_auditedRisk heta est) i.1
  · letI : IsEmpty Small := not_nonempty_iff.mp hsmall
    rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
    exact Causalean.Stat.worstCaseRisk_nonneg fun i => auditedRisk_nonneg est i

end CausalSmith.Stat.PomdpStateauditMinimax
