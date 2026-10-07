module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.UnitOverlapLower

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory

lemma minimaxValue_le_of_uniform {E Θ : Type*} (risk : E → Θ → ℝ)
    (hnonneg : ∀ e θ, 0 ≤ risk e θ) (e : E) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ θ, risk e θ ≤ c) : Causalean.Stat.minimaxValueReal risk ≤ c := by
  calc
    Causalean.Stat.minimaxValueReal risk ≤ Causalean.Stat.worstCaseRiskReal risk e :=
      Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hnonneg e
    _ ≤ c := by
      by_cases hidx : Nonempty Θ
      · letI : Nonempty Θ := hidx
        exact Causalean.Stat.worstCaseRisk_le h
      · letI : IsEmpty Θ := not_nonempty_iff.mp hidx
        rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
        exact hc

lemma invarianceMinimaxRisk_upper_iw {T : Nat} (hT : 1 ≤ T)
    {t0 zeta eta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    invarianceMinimaxRisk T t0 zeta eta ≤
      (policyFactor zeta + 4 / (1 - mixingAlpha t0)) / (T : ℝ) := by
  let InvIndex := {i : HWIndex T t0 zeta // InvarianceClass t0 zeta i.raw}
  let risk : AuditedEstimator T → InvIndex → ℝ := fun est q => auditedRisk eta est q.1
  unfold invarianceMinimaxRisk
  change Causalean.Stat.minimaxValueReal risk ≤ _
  apply minimaxValue_le_of_uniform (E := AuditedEstimator T) (Θ := InvIndex)
    risk (fun est q => auditedRisk_nonneg est q.1) (iwAuditedEstimator T)
  · have hden : 0 < 1 - mixingAlpha t0 := by
      exact sub_pos.mpr
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.mixingAlpha_lt_one ht0)
    exact div_nonneg (add_nonneg (by unfold policyFactor; positivity)
      (div_nonneg (by norm_num) hden.le)) (by exact_mod_cast (Nat.zero_le T))
  · intro q
    change auditedRisk eta (iwAuditedEstimator T) q.1 ≤ _
    change Causalean.Stat.sqRisk (auditedLaw eta q.1.raw)
      (iwEstimator q.1.raw.b q.1.raw.e) (targetValue q.1.raw) ≤ _
    exact audited_iw_invariance_risk_le hT q.1.raw q.2
      q.1.nX_pos q.1.nH_pos eta heta

end CausalSmith.Stat.PomdpStateauditMinimax
