module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.UniformLower
public import Causalean.Stat.Minimax.BretagnolleHuber
public import Causalean.Stat.Minimax.HellingerAffinity

/-! # Cardinality-uniform audited POMDP minimax theorem. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory

-- @node: thm:hu-wager-uniform-audit-minimax
/-- For every positive mixing and policy-overlap scale, two constants independent of
state and action cardinalities, horizon, and audit rate sandwich the audited minimax
risk at the hidden-state rate. PHIW attains the upper bound for every class member. -/
theorem hu_wager_uniform_audit_minimax (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ c A : ℝ, 0 < c ∧ c ≤ A ∧
      ∀ (T : Nat), 1 ≤ T → ∀ (eta : ℝ), eta ∈ Set.Icc (0 : ℝ) 1 →
        c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
          auditedMinimaxRisk T t0 zeta eta ∧
        auditedMinimaxRisk T t0 zeta eta ≤
          A * (T : ℝ) ^ (-rateExponent t0 zeta) ∧
        (∀ i : HWIndex T t0 zeta,
          Causalean.Stat.sqRisk (auditedLaw eta i.raw)
            (phiwEstimator t0 zeta i.raw.b i.raw.e)
            (targetValue i.raw) ≤
              A * (T : ℝ) ^ (-rateExponent t0 zeta)) := by
  obtain ⟨c, hc, hlower⟩ := auditedMinimaxRisk_uniform_lower t0 zeta ht0 hzeta
  obtain ⟨A, hA, hupper⟩ := auditedMinimaxRisk_upper_rate ht0 hzeta
  let A' := max A c
  refine ⟨c, A', hc, le_max_right _ _, ?_⟩
  intro T hT eta heta
  obtain ⟨hminUpper, hphiw⟩ := hupper T hT eta heta
  have hrate0 : 0 ≤ (T : ℝ) ^ (-rateExponent t0 zeta) :=
    Real.rpow_nonneg (Nat.cast_nonneg T) _
  refine ⟨hlower T hT eta heta, ?_, ?_⟩
  · exact hminUpper.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate0)
  · intro i
    exact (hphiw i).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate0)

end CausalSmith.Stat.PomdpStateauditMinimax
