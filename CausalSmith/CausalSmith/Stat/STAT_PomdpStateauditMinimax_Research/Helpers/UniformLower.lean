module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.TCloneBudgetFrontier
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.MinimaxMonotonicity

/-! # Cardinality-unrestricted audited minimax lower bound. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

/-- The signed-depth capped converse embeds into the unrestricted model class,
uniformly over the audit probability. -/
lemma auditedMinimaxRisk_uniform_lower (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ c : ℝ, 0 < c ∧ ∀ (T : Nat), 1 ≤ T → ∀ (eta : ℝ),
      eta ∈ Set.Icc (0 : ℝ) 1 →
      c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
        auditedMinimaxRisk T t0 zeta eta := by
  obtain ⟨B0, hconst⟩ := signedDepthConstantAtTwo_exists ht0 hzeta
  have hdelta : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (3 / 8) := by norm_num
  obtain ⟨c, hc, hconv⟩ :=
    capped_signedDepth_converse ht0 hzeta hconst (1 / 8) hdelta
  refine ⟨c, hc, ?_⟩
  intro T hT eta heta
  obtain ⟨m, hm, hcollision⟩ :=
    frontier_cloneBudget_exists T eta (1 / 8) heta (by norm_num)
  let N := signedDepthCardinality T t0 zeta B0 * m
  have hlower : c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
      cappedMinimaxRisk T N t0 zeta eta := by
    exact hconv T N m eta hT heta hm hcollision (by simp [N])
  exact hlower.trans (cappedMinimaxRisk_le_auditedMinimaxRisk T N heta)

end CausalSmith.Stat.PomdpStateauditMinimax
