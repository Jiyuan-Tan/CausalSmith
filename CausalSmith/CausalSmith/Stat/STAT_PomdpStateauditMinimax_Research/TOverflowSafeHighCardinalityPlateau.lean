module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.TCloneBudgetFrontier
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.THuWagerUniformAuditMinimax
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PlateauAsymptotic

/-! # High-cardinality plateau for the audited POMDP minimax risk. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open Filter

-- @node: cloneBudget_zero_audit
/-- With no audits, a single clone has zero collision cost and is the least budget. -/
lemma cloneBudget_zero_audit (T : Nat) (delta : ℝ)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    cloneBudget T 0 delta hdelta = 1 := by
  have henv : collisionEnvelope T 0 1 = 0 := by
    unfold collisionEnvelope
    rw [Finset.sum_eq_single 0]
    · simp
    · intro r hr hr0
      simp [hr0]
    · simp
  have hmem : 1 ∈ {m : Nat | 1 ≤ m ∧ collisionEnvelope T 0 m ≤ delta} := by
    simp [henv, hdelta.1.le]
  have hle : cloneBudget T 0 delta hdelta ≤ 1 := by
    exact Nat.sInf_le hmem
  have hge : 1 ≤ cloneBudget T 0 delta hdelta := by
    exact (Nat.sInf_mem ⟨1, hmem⟩).1
  omega

/-- The minimax part of the plateau follows from the signed-depth converse at
the collision budget and the cardinality-uniform PHIW upper bound. -/
lemma capped_plateau_risk_sandwich (t0 zeta B0 delta0 : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hconst : SignedDepthConstantAtTwo t0 zeta B0)
    (hdelta0 : delta0 ∈ Set.Ioo (0 : ℝ) (3 / 8)) :
    ∃ c A : ℝ, 0 < c ∧ c ≤ A ∧
      ∀ (T N : Nat) (eta : ℝ), 1 ≤ T → eta ∈ Set.Icc (0 : ℝ) 1 →
        signedDepthCardinality T t0 zeta B0 *
          cloneBudget T eta delta0
            ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩ ≤ N →
        c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
            cappedMinimaxRisk T N t0 zeta eta ∧
          cappedMinimaxRisk T N t0 zeta eta ≤
            A * (T : ℝ) ^ (-rateExponent t0 zeta) := by
  obtain ⟨c, hc, hlower⟩ :=
    capped_signedDepth_converse ht0 hzeta hconst delta0 hdelta0
  obtain ⟨Au, hAu, hupper⟩ := auditedMinimaxRisk_upper_rate ht0 hzeta
  let A := max Au c
  refine ⟨c, A, hc, le_max_right _ _, ?_⟩
  intro T N eta hT heta hcap
  let hdelta : delta0 ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩
  have hbudget := cloneBudget_minimal_of_exists T eta delta0 hdelta
    (frontier_cloneBudget_exists T eta delta0 heta hdelta0.1)
  have hlo := hlower T N (cloneBudget T eta delta0 hdelta) eta hT heta
    hbudget.1 hbudget.2.1 hcap
  have hup := (cappedMinimaxRisk_le_auditedMinimaxRisk T N heta).trans
    (hupper T hT eta heta).1
  have hrate0 : 0 ≤ (T : ℝ) ^ (-rateExponent t0 zeta) :=
    Real.rpow_nonneg (Nat.cast_nonneg T) _
  exact ⟨hlo, hup.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate0)⟩

-- @node: prop:overflow-safe-high-cardinality-plateau
/-- At the collision-budget cap, the cardinality-restricted minimax risk has the
same uniform hidden-state rate. The sufficient threshold has logarithmic size at
zero audits and squared expected-audit size times a logarithm along large-audit
sequences; no additional order-horizon floor is imposed. -/
theorem overflow_safe_high_cardinality_plateau (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ B0 : ℝ, SignedDepthConstantAtTwo t0 zeta B0 ∧
      ∀ delta0 : ℝ, ∀ hdelta0 : delta0 ∈ Set.Ioo (0 : ℝ) (3 / 8),
        ∃ c A cLog CLog cAud CAud : ℝ,
          0 < c ∧ c ≤ A ∧ 0 < cLog ∧ cLog ≤ CLog ∧
          0 < cAud ∧ cAud ≤ CAud ∧
          (∀ (T N : Nat) (eta : ℝ), 1 ≤ T →
            eta ∈ Set.Icc (0 : ℝ) 1 →
            signedDepthCardinality T t0 zeta B0 *
              cloneBudget T eta delta0 ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩ ≤ N →
              c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
                cappedMinimaxRisk T N t0 zeta eta ∧
              cappedMinimaxRisk T N t0 zeta eta ≤
                A * (T : ℝ) ^ (-rateExponent t0 zeta)) ∧
          (∀ T : Nat, 1 ≤ T →
            cloneBudget T 0 delta0 ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩ = 1) ∧
          (∀ T : Nat, 2 ≤ T →
            cLog * Real.log T ≤ (signedDepthCardinality T t0 zeta B0 : ℝ) ∧
            (signedDepthCardinality T t0 zeta B0 : ℝ) ≤ CLog * Real.log T) ∧
          (∀ (Tseq : Nat → Nat) (etaseq : Nat → ℝ),
            (∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1) →
            Tendsto (fun j => (Tseq j : ℝ) * etaseq j) atTop atTop →
            Filter.Eventually (fun j =>
              cAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j) ≤
                ((signedDepthCardinality (Tseq j) t0 zeta B0 *
                  cloneBudget (Tseq j) (etaseq j) delta0
                    ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩ : Nat) : ℝ) ∧
              ((signedDepthCardinality (Tseq j) t0 zeta B0 *
                cloneBudget (Tseq j) (etaseq j) delta0
                  ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩ : Nat) : ℝ) ≤
                CAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j))
              atTop) := by
  obtain ⟨B0, hconst⟩ := signedDepthConstantAtTwo_exists ht0 hzeta
  obtain ⟨hB0, _⟩ := signedDepthConstantAtTwo_spec hconst
  refine ⟨B0, hconst, ?_⟩
  intro delta0 hdelta0
  obtain ⟨c, A, hc, hcA, hrisk⟩ :=
    capped_plateau_risk_sandwich t0 zeta B0 delta0 ht0 hzeta hconst hdelta0
  obtain ⟨cLog, CLog, hcLog, hcLogC, hlog⟩ :=
    signedDepthCardinality_log_bounds ht0 hzeta hB0
  let hdelta : delta0 ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩
  obtain ⟨cAud, CAud, hcAud, hcAudC, haud⟩ :=
    signedDepthCardinality_mul_cloneBudget_eventually_bounds
      ht0 hzeta hB0 hdelta
  refine ⟨c, A, cLog, CLog, cAud, CAud, hc, hcA, hcLog, hcLogC,
    hcAud, hcAudC, hrisk, ?_, hlog, ?_⟩
  · intro T _
    exact cloneBudget_zero_audit T delta0 hdelta
  · intro Tseq etaseq heta hmean
    exact haud Tseq etaseq heta hmean

end CausalSmith.Stat.PomdpStateauditMinimax
