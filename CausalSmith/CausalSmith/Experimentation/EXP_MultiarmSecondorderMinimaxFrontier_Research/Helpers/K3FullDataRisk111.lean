import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataWitnessBase

/-! One response-type slice of the exact full-data risk certificate. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

set_option maxHeartbeats 0 in
-- @node: k3FullDataRule_risk_le_111
/-- [the stated side condition holds](hyp:h00), [the stated side condition holds](hyp:h01), [the stated side condition holds](hyp:h02), [the three-arm full data rule risk is at most 111](goal). -/
lemma k3FullDataRule_risk_le_111 (z : Schedule 3 3)
    (h00 : z 0 0 = true)
    (h01 : z 0 1 = true)
    (h02 : z 0 2 = true) :
    labeledRisk cDagger
      (Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit 3 ↦ qStarDesign cDagger), k3FullDataRule) z ≤
      (fullDataRuleRiskBound : ℝ) := by
  rw [k3FullDataRiskQ_cast]
  norm_cast
  unfold k3FullDataRiskQ
  rw [Fintype.sum_equiv (k3FullDataFin3FunEquiv (Fin 3)) _
    (fun p ↦ k3FullDataAssignmentProbQ ![p.1, p.2.1, p.2.2] *
      (k3FullDataEstimateQ ![p.1, p.2.1, p.2.2] z - k3FullDataTargetQ z) ^ 2)]
  · simp only [Fintype.sum_prod_type]
    cases h10 : z 1 0 <;> cases h11 : z 1 1 <;> cases h12 : z 1 2 <;>
      cases h20 : z 2 0 <;> cases h21 : z 2 1 <;> cases h22 : z 2 2 <;>
      simp [k3FullDataAssignmentProbQ, k3FullDataEstimateQ, k3FullDataTargetQ,
        k3FullDataTable, k3FullDataR1, k3FullDataS1, k3FullDataSMinus,
        obsOutcome, potentialOutcome, fullDataRuleRiskBound, Fin.sum_univ_succ,
        Fin.prod_univ_succ, h00, h01, h02, h10, h11, h12, h20, h21, h22] <;>
      norm_num [cDaggerQ_zero, cDaggerQ_one, cDaggerQ_two]
  · intro A
    rfl

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
