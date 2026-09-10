import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk000
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk001
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk010
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk011
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk100
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk101
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk110
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataRisk111

/-! Assembly of the exact finite full-data three-arm witness. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: k3FullDataRule_risk_le
/-- [the three-arm full data rule risk is at most property holds](goal). -/
lemma k3FullDataRule_risk_le (z : Schedule 3 3) :
    labeledRisk cDagger
      (Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit 3 ↦ qStarDesign cDagger), k3FullDataRule) z ≤
      (fullDataRuleRiskBound : ℝ) := by
  cases h00 : z 0 0 <;> cases h01 : z 0 1 <;> cases h02 : z 0 2
  all_goals first
    | exact k3FullDataRule_risk_le_000 z h00 h01 h02
    | exact k3FullDataRule_risk_le_001 z h00 h01 h02
    | exact k3FullDataRule_risk_le_010 z h00 h01 h02
    | exact k3FullDataRule_risk_le_011 z h00 h01 h02
    | exact k3FullDataRule_risk_le_100 z h00 h01 h02
    | exact k3FullDataRule_risk_le_101 z h00 h01 h02
    | exact k3FullDataRule_risk_le_110 z h00 h01 h02
    | exact k3FullDataRule_risk_le_111 z h00 h01 h02

-- @node: k3FullDataRule_boundary_risk
/-- [the three-arm full data rule boundary risk property holds](goal). -/
lemma k3FullDataRule_boundary_risk :
    labeledRisk cDagger
      (Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit 3 ↦ qStarDesign cDagger), k3FullDataRule) k3BoundarySchedule =
      (fullDataRuleRiskBound : ℝ) := by
  rw [k3FullDataRiskQ_cast]
  norm_cast
  unfold k3FullDataRiskQ
  rw [Fintype.sum_equiv (k3FullDataFin3FunEquiv (Fin 3)) _
    (fun p ↦ k3FullDataAssignmentProbQ ![p.1, p.2.1, p.2.2] *
      (k3FullDataEstimateQ ![p.1, p.2.1, p.2.2] k3BoundarySchedule -
        k3FullDataTargetQ k3BoundarySchedule) ^ 2)]
  · simp only [Fintype.sum_prod_type]
    simp [k3FullDataAssignmentProbQ, k3FullDataEstimateQ, k3FullDataTargetQ,
      k3FullDataTable, k3FullDataR1, k3FullDataS1, k3FullDataSMinus,
      obsOutcome, potentialOutcome, fullDataRuleRiskBound, k3BoundarySchedule,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      norm_num [cDaggerQ_zero, cDaggerQ_one, cDaggerQ_two]
  · intro A
    rfl

-- @node: k3FullDataRule_worstCaseRisk
/-- [the three-arm full data rule worst case risk property holds](goal). -/
lemma k3FullDataRule_worstCaseRisk :
    Causalean.Stat.worstCaseRisk
      (fun (p : Procedure 3 3 cDagger) (z : Schedule 3 3) ↦ labeledRisk cDagger p z)
      (Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit 3 ↦ qStarDesign cDagger), k3FullDataRule) =
      fullDataRuleRiskBound := by
  apply le_antisymm
  · apply Causalean.Stat.worstCaseRisk_le
    exact k3FullDataRule_risk_le
  · rw [← k3FullDataRule_boundary_risk]
    exact Causalean.Stat.le_worstCaseRisk (Set.finite_range _).bddAbove _

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
