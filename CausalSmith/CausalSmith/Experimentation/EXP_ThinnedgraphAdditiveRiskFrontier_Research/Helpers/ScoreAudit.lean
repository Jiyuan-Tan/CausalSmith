module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.AuditVariance
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.OracleVariance
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ScoreMean

/-!
# Exact audit score moments
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unbiasedness, the exact assignment-audit variance identity, and the explicit oracle bound.  [For the stated data and conditions](hyp:D,θ,d,q,hn,hd,hdu,hclass,ha,hw,hi,hq), [the stated conclusion holds](goal). -/
-- @node: lem:score-audit
lemma score_audit (D : Measure (Assign V × Audit V)) (θ : Schedule V) (d : ℕ) (q : ℝ)
    (hn : 4 ≤ Fintype.card V) (hd : 1 ≤ d) (hdu : d ≤ Fintype.card V - 1)
    (hclass : ScheduleClass θ d) (ha : AssignmentLaw D) (hw : AuditLaw D q)
    (hi : DesignIndependent D) (hq : 0 < q) :
    (∫ ω, auditScore q (recordOf θ ω) ∂D) = tte θ ∧
    ProbabilityTheory.variance (fun ω => auditScore q (recordOf θ ω)) D =
      ProbabilityTheory.variance (oracleScore θ) (halfBernoulli V) +
        4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) *
          ∑ i, (inNbhd θ i).card *
            ∫ z, (potentialOutcome θ i z) ^ 2 ∂(halfBernoulli V) ∧
    ProbabilityTheory.variance (oracleScore θ) (halfBernoulli V) ≤
      5 * ((d : ℝ) + 1) ^ 2 / Fintype.card V := by
  refine ⟨integral_auditScore_eq_tte D θ q ha hw hi hq, ?_,
    oracle_variance_le θ d hn hd hclass⟩
  exact variance_auditScore_eq_oracle_add D θ q (by omega) ha hw hi hq

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
