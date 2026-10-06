module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TObservedRecordPrecisionFrontier

/-!
# Explicit precision frontier answer
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Explicit-constant precision answer and the necessary and sufficient consistency criteria.  For the stated data and conditions, [the stated conclusion holds](goal). -/
-- @node: thm:frontier-answer
theorem frontier_answer :

    (∀ n : ℕ, 4 ≤ n → -- @realizes n(population size n ≥ 4)
    ∀ d : ℕ, 1 ≤ d → d ≤ n - 1 → -- @realizes d(1 ≤ d ≤ n-1)
    ∀ q : ℝ, q ∈ Set.Icc 0 1 → -- @realizes q(known retention in [0,1])
      ENNReal.ofReal (frontierScale n d q / (2560000 * Real.pi ^ 2)) ≤ R (Fin n) d q ∧
      R (Fin n) d q ≤ worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ∧
      worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ≤
        ENNReal.ofReal (24 * frontierScale n d q))
 ∧

    (∀ (dseq : ℕ → ℕ) (qseq : ℕ → ℝ), AdmissibleSequences dseq qseq →
      ((∃ T : ∀ n, Estimator (Fin n),
        Filter.Tendsto (fun n => worstRisk (thinnedDesign (Fin n) (qseq n)) (dseq n) (T n))
          Filter.atTop (nhds 0)) ↔
      (Filter.Tendsto (fun n => (dseq n : ℝ) ^ 2 / n) Filter.atTop (nhds 0) ∧
       Filter.Tendsto (fun n => if qseq n = 0 then (⊤ : ℝ≥0∞)
         else ENNReal.ofReal (dseq n / (n * qseq n))) Filter.atTop (nhds 0))))
 ∧
(∀ (V : Type) [Fintype V] [DecidableEq V] (n d : ℕ) (q : ℝ),
  frontierRule (V := V) n d q = upperRule n d q) ∧

    (∀ n d : ℕ, 4 ≤ n → 1 ≤ d → d ≤ n - 1 →
      frontierScale n d 0 = 1 ∧ frontierScale n d 1 = min 1 ((d : ℝ) ^ 2 / n) ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 →
        (1 / 2 : ℝ) * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)) ≤ frontierScale n d q ∧
        frontierScale n d q ≤ (1 - Real.exp (-1))⁻¹ * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)))
 := by
  rcases precision_frontier_explicit with ⟨hrisk, hconsistency, helbow⟩
  refine ⟨hrisk, hconsistency, ?_, helbow⟩
  intro V _ _ n d q
  rfl

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
