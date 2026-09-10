import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Inference
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T2_SharpInterval

/-! # Finite-sample confidence interval for the whole identified set -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped ENNReal
open MeasureTheory Set

variable {O T OBlind Ω : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]
  [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSingletonClass O]
  {μ : Measure Ω} {P : Measure O}

/-- Bonferroni propagation of the exact cell intervals covers the entire
identified interval, and on the true-law-in-box event both implementation
optima are attained. -/
-- @node: prop:finite-sample-whole-set-implementation
theorem finite_sample_whole_set_implementation
    (G : SLCCIncidence O T OBlind) (p : O → ℝ)
    (S : Causalean.Stat.IIDSample Ω O μ P)
    (hIID : IidFiniteSampling μ P S G p)
    (n : ℕ) (hn : 1 ≤ n) (alpha : ℝ) (hAlpha : 0 < alpha ∧ alpha < 1) :
    ENNReal.ofReal (1 - alpha) ≤
      μ {ω | Set.Icc (lowerEndpoint G p) (upperEndpoint G p) ⊆
        wholeSetConfidenceInterval G n (ENNReal.ofReal alpha)
          (multinomialCounts S n ω)} ∧
    (∀ ω, (∃ q ∈ simultaneousConfidenceBox n (ENNReal.ofReal alpha)
          (multinomialCounts S n ω), (fun o => (q o : ℝ)) = p) →
      (simultaneousConfidenceBox n (ENNReal.ofReal alpha)
          (multinomialCounts S n ω) ∩
        {q | (fun o => (q o : ℝ)) ∈ observablePolytope G}).Nonempty ∧
      (∃ w ∈ stdSimplex ℝ T,
        ∃ q ∈ simultaneousConfidenceBox n (ENNReal.ofReal alpha)
          (multinomialCounts S n ω),
          G.B.mulVec w = (fun o => (q o : ℝ)) ∧
          targetFunctional G w = sInf (wholeSetConfidenceInterval G n
            (ENNReal.ofReal alpha) (multinomialCounts S n ω))) ∧
      (∃ w ∈ stdSimplex ℝ T,
        ∃ q ∈ simultaneousConfidenceBox n (ENNReal.ofReal alpha)
          (multinomialCounts S n ω),
          G.B.mulVec w = (fun o => (q o : ℝ)) ∧
          targetFunctional G w = sSup (wholeSetConfidenceInterval G n
            (ENNReal.ofReal alpha) (multinomialCounts S n ω)))) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
