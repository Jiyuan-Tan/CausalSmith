import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Witnesses
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessSigns

/-!
# Sparse and cancellation witness certificate

The theorem certifies both explicit three-node constructions, the quantitative
sparse separation, and the exact cancellation example.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: prop:sparse-witness-certificate
/-- The reflected sparse and cancellation mechanisms satisfy the model atoms; the sparse witness
has the certified moment and Gaussian-MMD gaps, while the cancellation ratio law is unchanged. -/
theorem sparse_witness_certificate (s : SignVector 3) :
    let sparse := sparseWitness s
    let cancel := cancellationWitness s
    let Ws := canonicalObservedWorld threeNodeDAG sparse (Equiv.refl (Fin 3))
    let Wc := canonicalObservedWorld threeNodeDAG cancel (Equiv.refl (Fin 3))
    PositiveNormalizedSmoothMechanisms threeNodeDAG sparse ∧
    FixedOwnDerivativeSign threeNodeDAG s sparse ∧
    Faithfulness threeNodeDAG sparse ∧
    (∀ k i, ContDiffOn ℝ k (sparse.p i) (latentCube 3)) ∧
    (∀ k i, ContDiffOn ℝ k (sparse.q i) (Set.Icc (0 : ℝ) 1)) ∧
    PositiveNormalizedSmoothMechanisms threeNodeDAG cancel ∧
    FixedOwnDerivativeSign threeNodeDAG s cancel ∧
    Faithfulness threeNodeDAG cancel ∧
    (∀ k i, ContDiffOn ℝ k (cancel.p i) (latentCube 3)) ∧
    (∀ k i, ContDiffOn ℝ k (cancel.q i) (Set.Icc (0 : ℝ) 1)) ∧
    (3 / 10000 : ℝ) <
      (∫ x, (Ws.ratio 1 x) ^ 2 ∂Ws.law 0) -
        ∫ x, (Ws.ratio 1 x) ^ 2 ∂Ws.law (Fin.succ 0) ∧
    (5 / 100000000 : ℝ) < populationDiscrepancy gaussianFeatureMap Ws 0 1 ∧
    observationalRatioLaw Wc 1 = interventionalRatioLaw Wc 0 1 ∧
    populationDiscrepancy gaussianFeatureMap Wc 0 1 = 0 := by sorry

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
