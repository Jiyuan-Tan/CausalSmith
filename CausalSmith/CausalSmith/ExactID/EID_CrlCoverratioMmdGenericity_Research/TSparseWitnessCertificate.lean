module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Witnesses
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessSigns
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessQuantitative
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessTransport
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessFaithfulness
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessAssembly
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessFaithfulnessAssembly
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessCancellationFaithfulness
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessMomentMmdAssembly

/-!
# Sparse and cancellation witness certificate

The theorem certifies both explicit three-node constructions, quantitative
sparse separation, and the exact cancellation example.
-/

public section

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- The already established witness lemmas assemble both faithfulness assertions, all regularity,
and exact cancellation.  This leaves only the quantitative sparse moment/MMD estimates to the
final assembly.  [the stated conclusion](goal) follows. -/
-- @node: explicitWitness_structural_cancellation_certificate
lemma explicitWitness_structural_cancellation_certificate (s : SignVector 3) :
    let sparse := sparseWitness s
    let cancel := cancellationWitness s
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
    observationalRatioLaw Wc 1 = interventionalRatioLaw Wc 0 1 ∧
    populationDiscrepancy gaussianFeatureMap Wc 0 1 = 0 := by
  dsimp only
  rcases explicitWitness_regularities s with
    ⟨hsp, hss, hspd, hsqd, hcp, hcs, hcpd, hcqd⟩
  exact ⟨hsp, hss, sparseWitness_faithfulness s, hspd, hsqd, hcp, hcs,
    cancellationWitness_faithfulness s, hcpd, hcqd,
    cancellationWitness_ratioLaws_eq s,
    cancellationWitness_populationDiscrepancy_eq_zero s⟩

/-- The reflected sparse and cancellation mechanisms satisfy the model atoms; the sparse witness
has the certified moment and Gaussian-MMD gaps, while the cancellation ratio law is unchanged.  [the stated conclusion](goal) follows. -/
-- @node: prop:sparse-witness-certificate
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
    populationDiscrepancy gaussianFeatureMap Wc 0 1 = 0 := by
  dsimp only
  rcases explicitWitness_structural_cancellation_certificate s with
    ⟨hsp, hss, hsf, hspd, hsqd, hcp, hcs, hcf, hcpd, hcqd, hratio, hcMmd⟩
  exact ⟨hsp, hss, hsf, hspd, hsqd, hcp, hcs, hcf, hcpd, hcqd,
    sparse_witness_moment_gap s, sparse_witness_mmd_gap s, hratio, hcMmd⟩

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
