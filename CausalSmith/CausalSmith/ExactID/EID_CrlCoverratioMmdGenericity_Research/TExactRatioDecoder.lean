import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CondIndepIntersection
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CitedGates
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.FiniteDensityBridge
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Exact ratio decoder

This file states the population transitive-closure, continuous conditional-rank,
parent-pruning, ordering-independence, and representation-uniqueness conclusions.
Faithfulness is confined to a separate overlap corollary.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Environment-label parents obtained by pulling back the latent parent set. -/
def environmentParentSet {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => G.edge (W.targetPerm j) (W.targetPerm i))

/-- The componentwise `C²` ambiguity relating two compatible representations. -/
def ComponentwiseC2Equivalent
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂) : Prop :=
  observedSupport G₁ W₁ = observedSupport G₂ W₂ ∧
  ∃ σ : Equiv.Perm (Fin n),
    (∀ j i, G₂.edge (σ j) (σ i) ↔ G₁.edge j i) ∧
    ∃ h hinv : Fin n → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ 2 (h i) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i, ContDiffOn ℝ 2 (hinv i) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i, Set.MapsTo (h i) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i, Set.MapsTo (hinv i) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i z, z ∈ Set.Icc (0 : ℝ) 1 → hinv i (h i z) = z) ∧
      (∀ i z, z ∈ Set.Icc (0 : ℝ) 1 → h i (hinv i z) = z) ∧
      (∀ x ∈ observedSupport G₁ W₁, ∀ i,
        W₂.unmix x (σ i) = h i (W₁.unmix x i))

/-- Formal scope/comparison payload: one unknown target per node, recovery of rather than input
of the graph/order/alignment, faithful-overlap uniqueness, and the bivariate MMD witness. -/
def ExactRatioDecoderComparisonClauses
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
  (θ : Mechanism n G) (W : ObservedWorld G θ) : Prop :=
  let laws := observedProbabilityLawFamily W.law
  (∀ i : Fin n, ∃! e : Fin n, W.targetPerm e = i) ∧
  (populationDecoder laws).2.2.edge = permutedGraph G W ∧
  (Faithfulness G θ →
    ∀ (G' : Causalean.DAG (Fin n)) (θ' : Mechanism n G')
      (W' : ObservedWorld G' θ'),
      PositiveNormalizedSmoothMechanisms G' θ' → CausalMinimality G' θ' →
      FixedOwnDerivativeSign G' s θ' → SharedDiffeomorphicMixing G' θ' W' →
      OnePerfectInterventionPerNode G' θ' W' → W'.law = W.law →
      ComponentwiseC2Equivalent W W') ∧
  (n = 2 → ∀ ⦃j i⦄, G.edge j i →
    0 < observedLawDiscrepancy gaussianFeatureMap W.law
      (W.targetPerm.symm j) (W.targetPerm.symm i)) ∧
  (∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i, environmentParentSet W i ⊆ predecessorSet order i)

/-- Equation (11): conditional on predecessor ranks (hence on the parents), the target log-ratio
CDF integrates the intervention density over own-coordinate values below the log-ratio threshold. -/
def equationElevenConditionalRatioCDF
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (i : Fin n) (t : ℝ) (v : LatentState n) : ℝ :=
  ∫ w in Set.Icc (0 : ℝ) 1,
    if Real.log (θ.q i w / θ.p i (Function.update v i w)) ≤ t then θ.q i w else 0

/-- All mathematical conclusions of the exact population decoder theorem. -/
def ExactRatioDecoderConclusion
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (W : ObservedWorld G θ) : Prop :=
  let laws := observedProbabilityLawFamily W.law
  Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W) ∧
  IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law)
      (selectedTopologicalOrder laws) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i,
      IsContinuousConditionalRatioCDFVersion laws order i
        (observedConditionalRatioCDF laws order i) ∧
      (∃ C, IsContinuousConditionalRatioCDFVersion laws order i C ∧
        ∀ t v, v ∈ latentCube n →
          (C t (familyProjection (observedLawLogRatio W.law)
              (predecessorSet order i) (W.mix v)) : ℝ) =
            equationElevenConditionalRatioCDF θ (W.targetPerm i) t v) ∧
      (∀ C, IsContinuousConditionalRatioCDFVersion laws order i C →
        ∀ z ∈ observedConditionalRatioSupport W.law order i,
          C z.1 z.2 = observedConditionalRatioCDF laws order i z.1 z.2) ∧
      (∀ t v, v ∈ latentCube n →
        (observedConditionalRatioCDF laws order i t
            (familyProjection (observedLawLogRatio W.law)
              (predecessorSet order i) (W.mix v)) : ℝ) =
          equationElevenConditionalRatioCDF θ (W.targetPerm i) t v) ∧
      ∀ v, v ∈ latentCube n →
        (observedLawRankCoordinate laws order i (W.mix v) : ℝ) =
          if s.value (W.targetPerm i) = 1
          then interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))
          else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i, environmentParentSet W i ⊆ predecessorSet order i) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i A, A ⊆ predecessorSet order i →
      (CondIndepGiven (W.law 0) (observedLawRankCoordinate laws order i)
        (familyProjection (observedLawRankCoordinate laws order)
          (predecessorSet order i \ A))
        (familyProjection (observedLawRankCoordinate laws order) A) ↔
      environmentParentSet W i ⊆ A)) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i, MinimalAdmissibleParentSet laws order i (environmentParentSet W i) ∧
      ∀ A, MinimalAdmissibleParentSet laws order i A →
        A = environmentParentSet W i) ∧
  ObservedWorldLawCoherent W ∧
  (populationDecoder laws).2.2.edge = permutedGraph G W ∧
  (∀ (G' : Causalean.DAG (Fin n)) (θ' : Mechanism n G')
      (W' : ObservedWorld G' θ'),
    PositiveNormalizedSmoothMechanisms G' θ' →
    CausalMinimality G' θ' →
    FixedOwnDerivativeSign G' s θ' →
    SharedDiffeomorphicMixing G' θ' W' →
    OnePerfectInterventionPerNode G' θ' W' →
    W'.law = W.law → ComponentwiseC2Equivalent W W') ∧
  (n = 2 → ∀ ⦃j i⦄, G.edge j i →
    0 < observedLawDiscrepancy gaussianFeatureMap W.law
      (W.targetPerm.symm j) (W.targetPerm.symm i)) ∧
  ExactRatioDecoderComparisonClauses s θ W

/-- A non-ancestor intervention leaves the corresponding ratio law unchanged, hence has zero MMD. -/
-- @node: ratio_nonancestor_zero
lemma ratio_nonancestor_zero
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {j i : Fin n} (hne : j ≠ i)
    (hna : ¬ G.isAncestor (W.targetPerm j) (W.targetPerm i)) :
    populationDiscrepancy gaussianFeatureMap W j i = 0 := by
  apply populationDiscrepancy_eq_zero_of_ratioLaw_eq
  exact FiniteDensityObservedWorldBridge.ratioLaw_eq_of_nonancestor
    (finiteDensityObservedWorldBridge_of_assumptions W hpos hmix hone) hne hna

-- @node: thm:exact-ratio-decoder
/-- Cover-separated positive smooth causal-minimal mechanisms are decoded exactly from their
observed environment laws, up to relabeling and componentwise `C²` diffeomorphisms. -/
theorem exact_ratio_decoder
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (world : ∀ θ' : Mechanism n G, ObservedWorld G θ')
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hminimal : CausalMinimality G θ)
    (hmix : SharedDiffeomorphicMixing G θ (world θ))
    (hone : OnePerfectInterventionPerNode G θ (world θ))
    (hsign : FixedOwnDerivativeSign G s θ)
    (hcover : (⟨θ, ⟨hpos, hminimal, hsign⟩⟩ : StratumPoint G s) ∈
      coverSeparatedSet (s := s) gaussianFeatureMap (world θ).targetPerm) :
    ExactRatioDecoderConclusion s θ (world θ) := by sorry

/-- Faithful-overlap corollary; faithfulness is deliberately not a premise of the main theorem. -/
theorem exact_ratio_decoder_faithful
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (world : ∀ θ' : Mechanism n G, ObservedWorld G θ')
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hminimal : CausalMinimality G θ)
    (hmix : SharedDiffeomorphicMixing G θ (world θ))
    (hone : OnePerfectInterventionPerNode G θ (world θ))
    (hsign : FixedOwnDerivativeSign G s θ)
    (hfaith : Faithfulness G θ)
    (hcover : (⟨θ, ⟨hpos, hminimal, hsign⟩⟩ : StratumPoint G s) ∈
      coverSeparatedSet (s := s) gaussianFeatureMap (world θ).targetPerm) :
    ExactRatioDecoderConclusion s θ (world θ) := by
  exact exact_ratio_decoder s θ world hpos hminimal hmix hone hsign hcover

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
