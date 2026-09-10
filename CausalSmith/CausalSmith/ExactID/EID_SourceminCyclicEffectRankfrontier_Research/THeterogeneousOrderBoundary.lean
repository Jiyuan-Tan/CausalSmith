import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.VeroneseKruskal
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TUniformConfidenceFrontier

/-!
# Heterogeneous-order population inverse boundary
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set Filter
open scoped Topology

universe u

def activeDirections {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (nu : ℕ) :
    Set (Set (Vec p)) :=
  {D | ∃ j, Causalean.Stat.MomentProblems.sourceCumulant μ (ε j) nu ≠ 0 ∧
    D = projectiveClass (C.col j)}

def twoCoordinateSources : Fin 2 → (ℝ × ℝ) → ℝ :=
  fun j z => if j.1 = 0 then z.1 else z.2

def HeterogeneousModel {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) : Prop :=
  ValidPopulationDimensions p n ∧ IsProbabilityMeasure μ ∧
    FullRowRank C ∧ NonzeroColumns C ∧ DistinctDirections C ∧ UnitNormalizedColumns C ∧
    ProbabilityTheory.iIndepFun ε μ ∧ NondegenerateSources μ ε ∧
    NonGaussianSources μ ε ∧ AllFiniteSourceMoments μ ε

def MomentDeterminateModel {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) : Prop :=
  HeterogeneousModel μ C ε ∧ ∀ j, MomentDeterminate (μ.map (ε j))

def LoadingFrontierDiscontinuity : Prop :=
  ∃ (μ : ℕ → Measure (ℝ × ℝ)) (C : ℕ → MixingMatrix 2 2) (C₀ : MixingMatrix 2 2),
    (∀ t, MomentDeterminateModel (μ t) (C t) twoCoordinateSources) ∧
    Tendsto C atTop (nhds C₀) ∧
    Tendsto (fun t => |C t 0 0|) atTop (nhds 0) ∧
    ¬ Tendsto (fun t => Metric.hausdorffDist (responseFrontier (C t) 0)
      (responseFrontier C₀ 0)) atTop (nhds 0)

def DeletionRankFrontierDiscontinuity : Prop :=
  ∃ (μ : ℕ → Measure (ℝ × ℝ)) (C : ℕ → MixingMatrix 2 2) (C₀ : MixingMatrix 2 2),
    (∀ t, MomentDeterminateModel (μ t) (C t) twoCoordinateSources) ∧
    Tendsto C atTop (nhds C₀) ∧
    Tendsto (fun t => euclideanLeastRowSingularValue (deleteRowCol (C t) 0 0))
      atTop (nhds 0) ∧
    ¬ Tendsto (fun t => Metric.hausdorffDist (responseFrontier (C t) 0)
      (responseFrontier C₀ 0)) atTop (nhds 0)

def projectiveUnitRepresentatives (directions : Set (Set (Vec 2))) : Set (Vec 2) :=
  {z | euclideanNorm z = 1 ∧ ∃ D ∈ directions, z ∈ D}

noncomputable def projectiveDirectionHausdorffDist
    (directions₁ directions₂ : Set (Set (Vec 2))) : ENNReal :=
  Metric.hausdorffEDist (projectiveUnitRepresentatives directions₁)
    (projectiveUnitRepresentatives directions₂)

noncomputable def UniformDirectionEstimationError
    (estimator : ∀ N : ℕ, Sample 2 N → Set (Set (Vec 2)))
    (N : ℕ) (eta : ℝ) : ENNReal :=
  sSup {q | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (C : MixingMatrix 2 2) (ε : Fin 2 → Ω → ℝ),
    MomentDeterminateModel μ C ε ∧
    q = (Measure.pi (fun _ : Fin N => observedLaw μ C ε))
      {s | ENNReal.ofReal eta ≤ projectiveDirectionHausdorffDist (estimator N s)
        (projectiveDirections.{0} (observedLaw μ C ε))}}

def UniformlyConsistentDirectionEstimator
    (estimator : ∀ N : ℕ, Sample 2 N → Set (Set (Vec 2))) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    Tendsto (fun N => UniformDirectionEstimationError estimator N eta) atTop (nhds 0)

noncomputable def UniformFrontierEstimationError
    (estimator : ∀ N : ℕ, Sample 2 N → Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ))
    (N : ℕ) (eta : ℝ) : ENNReal :=
  sSup {q | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (C : MixingMatrix 2 2) (ε : Fin 2 → Ω → ℝ),
    MomentDeterminateModel μ C ε ∧
    q = (Measure.pi (fun _ : Fin N => observedLaw μ C ε))
      {s | ENNReal.ofReal eta ≤
        Metric.hausdorffEDist (estimator N s) (responseFrontier C 0)}}

def UniformlyConsistentFrontierEstimator
    (estimator : ∀ N : ℕ, Sample 2 N → Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ)) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    Tendsto (fun N => UniformFrontierEstimationError estimator N eta) atTop (nhds 0)

def UniformFrontierCoverageAboveHalf
    (union : ∀ N : ℕ, Sample 2 N → Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ)) : Prop :=
  ∃ beta : ENNReal, (2 : ENNReal)⁻¹ < beta ∧
    ∀ {Ω : Type} (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (C : MixingMatrix 2 2) (ε : Fin 2 → Ω → ℝ) (N : ℕ),
      MomentDeterminateModel μ C ε → beta ≤
        (Measure.pi (fun _ : Fin N => observedLaw μ C ε))
          {s | responseFrontier C 0 ⊆ union N s}

noncomputable def UniformConfidenceUnionHausdorffError
    (union : ∀ N : ℕ, Sample 2 N → Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ))
    (N : ℕ) (eta : ℝ) : ENNReal :=
  sSup {q | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (C : MixingMatrix 2 2) (ε : Fin 2 → Ω → ℝ),
    MomentDeterminateModel μ C ε ∧
    q = (Measure.pi (fun _ : Fin N => observedLaw μ C ε))
      {s | ENNReal.ofReal eta ≤
        Metric.hausdorffEDist (union N s) (responseFrontier C 0)}}

def UniformlyVanishingConfidenceUnionError
    (union : ∀ N : ℕ, Sample 2 N → Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ)) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    Tendsto (fun N => UniformConfidenceUnionHausdorffError union N eta) atTop (nhds 0)

/-- Model-linked nonuniformity on the moment-determinate qualitative subclass. -/
def HeterogeneousNonuniformityBoundary : Prop :=
  (∀ K : ℕ, 3 ≤ K →
    ∃ (nu₀ nu₁ : Measure (ℝ × ℝ)) (C₀ C₁ : MixingMatrix 2 2),
      MomentDeterminateModel nu₀ C₀ twoCoordinateSources ∧
      MomentDeterminateModel nu₁ C₁ twoCoordinateSources ∧
      let P₀ := observedLaw nu₀ C₀ twoCoordinateSources
      let P₁ := observedLaw nu₁ C₁ twoCoordinateSources
      (∀ nu, nu ≤ K → lawCumulantTensor (nu := nu) P₀ = lawCumulantTensor P₁) ∧
      projectiveDirections.{0} P₀ ≠ projectiveDirections.{0} P₁ ∧
      responseFrontier C₀ 0 ≠ responseFrontier C₁ 0) ∧
  (∃ (C₀ C₁ : MixingMatrix 2 2) (mu₀ mu₁ : ℕ → Measure (ℝ × ℝ)),
    (∀ N, MomentDeterminateModel (mu₀ N) C₀ twoCoordinateSources ∧
      MomentDeterminateModel (mu₁ N) C₁ twoCoordinateSources) ∧
    {D | ∃ j, D = projectiveClass (C₀.col j)} ≠
      {D | ∃ j, D = projectiveClass (C₁.col j)} ∧
    responseFrontier C₀ 0 ≠ responseFrontier C₁ 0 ∧
    Tendsto (fun N => totalVariationDistance
      (Measure.pi (fun _ : Fin N => observedLaw (mu₀ N) C₀ twoCoordinateSources))
      (Measure.pi (fun _ : Fin N => observedLaw (mu₁ N) C₁ twoCoordinateSources)))
      atTop (nhds 0)) ∧
  (∀ estimator : ∀ N : ℕ, Sample 2 N → Set (Set (Vec 2)),
    ¬ UniformlyConsistentDirectionEstimator estimator) ∧
  (∀ estimator : ∀ N : ℕ, Sample 2 N →
      Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ),
    ¬ UniformlyConsistentFrontierEstimator estimator) ∧
  (∀ union : ∀ N : ℕ, Sample 2 N → Set ({i : Fin 2 // i ≠ (0 : Fin 2)} → ℝ),
    ¬ (UniformFrontierCoverageAboveHalf union ∧
      UniformlyVanishingConfidenceUnionError union)) ∧
  LoadingFrontierDiscontinuity ∧ DeletionRankFrontierDiscontinuity

def AdaptiveReshapeRecovery {p nu : ℕ} (P : Measure (Vec p))
    (directions : Set (Set (Vec p))) : Prop :=
  let R := directions.ncard
  R < 2 ∨ (2 * R - 1 ≤ nu ∧
    ∀ (gamma : Fin R → ℝ) (z : Fin R → Vec p),
      IsLeastFeasibleRank (n := R) (lawCumulantTensor (nu := nu) P) R →
      ThreeBlockCPDecomposition (lawCumulantTensor (nu := nu) P)
        (R - 1) (R - 1) (nu - 2 * R + 2) R gamma z →
      directions = {D | ∃ h, D = projectiveClass (z h)})

def RetainedCommonOrderConclusion : Prop :=
  ∀ {Ω : Type*} (_ : MeasurableSpace Ω) {p n r d q : ℕ}
      (μ : Measure Ω) (u v : Vec p) (a delta sigma kappa Lambda M alpha : ℝ),
    ValidInferenceMargins alpha a delta sigma kappa Lambda M →
    SeparatedClassNonempty (n := n) μ u v r d q a delta sigma kappa Lambda M →
    (∀ (N : ℕ) (hN : ValidSampleSize N) (C : MixingMatrix p n)
        (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ)
        (hclass : SeparatedOICAClass μ C ε lam u v r d q
          a delta sigma kappa Lambda M) (sampleLaw : Measure (Sample p N)),
      IidObservationalSample sampleLaw (observedLaw μ C ε) →
      ENNReal.ofReal (1 - alpha) ≤ sampleLaw
        {s | ConfidenceEvent μ C ε lam u v a delta sigma kappa Lambda M alpha
          hN hclass s}) ∧
    RootNConfidenceRate p n r q a sigma kappa Lambda M alpha

-- @node: thm:heterogeneous-order-population-inverse-boundary
theorem heterogeneous_order_population_inverse_boundary
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ)
    (hp : 2 ≤ p) (hpn : p ≤ n)
    (hC : FullRowRank C) (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C)
    (hnorm : UnitNormalizedColumns C) (hind : ProbabilityTheory.iIndepFun ε μ)
    (hnd : NondegenerateSources μ ε) (hng : NonGaussianSources μ ε)
    (hmom : AllFiniteSourceMoments μ ε)
    (KruskalThreeFactorUniqueness_of_gate : KruskalThreeFactorUniqueness)
    (MarcinkiewiczCumulantTail_of_gate : MarcinkiewiczCumulantTail) :
    (∀ nu, 2 * n - 1 ≤ nu → ∀ R gamma z,
      IsLeastFeasibleRank (n := n)
          (lawCumulantTensor (nu := nu) (observedLaw μ C ε)) R →
      ThreeBlockCPDecomposition
          (lawCumulantTensor (nu := nu) (observedLaw μ C ε))
          (n - 1) (n - 1) (nu - 2 * n + 2) R gamma z →
      {D | ∃ h, D = projectiveClass (z h)} = activeDirections μ C ε nu) ∧
    (∃ (rankAt : ℕ → ℕ) (weightAt : (nu : ℕ) → Fin (rankAt nu) → ℝ)
        (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p),
      ∀ K, 2 * n - 1 ≤ K →
        ValidMultiOrderSelection (observedLaw μ C ε) n K rankAt weightAt directionAt) ∧
    (∀ (rankAt : ℕ → ℕ) (weightAt : (nu : ℕ) → Fin (rankAt nu) → ℝ)
        (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p),
      ∀ (hselection : ∀ K, 2 * n - 1 ≤ K →
        ValidMultiOrderSelection (observedLaw μ C ε) n K rankAt weightAt directionAt),
      ∃ (K : ℕ) (hK : 2 * n - 1 ≤ K) (stop : ℕ),
        2 * n - 1 ≤ stop ∧ stop ≤ K ∧
        multiOrderHandle (observedLaw μ C ε) n K hK (K + 1) (Nat.lt_succ_self K)
            rankAt weightAt directionAt (hselection K hK) =
          MultiOrderHandleResult.complete stop {D | ∃ j, D = projectiveClass (C.col j)} ∧
        projectiveDirections.{u} (observedLaw μ C ε) =
          {D | ∃ j, D = projectiveClass (C.col j)}) ∧
    (∀ nu, 2 * n - 1 ≤ nu →
      let R := (activeDirections μ C ε nu).ncard
      (2 ≤ R → 2 * R - 1 ≤ nu) ∧
      AdaptiveReshapeRecovery (nu := nu) (observedLaw μ C ε)
        (activeDirections μ C ε nu) ∧
      (R = 0 → lawCumulantTensor (nu := nu) (observedLaw μ C ε) = 0) ∧
      (R = 1 → ∃ gamma z, CPDecomposition
        (lawCumulantTensor (nu := nu) (observedLaw μ C ε)) 1 gamma z)) ∧
    (∀ (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ), (∀ j, scale j ≠ 0) →
      ∀ x y : Fin p,
        responseFrontier (permuteScaleColumns C pi scale) x = responseFrontier C x ∧
        effectFrontier (permuteScaleColumns C pi scale) x y = effectFrontier C x y) ∧
    HeterogeneousNonuniformityBoundary ∧
    RetainedCommonOrderConclusion := by sorry

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
