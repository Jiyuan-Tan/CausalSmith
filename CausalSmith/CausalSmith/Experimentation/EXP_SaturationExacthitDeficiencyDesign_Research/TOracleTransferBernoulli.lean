import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Certificate
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TTargetTangentLanBernoulli
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TGaussianFiniteCertificate
import Causalean.Stat.Concentration.Matrix.IidSums
import Causalean.Stat.Limit.ConvergenceVec

set_option linter.style.openClassical false

/-! # Bernoulli primitive-to-Gaussian oracle transfer -/

open scoped BigOperators
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- Primitive regret of a represented Gaussian selector fed the calibrated vector. -/
def bernoulliPrimitiveRisk (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (A : Finset (Fin K))
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) (C : ℕ) : ℝ :=
  ∫ O : Fin C → Record K n,
    ∑ a, delta (calibratedEstimator O m A).2 a *
      simpleRegret A (exactSliceWelfare P m) a
    ∂(Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)

/-- Risk of the actual split rule: the pilot chooses a snapped-covariance
certificate selector, which is then fed the remaining-sample calibrated vector. -/
def bernoulliSplitPrimitiveRisk (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (A : Finset (Fin K)) (pilotSize : ℕ)
    (selector : (Fin pilotSize → Record K n) → (ActiveIndex A → ℝ) → Fin K → ℝ)
    (N : ℕ) : ℝ :=
  ∫ pilot : Fin pilotSize → Record K n,
    ∫ remaining : Fin (N - pilotSize) → Record K n,
      ∑ a, selector pilot (calibratedEstimator remaining m A).2 a *
        simpleRegret A (exactSliceWelfare P m) a
      ∂(Measure.pi fun _ : Fin (N - pilotSize) => bernoulliObservedLaw P p m)
    ∂(Measure.pi fun _ : Fin pilotSize => bernoulliObservedLaw P p m)

def bernoulliPilotLaw (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (pilotSize : ℕ) : Measure (Fin pilotSize → Record K n) :=
  Measure.pi fun _ => bernoulliObservedLaw P p m

-- @node: prop:oracle-transfer-bernoulli
/-- A diverging, vanishing-fraction pilot and outward covariance snapping transfer
the compact Gaussian certificate uniformly over the Bernoulli outer simplex. -/
theorem oracle_transfer_bernoulli {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : (Fin K → ℝ) → Measure (Fin C → Fin K))
    (jointLaw : (Fin K → ℝ) →
      Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (m : Fin K → ℕ) (A : Finset (Fin K)) (M tauLower : ℝ)
    (localDirections : Finset (Fin K) → Set (Fin K → ℝ))
    (observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells : List RationalCell)
    (covarianceCells : Finset (Fin K) → List RationalCell)
    (h_iid : IidSchedules P0 sampleLaw)
    (h_labels : ∀ p, InSimplex p → BernoulliLabelIid p (labelLaw p))
    (h_indep : ∀ p, InSimplex p →
      BernoulliLabelScheduleIndep sampleLaw (labelLaw p) (jointLaw p))
    (h_units : ∀ p, InSimplex p →
      BernoulliUnits m P0 (labelLaw p) assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower)
    (hmenu : WellFormedMenu n K m) (hA : 2 ≤ A.card) (hM : 0 < M)
    (hargmax : ∀ k, k ∈ A ↔
      ∀ j, exactSliceWelfare P0 m j ≤ exactSliceWelfare P0 m k)
    (hlocal : ∀ S : Finset (Fin K), 2 ≤ S.card → S ⊆ A →
      IsCompact (localDirections S) ∧
      ExactQuotientBallRepresentativeCoverage S M (localDirections S))
    (hpartition : GenuineQuotientPartition A M parameterCells)
    (hobservation : TruncatedObservationPartition A observationRadius observationCells)
    (hvariancePartition : GenuineRatePartition K varianceCells ∧
      ∃ cell ∈ varianceCells, InRationalCell (fun k => sliceVariance P0 (m k)) cell)
    (hratePartition : GenuineRatePartition K rateCells ∧
      ∀ p, InSimplex p → ∃ cell ∈ rateCells,
        InRationalCell (hitMatrix n m p).2 cell)
    (hcovariancePartition : ∀ S : Finset (Fin K), 2 ≤ S.card → S ⊆ A →
      (covarianceCells S).Nodup ∧ 1 < (covarianceCells S).length ∧
      (∀ cell ∈ covarianceCells S, cell ≠ []) ∧
      CovarianceCellsHaveDisjointInteriors S (covarianceCells S) ∧
      CovariancePartitionCoversRates S (fun k => sliceVariance P0 (m k))
        rateCells (covarianceCells S) ∧
      ∃ eigenLower eigenUpper : ℝ, 0 < eigenLower ∧ eigenLower ≤ eigenUpper ∧
        UniformlyEigenBoundedCovarianceCells S (covarianceCells S)
          eigenLower eigenUpper) :
    ∀ epsilon > 0, ∃ pilot : ℕ → ℕ,
    ∃ hatSigma : ∀ N, (Fin (pilot N) → Record K n) → Fin K → Fin K → ℝ,
    ∃ snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ,
    ∃ varianceAssignment : (Fin K → ℝ) → RationalCell,
    ∃ rateAssignment : (Fin K → ℝ) → RationalCell,
    ∃ covarianceAssignment : ∀ S : Finset (Fin K),
      (Fin K → ℝ) → (Fin K → ℝ) → RationalCell,
    ∃ fallback : ∀ S : Finset (Fin K), (ActiveIndex S → ℝ) → Fin K → ℝ,
    ∃ cellCertificate : ∀ S : Finset (Fin K), RationalCell → ℝ →
      CompactCertificateOutput S,
    ∃ goodPilot : ∀ S : Finset (Fin K), ∀ N,
      {p : Fin K → ℝ // InSimplex p} → Set (Fin (pilot N) → Record K n),
    ∃ certificate : ∀ S : Finset (Fin K), ∀ N,
      {p : Fin K → ℝ // InSimplex p} → (Fin (pilot N) → Record K n) →
        ℝ → CompactCertificateOutput S,
    ∃ selector : ∀ S : Finset (Fin K), ∀ N,
      {p : Fin K → ℝ // InSimplex p} → (Fin (pilot N) → Record K n) →
        ℝ → (ActiveIndex S → ℝ) → Fin K → ℝ,
      Tendsto pilot atTop atTop ∧
      Tendsto (fun N => (pilot N : ℝ) / N) atTop (nhds 0) ∧
      DataDeterminedOutwardCovarianceSnap A snap ∧
      DeterministicRateCellAssignment varianceCells varianceAssignment ∧
      DeterministicRateCellAssignment rateCells rateAssignment ∧
      (∀ S, 2 ≤ S.card → S ⊆ A →
        DeterministicCovarianceCellAssignment S (covarianceCells S)
          (covarianceAssignment S)) ∧
      (∀ S, S.Nonempty → S ⊆ A → GaussianSelector S (fallback S)) ∧
      (∀ N O, hatSigma N O =
        empiricalCovariance (fun k => feasibleBernoulliInfluence O m k) O) ∧
      (∀ S N p, MeasurableSet (goodPilot S N p)) ∧
      Tendsto (fun (N : ℕ) => sSup {prob : ℝ | ∃ S : Finset (Fin K), S.Nonempty ∧ S ⊆ A ∧
        ∃ p : {p : Fin K → ℝ // InSimplex p}, ∃ h ∈ localDirections S,
          prob = ((bernoulliPilotLaw
            (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹) p.1 m (pilot N))
              (goodPilot S N p)ᶜ).toReal})
        atTop (nhds 0) ∧
      (∀ S (p : {p : Fin K → ℝ // InSimplex p}) tolerance,
        S.Nonempty → S ⊆ A → 0 < tolerance →
        let q := (hitMatrix n m p.1).2
        let trueV := fun k => sliceVariance P0 (m k)
        S.card = 1 ∨ (2 ≤ S.card ∧
          ∀ cell ∈ covarianceCells S, CovarianceCellContains S trueV q cell →
            (cellCertificate S cell tolerance).2.2.variancePartition = varianceCells ∧
              TrueParameterCertificateBenchmark S trueV q M tolerance
                (cellCertificate S cell tolerance))) ∧
      (∀ S N p O, S.Nonempty → S ⊆ A → O ∈ goodPilot S N p →
        let q := (hitMatrix n m p.1).2
        let snappedV := snap (hatSigma N O) q
        varianceAssignment snappedV ∈ varianceCells ∧
        InRationalCell snappedV (varianceAssignment snappedV) ∧
        varianceAssignment (fun k => sliceVariance P0 (m k)) ∈ varianceCells ∧
        InRationalCell (fun k => sliceVariance P0 (m k))
          (varianceAssignment (fun k => sliceVariance P0 (m k))) ∧
        rateAssignment q ∈ rateCells ∧ InRationalCell q (rateAssignment q) ∧
        ((S.card = 1 ∧ ∀ tolerance,
            (certificate S N p O tolerance).2.1 = singletonActiveSelector S ∧
            selector S N p O tolerance = singletonActiveSelector S) ∨
          (2 ≤ S.card ∧ ∀ tolerance > 0,
            covarianceAssignment S snappedV q ∈ covarianceCells S ∧
            covarianceAssignment S snappedV q = covarianceAssignment S
              (fun k => sliceVariance P0 (m k)) q ∧
            CovarianceCellContains S (fun k => sliceVariance P0 (m k)) q
              (covarianceAssignment S snappedV q) ∧
            CovarianceCellContains S snappedV q (covarianceAssignment S snappedV q) ∧
            IsCheckedCompactCertificate S snappedV q M tolerance
                (certificate S N p O tolerance) ∧
            (certificate S N p O tolerance).2.2.variancePartition = varianceCells ∧
            (certificate S N p O tolerance).2.2.ratePartition = rateCells ∧
            certificate S N p O tolerance =
                cellCertificate S (covarianceAssignment S snappedV q) tolerance ∧
            covarianceAssignment S snappedV q ∈
                (certificate S N p O tolerance).2.2.covariancePartition ∧
            covarianceAssignment S snappedV q ∈
                (certificate S N p O tolerance).2.2.terminalBranchCells ∧
            (∃ terminal ∈ (certificate S N p O tolerance).2.2.terminalBranchCells,
              RationalCellRefines terminal (rateAssignment q) ∧
                InRationalCell q terminal) ∧
            selector S N p O tolerance = (certificate S N p O tolerance).2.1))) ∧
      (∀ S N p O, S.Nonempty → S ⊆ A → O ∉ goodPilot S N p →
        ∀ tolerance, selector S N p O tolerance = fallback S) ∧
      (∃ scaledLocalRegretBound ≥ 0, ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
        ∀ (N : ℕ) (h : Fin K → ℝ) (x : ActiveIndex S → ℝ),
        h ∈ localDirections S → Real.sqrt N * |∑ a,
          fallback S x a * simpleRegret S
            (exactSliceWelfare (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹) m) a| ≤
              scaledLocalRegretBound) ∧
      (∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
        (S.card = 1 ∧ ∀ (N : ℕ) (p : {p : Fin K → ℝ // InSimplex p}) h,
          bernoulliSplitPrimitiveRisk
            (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹) p.1 m S (pilot N)
              (fun O => selector S N p O epsilon) N = 0) ∨
        (2 ≤ S.card ∧ Filter.limsup (fun (N : ℕ) => sSup {gap : ℝ |
          ∃ p : {p : Fin K → ℝ // InSimplex p}, ∃ h ∈ localDirections S,
            gap = Real.sqrt N * bernoulliSplitPrimitiveRisk
              (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹) p.1 m S (pilot N)
                (fun O => selector S N p O epsilon) N -
              finiteContainingCertificateUpper S (fun k => sliceVariance P0 (m k))
                (hitMatrix n m p.1).2 (covarianceCells S)
                (fun cell => cellCertificate S cell epsilon)}) atTop ≤ 0)) ∧
      ∃ epsilonSeq : ℕ → ℝ, (∀ N, 0 < epsilonSeq N) ∧
        Antitone epsilonSeq ∧ Tendsto epsilonSeq atTop (nhds 0) ∧
        (∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
          (S.card = 1 ∨ Tendsto (fun (N : ℕ) => sSup {gap : ℝ |
            ∃ p : {p : Fin K → ℝ // InSimplex p},
              gap = |sSup {risk : ℝ | ∃ h ∈ localDirections S,
                risk = Real.sqrt N * bernoulliSplitPrimitiveRisk
                  (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹) p.1 m S (pilot N)
                    (fun O => selector S N p O (epsilonSeq N)) N} -
                      gaussianCompactValueReal S (fun k => sliceVariance P0 (m k))
                        (hitMatrix n m p.1).2 M|}) atTop (nhds 0))) ∧
      (A = Finset.univ → ∀ p, InSimplex p → ∀ k, 0 < (hitMatrix n m p).2 k) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
