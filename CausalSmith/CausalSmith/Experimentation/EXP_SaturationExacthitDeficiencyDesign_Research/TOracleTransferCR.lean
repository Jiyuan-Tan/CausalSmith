import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Certificate
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.ScheduleLawBridge
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TTargetTangentLanCR
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TGaussianFiniteCertificate

set_option linter.style.openClassical false

/-! # Fixed-count primitive-to-Gaussian oracle transfer -/

open scoped BigOperators
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

def crPrimitiveRisk (P : Measure (Schedule n)) (counts : Fin K → ℕ)
    (m : Fin K → ℕ) (A : Finset (Fin K))
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) (C : ℕ) : ℝ :=
  ∫ O : Fin C → Record K n,
    ∑ a, delta (calibratedEstimator O m A).2 a *
      simpleRegret A (exactSliceWelfare P m) a ∂(crObservedLaw P counts m)

/-- Fixed-count split risk formed from one total sample: pilot counts are
subtracted stratumwise and the decision record array has the remaining size. -/
def crSplitPrimitiveRisk (P : Measure (Schedule n)) (pilotCounts totalCounts : Fin K → ℕ)
    (m : Fin K → ℕ) (A : Finset (Fin K))
    (selector : (Fin C → Record K n) → (ActiveIndex A → ℝ) → Fin K → ℝ) (N : ℕ) : ℝ :=
  ∫ pilot : Fin C → Record K n,
    ∫ decision : Fin (N - C) → Record K n,
      ∑ a, selector pilot (calibratedEstimator decision m A).2 a *
        simpleRegret A (exactSliceWelfare P m) a
        ∂(crObservedLaw P (fun k => totalCounts k - pilotCounts k) m)
    ∂(crObservedLaw P pilotCounts m)

/-- Coordinatewise measurability of the pilot covariance estimate used by the
outer integral in the split experiment. -/
def MeasurableCrPilotCovarianceEstimate
    (hatSigma : (Fin C → Record K n) → Fin K → Fin K → ℝ) : Prop :=
  ∀ i j, Measurable fun O => hatSigma O i j

/-- Joint measurability of the outward snapping map in its empirical covariance
matrix and rate-vector arguments. -/
def MeasurableOutwardCovarianceSnap
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ∀ k, Measurable fun input : (Fin K → Fin K → ℝ) × (Fin K → ℝ) =>
    snap input.1 input.2 k

/-- A finite rational-cell assignment is measurable when each of its fibres is
measurable.  This formulation avoids assigning an unrelated sigma-algebra to
the list encoding of a rational cell. -/
def MeasurableRationalCellAssignment {X : Type*} [MeasurableSpace X]
    (assign : X → RationalCell) : Prop :=
  ∀ cell, MeasurableSet {x | assign x = cell}

/-- The data-driven randomized rule is jointly measurable in the pilot record
and the independent active decision statistic, so the outer Bochner integral
cannot acquire the junk value of a nonintegrable witness. -/
def JointlyMeasurableCrPilotSelector (S : Finset (Fin K))
    (selector : (Fin C → Record K n) → ℝ →
      (ActiveIndex S → ℝ) → Fin K → ℝ) : Prop :=
  ∀ tolerance a, Measurable fun input :
      (Fin C → Record K n) × (ActiveIndex S → ℝ) =>
    selector input.1 tolerance input.2 a

-- @node: prop:oracle-transfer-cr
/-- Within-stratum pilots transfer the compact Gaussian certificate uniformly on
compact active-interior allocation sets; no positive-rate claim is made at a vanishing share. -/
theorem oracle_transfer_cr {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (allocations : Set (Fin K → ℝ))
    (counts : (Fin K → ℝ) → ℕ → Fin K → ℕ)
    (labelLaw : (Fin K → ℝ) → Measure (Fin C → Fin K))
    (jointLaw : (Fin K → ℝ) →
      Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (M tauLower : ℝ)
    (localDirections : Finset (Fin K) → Set (Fin K → ℝ))
    (observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells : List RationalCell)
    (covarianceCells : Finset (Fin K) → List RationalCell)
    (h_iid : IidSchedules P0 sampleLaw)
    (h_allocations : IsCompact allocations ∧ allocations.Nonempty ∧
      ∀ alpha ∈ allocations, InActiveSimplex A alpha)
    (h_labels : ∀ alpha ∈ allocations, CrLabelVector (counts alpha C) (labelLaw alpha))
    (h_indep : ∀ alpha ∈ allocations,
      CrLabelScheduleIndep sampleLaw (labelLaw alpha) (jointLaw alpha))
    (h_shares : ∀ alpha ∈ allocations, CrActiveShares (counts alpha) alpha A)
    (h_slices : ∀ alpha ∈ allocations,
      CrExactSlices m P0 (labelLaw alpha) assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower)
    (hmenu : WellFormedMenu n K m)
    (hcounts : (∀ alpha ∈ allocations, ∀ N, ∑ k, counts alpha N k = N) ∧
      ∀ alpha ∈ allocations, ∀ N k, k ∉ A → counts alpha N k = 0)
    (hA : 2 ≤ A.card) (hM : 0 < M)
    (hargmax : ∀ k, k ∈ A ↔
      ∀ j, exactSliceWelfare P0 m j ≤ exactSliceWelfare P0 m k)
    (hlocal : ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
      IsCompact (localDirections S) ∧
      ExactQuotientBallRepresentativeCoverage S M (localDirections S))
    (hpartition : GenuineQuotientPartition A M parameterCells)
    (hobservation : TruncatedObservationPartition A observationRadius observationCells)
    (hvariancePartition : GenuineRatePartition K varianceCells ∧
      ∃ cell ∈ varianceCells, InRationalCell (fun k => sliceVariance P0 (m k)) cell)
    (hratePartition : GenuineRatePartition K rateCells ∧
      ∀ alpha ∈ allocations, ∃ cell ∈ rateCells, InRationalCell alpha cell)
    (hcovariancePartition : ∀ S : Finset (Fin K), 2 ≤ S.card → S ⊆ A →
      (covarianceCells S).Nodup ∧ 1 < (covarianceCells S).length ∧
      (∀ cell ∈ covarianceCells S, cell ≠ []) ∧
      CovarianceCellsHaveDisjointInteriors S (covarianceCells S) ∧
      CovariancePartitionCoversRates S (fun k => sliceVariance P0 (m k))
        rateCells (covarianceCells S) ∧
      ∃ eigenLower eigenUpper : ℝ, 0 < eigenLower ∧ eigenLower ≤ eigenUpper ∧
        UniformlyEigenBoundedCovarianceCells S (covarianceCells S)
          eigenLower eigenUpper) :
    let v := fun k => sliceVariance P0 (m k)
    ∃ pilotTotal : ∀ alpha : {a : Fin K → ℝ // a ∈ allocations}, ℕ → ℕ,
    ∃ pilot : ∀ alpha : {a : Fin K → ℝ // a ∈ allocations}, ℕ → Fin K → ℕ,
      (∀ alpha N, ∑ k, pilot alpha N k = pilotTotal alpha N) ∧
      (∀ alpha N k, pilot alpha N k ≤ counts alpha.1 N k) ∧
      (∀ alpha k, k ∈ A → Tendsto (fun N => pilot alpha N k) atTop atTop) ∧
      (∀ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∀ k ∈ A,
        Tendsto (fun N => (pilot alpha N k : ℝ) / counts alpha.1 N k)
          atTop (nhds 0)) ∧
      ∃ hatSigma : ∀ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∀ N : ℕ,
          (Fin (pilotTotal alpha N) → Record K n) → Fin K → Fin K → ℝ,
      ∃ snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ,
      ∃ varianceAssignment : (Fin K → ℝ) → RationalCell,
      ∃ rateAssignment : (Fin K → ℝ) → RationalCell,
      ∃ covarianceAssignment : ∀ S : Finset (Fin K),
        (Fin K → ℝ) → (Fin K → ℝ) → RationalCell,
      ∃ fallback : ∀ S : Finset (Fin K), (ActiveIndex S → ℝ) → Fin K → ℝ,
      ∃ cellCertificate : ∀ S : Finset (Fin K), RationalCell → ℝ →
        CompactCertificateOutput S,
      ∃ goodPilot : ∀ S : Finset (Fin K),
        ∀ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∀ N,
          Set (Fin (pilotTotal alpha N) → Record K n),
      ∃ certificate : ∀ S : Finset (Fin K),
        ∀ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∀ N,
          (Fin (pilotTotal alpha N) → Record K n) → ℝ → CompactCertificateOutput S,
      ∃ selector : ∀ alpha : {a : Fin K → ℝ // a ∈ allocations},
          ∀ S : Finset (Fin K), ∀ N : ℕ,
          (Fin (pilotTotal alpha N) → Record K n) → ℝ →
            (ActiveIndex S → ℝ) → Fin K → ℝ,
        DataDeterminedOutwardCovarianceSnap A snap ∧
        MeasurableOutwardCovarianceSnap snap ∧
        DeterministicRateCellAssignment varianceCells varianceAssignment ∧
        DeterministicRateCellAssignment rateCells rateAssignment ∧
        (∀ S, 2 ≤ S.card → S ⊆ A →
          DeterministicCovarianceCellAssignment S (covarianceCells S)
            (covarianceAssignment S)) ∧
        MeasurableRationalCellAssignment varianceAssignment ∧
        MeasurableRationalCellAssignment rateAssignment ∧
        (∀ alpha N,
          MeasurableCrPilotCovarianceEstimate (hatSigma alpha N)) ∧
        (∀ S alpha N,
          JointlyMeasurableCrPilotSelector S (selector alpha S N)) ∧
        (∀ S alpha N cell, MeasurableSet {O |
          covarianceAssignment S (snap (hatSigma alpha N O) alpha.1) alpha.1 = cell}) ∧
        (∀ S, S.Nonempty → S ⊆ A → GaussianSelector S (fallback S)) ∧
        (∀ alpha N O, hatSigma alpha N O = empiricalCovariance
          (fun k => feasibleCrInfluence O (pilot alpha N) m k) O) ∧
        (∀ S alpha N, MeasurableSet (goodPilot S alpha N)) ∧
        Tendsto (fun (N : ℕ) => sSup {prob : ℝ |
          ∃ S : Finset (Fin K), S.Nonempty ∧ S ⊆ A ∧
          ∃ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∃ h ∈ localDirections S,
            prob = (crObservedLaw
              (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹)
              (pilot alpha N) m (goodPilot S alpha N)ᶜ).toReal})
          atTop (nhds 0) ∧
        (∀ S (alpha : {a : Fin K → ℝ // a ∈ allocations}) tolerance,
          S.Nonempty → S ⊆ A → 0 < tolerance →
          S.card = 1 ∨ (2 ≤ S.card ∧
            ∀ cell ∈ covarianceCells S, CovarianceCellContains S v alpha.1 cell →
              (cellCertificate S cell tolerance).2.2.variancePartition = varianceCells ∧
                TrueParameterCertificateBenchmark S v alpha.1 M tolerance
                  (cellCertificate S cell tolerance))) ∧
        (∀ S alpha N O, S.Nonempty → S ⊆ A → O ∈ goodPilot S alpha N →
          let snappedV := snap (hatSigma alpha N O) alpha.1
          varianceAssignment snappedV ∈ varianceCells ∧
          InRationalCell snappedV (varianceAssignment snappedV) ∧
          varianceAssignment v ∈ varianceCells ∧ InRationalCell v (varianceAssignment v) ∧
          rateAssignment alpha.1 ∈ rateCells ∧ InRationalCell alpha.1 (rateAssignment alpha.1) ∧
          ((S.card = 1 ∧ ∀ tolerance,
              (certificate S alpha N O tolerance).2.1 = singletonActiveSelector S ∧
              selector alpha S N O tolerance = singletonActiveSelector S) ∨
            (2 ≤ S.card ∧ ∀ tolerance > 0,
              covarianceAssignment S snappedV alpha.1 ∈ covarianceCells S ∧
              covarianceAssignment S snappedV alpha.1 = covarianceAssignment S v alpha.1 ∧
              CovarianceCellContains S v alpha.1
                (covarianceAssignment S snappedV alpha.1) ∧
              CovarianceCellContains S snappedV alpha.1
                (covarianceAssignment S snappedV alpha.1) ∧
              IsCheckedCompactCertificate S snappedV alpha.1 M tolerance
                  (certificate S alpha N O tolerance) ∧
              (certificate S alpha N O tolerance).2.2.variancePartition = varianceCells ∧
              (certificate S alpha N O tolerance).2.2.ratePartition = rateCells ∧
              certificate S alpha N O tolerance =
                  cellCertificate S (covarianceAssignment S snappedV alpha.1) tolerance ∧
              covarianceAssignment S snappedV alpha.1 ∈
                  (certificate S alpha N O tolerance).2.2.covariancePartition ∧
              covarianceAssignment S snappedV alpha.1 ∈
                  (certificate S alpha N O tolerance).2.2.terminalBranchCells ∧
              (∃ terminal ∈ (certificate S alpha N O tolerance).2.2.terminalBranchCells,
                RationalCellRefines terminal (rateAssignment alpha.1) ∧
                  InRationalCell alpha.1 terminal) ∧
              selector alpha S N O tolerance =
                  (certificate S alpha N O tolerance).2.1))) ∧
        (∀ S alpha N O, S.Nonempty → S ⊆ A → O ∉ goodPilot S alpha N →
          ∀ tolerance, selector alpha S N O tolerance = fallback S) ∧
        (∃ scaledLocalRegretBound ≥ 0, ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
          ∀ (N : ℕ) (h : Fin K → ℝ) (x : ActiveIndex S → ℝ),
          h ∈ localDirections S → Real.sqrt N * |∑ a,
            fallback S x a * simpleRegret S
              (exactSliceWelfare (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹) m) a| ≤
                scaledLocalRegretBound) ∧
        (∀ fixedEpsilon > 0, ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
          (S.card = 1 ∧ ∀ (N : ℕ)
              (alpha : {a : Fin K → ℝ // a ∈ allocations}) h,
            h ∈ localDirections S →
            crSplitPrimitiveRisk (C := pilotTotal alpha N)
              (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹)
              (pilot alpha N) (counts alpha.1 N) m S
              (fun O => selector alpha S N O fixedEpsilon) N = 0) ∨
          (2 ≤ S.card ∧ Filter.limsup (fun (N : ℕ) => sSup {gap : ℝ |
            ∃ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∃ h ∈ localDirections S,
              gap = Real.sqrt N * crSplitPrimitiveRisk (C := pilotTotal alpha N)
                (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹)
                (pilot alpha N) (counts alpha.1 N) m S
                (fun O => selector alpha S N O fixedEpsilon) N -
              finiteContainingCertificateUpper S v alpha.1 (covarianceCells S)
                (fun cell => cellCertificate S cell fixedEpsilon)}) atTop ≤ 0)) ∧
        (∃ epsilonSeq : ℕ → ℝ, (∀ N, 0 < epsilonSeq N) ∧
          Antitone epsilonSeq ∧ Tendsto epsilonSeq atTop (nhds 0) ∧
          (∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
            (S.card = 1 ∨ Tendsto (fun (N : ℕ) => sSup {gap : ℝ |
              ∃ alpha : {a : Fin K → ℝ // a ∈ allocations},
                gap = |sSup {risk : ℝ | ∃ h ∈ localDirections S,
                  risk = Real.sqrt N * crSplitPrimitiveRisk (C := pilotTotal alpha N)
                    (leastFavourablePath P0 A m h (Real.sqrt N)⁻¹)
                    (pilot alpha N) (counts alpha.1 N) m S
                    (fun O => selector alpha S N O (epsilonSeq N)) N} -
                      gaussianCompactValueReal S v alpha.1 M|}) atTop (nhds 0)))) ∧
        (A = Finset.univ → ∀ alpha ∈ allocations, ∀ k, 0 < alpha k) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
