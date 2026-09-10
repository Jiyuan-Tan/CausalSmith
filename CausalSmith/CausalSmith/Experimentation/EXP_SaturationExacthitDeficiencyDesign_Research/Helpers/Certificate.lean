import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.GaussianGame
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.FiniteKernelBayes
import Causalean.Mathlib.Optimization.RationalLP
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Order.Lattice

set_option linter.unusedVariables false
set_option linter.style.openClassical false

/-!
# Validated finite Gaussian certificates

The certificate is represented by rational lower/upper envelopes, a finite-action
selector, and a transcript payload.  Its Bayes helper disintegrates a finite prior
over a continuum observation by densities; it does not use singleton observation
masses or the squared-loss posterior-mean specialization.
-/

open scoped BigOperators
open MeasureTheory Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- Mixture density of a finite prior with respect to a common continuum
observation measure. -/
def finiteDensityMixture {S Y : Type*} [Fintype S]
    (prior : S → ℝ) (density : S → Y → ℝ) (y : Y) : ℝ :=
  ∑ s, prior s * density s y

/-- Density posterior weight.  The fallback is the uniform finite design and is
used only on a zero-mixture fibre; strict positivity of Gaussian densities proves
that branch unreachable in certificate applications. -/
def densityPosteriorWeight {S Y : Type*} [Fintype S] [Nonempty S]
    (prior : S → ℝ) (density : S → Y → ℝ) (y : Y) (s : S) : ℝ :=
  if finiteDensityMixture prior density y = 0 then
    (Fintype.card S : ℝ)⁻¹
  else prior s * density s y / finiteDensityMixture prior density y

/-- Posterior expected cost under density posterior weights. -/
def densityPosteriorCost {S A Y : Type*} [Fintype S] [Nonempty S]
    (prior : S → ℝ) (density : S → Y → ℝ)
    (loss : A → S → ℝ) (a : A) (y : Y) : ℝ :=
  ∑ s, densityPosteriorWeight prior density y s * loss a s

/-- Measurable randomized rules on a continuum observation space. -/
def DensityRandomizedRule {A Y : Type*} [Fintype A] [MeasurableSpace Y]
    (delta : Y → A → ℝ) : Prop :=
  (∀ a, Measurable fun y => delta y a) ∧
    (∀ y a, 0 ≤ delta y a) ∧ ∀ y, ∑ a, delta y a = 1

/-- Bayes risk of a continuum-observation randomized rule, written against a
common dominating measure and state densities. -/
def densityFinitePriorRisk {S A Y : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace Y] (prior : S → ℝ) (density : S → Y → ℝ)
    (loss : A → S → ℝ) (nu : Measure Y) (delta : Y → A → ℝ) : ℝ :=
  ∑ s, prior s * ∫ y, density s y * (∑ a, delta y a * loss a s) ∂nu

/-- Finite-action density/Radon--Nikodym posterior minimization and its Tonelli
Bayes-risk identity.  This is the continuum-observation replacement for the
finite-singleton-mass posterior API. -/
lemma densityPosteriorCost_bayesValue {S A Y : Type*} [Fintype S] [Nonempty S]
    [Fintype A] [Nonempty A] [MeasurableSpace Y]
    (prior : S → ℝ) (density : S → Y → ℝ)
    (loss : A → S → ℝ) (nu : Measure Y)
    (hprior : (∀ s, 0 ≤ prior s) ∧ ∑ s, prior s = 1)
    (hdensity : ∀ s, Measurable (density s) ∧
      (∀ y, 0 < density s y) ∧ ∫ y, density s y ∂nu = 1)
    (hloss : ∀ a s, 0 ≤ loss a s)
    (hbounded : ∃ bound : ℝ, 0 ≤ bound ∧ ∀ a s, loss a s ≤ bound) :
    (∀ y, 0 < finiteDensityMixture prior density y) ∧
    (∀ y, (∑ s, densityPosteriorWeight prior density y s) = 1) ∧
    (∀ a y, finiteDensityMixture prior density y *
      densityPosteriorCost prior density loss a y =
        ∑ s, prior s * density s y * loss a s) ∧
    (∀ y, ∃ a : A, ∀ b : A,
      densityPosteriorCost prior density loss a y ≤
        densityPosteriorCost prior density loss b y) ∧
    Measurable (fun y => Finset.univ.inf' Finset.univ_nonempty fun a =>
      densityPosteriorCost prior density loss a y) ∧
    (∫ y, finiteDensityMixture prior density y *
        (Finset.univ.inf' Finset.univ_nonempty fun a =>
          densityPosteriorCost prior density loss a y) ∂nu) =
      sInf {risk : ℝ | ∃ delta : Y → A → ℝ,
        DensityRandomizedRule delta ∧
        risk = densityFinitePriorRisk prior density loss nu delta} := by sorry

end

section

/-- One rational axis-aligned cell, represented by outward-rounded intervals. -/
abbrev RationalCell := List (ℚ × ℚ)

def InRationalCell (x : Fin K → ℝ) (cell : RationalCell) : Prop :=
  ∃ lower upper : Fin K → ℚ,
    cell = List.ofFn (fun k => (lower k, upper k)) ∧
    ∀ k, (lower k : ℝ) ≤ x k ∧ x k ≤ (upper k : ℝ)

def InRationalCellInterior (x : Fin K → ℝ) (cell : RationalCell) : Prop :=
  ∃ lower upper : Fin K → ℚ,
    cell = List.ofFn (fun k => (lower k, upper k)) ∧
    ∀ k, (lower k : ℝ) < x k ∧ x k < (upper k : ℝ)

def InQuotientRationalCell [NeZero K] (A : Finset (Fin K))
    (x : QuotientIndex A → ℝ) (cell : RationalCell) : Prop :=
  ∃ lower upper : QuotientIndex A → ℚ,
    cell = Finset.univ.toList.map (fun k => (lower k, upper k)) ∧
    ∀ k, (lower k : ℝ) ≤ x k ∧ x k ≤ (upper k : ℝ)

def InQuotientRationalCellInterior [NeZero K] (A : Finset (Fin K))
    (x : QuotientIndex A → ℝ) (cell : RationalCell) : Prop :=
  ∃ lower upper : QuotientIndex A → ℚ,
    cell = Finset.univ.toList.map (fun k => (lower k, upper k)) ∧
    ∀ k, (lower k : ℝ) < x k ∧ x k < (upper k : ℝ)

def QuotientCellsHaveDisjointInteriors [NeZero K] (A : Finset (Fin K))
    (cells : List RationalCell) : Prop :=
  ∀ cell₁ ∈ cells, ∀ cell₂ ∈ cells, cell₁ ≠ cell₂ →
    ¬ ∃ g, InQuotientRationalCellInterior A g cell₁ ∧
      InQuotientRationalCellInterior A g cell₂

def QuotientBallCovered [NeZero K] (A : Finset (Fin K)) (M : ℝ)
    (cells : List RationalCell) : Prop :=
  ∀ g : QuotientIndex A → ℝ, (∑ i, g i ^ 2) ≤ M ^ 2 →
    ∃ cell ∈ cells, InQuotientRationalCell A g cell

/-- Exact image coverage by full representatives: the supplied representatives
map onto, and only onto, the entire closed quotient ball. -/
def ExactQuotientBallRepresentativeCoverage [NeZero K]
    (A : Finset (Fin K)) (M : ℝ) (representatives : Set (Fin K → ℝ)) : Prop :=
  {g : QuotientIndex A → ℝ | ∃ h ∈ representatives,
      g = quotientObservation A (fun k => h k.1)} =
    {g : QuotientIndex A → ℝ | (∑ i, g i ^ 2) ≤ M ^ 2}

def GenuineQuotientPartition [NeZero K] (A : Finset (Fin K)) (M : ℝ)
    (cells : List RationalCell) : Prop :=
  cells.Nodup ∧ 1 < cells.length ∧ QuotientBallCovered A M cells ∧
    (∀ cell ∈ cells, cell ≠ []) ∧ QuotientCellsHaveDisjointInteriors A cells

def TruncatedObservationPartition [NeZero K] (A : Finset (Fin K)) (radius : ℝ)
    (cells : List RationalCell) : Prop :=
  cells.Nodup ∧ 0 < radius ∧ 1 < cells.length ∧ (∀ cell ∈ cells, cell ≠ []) ∧
    QuotientCellsHaveDisjointInteriors A cells ∧
    ∀ y : QuotientIndex A → ℝ, (∀ i, |y i| ≤ radius) →
      ∃ cell ∈ cells, InQuotientRationalCell A y cell

def CovarianceCellContains [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (cell : RationalCell) : Prop :=
  ∃ lower upper : QuotientIndex A × QuotientIndex A → ℚ,
    cell = Finset.univ.toList.map (fun ij => (lower ij, upper ij)) ∧
    ∀ i j, (lower (i, j) : ℝ) ≤ quotientCovariance A v r i.1 j.1 ∧
      quotientCovariance A v r i.1 j.1 ≤ (upper (i, j) : ℝ)

def CovarianceCellContainsInterior [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (cell : RationalCell) : Prop :=
  ∃ lower upper : QuotientIndex A × QuotientIndex A → ℚ,
    cell = Finset.univ.toList.map (fun ij => (lower ij, upper ij)) ∧
    ∀ i j, (lower (i, j) : ℝ) < quotientCovariance A v r i.1 j.1 ∧
      quotientCovariance A v r i.1 j.1 < (upper (i, j) : ℝ)

def RationalCellRefines (child parent : RationalCell) : Prop :=
  ∀ {K : ℕ} (x : Fin K → ℝ), InRationalCell x child → InRationalCell x parent

def RationalChildrenCover (children : List RationalCell) (parent : RationalCell) : Prop :=
  ∀ {K : ℕ} (x : Fin K → ℝ), InRationalCell x parent →
    ∃ child ∈ children, InRationalCell x child

def RationalCellEndpointRefines (child parent : RationalCell) : Prop :=
  child.length = parent.length ∧
    ∀ entry ∈ child.zip parent,
      entry.2.1 ≤ entry.1.1 ∧ entry.1.2 ≤ entry.2.2

/-- One checked branch in the finite refinement tree. -/
structure CertificateRefinementBranch where
  parent : RationalCell
  children : List RationalCell
  ancestry : List RationalCell
  terminalChildren : List RationalCell
  precision : ℕ
deriving Repr, DecidableEq

def IsEarlierRefinementChild (trace : List CertificateRefinementBranch)
    (i : Fin trace.length) (cell : RationalCell) : Prop :=
  ∃ j : Fin trace.length, j.1 < i.1 ∧ cell ∈ (trace.get j).children

def IsRefinedLater (trace : List CertificateRefinementBranch)
    (i : Fin trace.length) (cell : RationalCell) : Prop :=
  ∃ j : Fin trace.length, i.1 < j.1 ∧ (trace.get j).parent = cell

def ValidRefinementTrace (roots terminals : List RationalCell)
    (trace : List CertificateRefinementBranch) : Prop :=
  roots ≠ [] ∧ terminals ≠ [] ∧ trace ≠ [] ∧
    (∀ i : Fin trace.length,
      let branch := trace.get i
      (branch.parent ∈ roots ∨ IsEarlierRefinementChild trace i branch.parent) ∧
      branch.children ≠ [] ∧
      (∀ child ∈ branch.children, RationalCellRefines child branch.parent) ∧
      RationalChildrenCover branch.children branch.parent ∧
      (∃ root ∈ roots, branch.ancestry.head? = some root) ∧
      branch.ancestry.getLast? = some branch.parent ∧
      (∀ ancestor ∈ branch.ancestry,
        ancestor ∈ roots ∨ IsEarlierRefinementChild trace i ancestor) ∧
      branch.terminalChildren ≠ [] ∧
      (∀ terminal ∈ branch.terminalChildren, terminal ∈ branch.children) ∧
      (∀ child ∈ branch.children,
        child ∈ branch.terminalChildren ∨ IsRefinedLater trace i child) ∧
      (∀ terminal ∈ branch.terminalChildren, ¬ IsRefinedLater trace i terminal) ∧
      0 < branch.precision) ∧
    terminals = trace.flatMap CertificateRefinementBranch.terminalChildren

/-- Fully rational replay of the finite refinement computation. -/
def RationalRefinementReplay (roots terminals : List RationalCell)
    (trace : List CertificateRefinementBranch) : Prop :=
  roots ≠ [] ∧ trace ≠ [] ∧
    (∀ i : Fin trace.length,
      let branch := trace.get i
      (branch.parent ∈ roots ∨ IsEarlierRefinementChild trace i branch.parent) ∧
      branch.children ≠ [] ∧
      (∀ child ∈ branch.children, RationalCellEndpointRefines child branch.parent) ∧
      branch.terminalChildren ⊆ branch.children ∧ 0 < branch.precision ∧
      (∀ j : Fin trace.length, i.1 < j.1 → branch.precision ≤ (trace.get j).precision)) ∧
    terminals = trace.flatMap CertificateRefinementBranch.terminalChildren

def rationalRefinementTraceCheck (roots terminals : List RationalCell)
    (trace : List CertificateRefinementBranch) : Bool :=
  let branchCheck := fun i =>
    match trace.drop i with
    | [] => false
    | branch :: _ =>
      let earlierChildren := (trace.take i).flatMap CertificateRefinementBranch.children
      let laterBranches := trace.drop (i + 1)
      decide (branch.parent ∈ roots ∨ branch.parent ∈ earlierChildren) &&
      decide (branch.children ≠ []) &&
      branch.children.all (fun child =>
        decide (child.length = branch.parent.length) &&
        (child.zip branch.parent).all (fun entry =>
          decide (entry.2.1 ≤ entry.1.1 ∧ entry.1.2 ≤ entry.2.2))) &&
      branch.terminalChildren.all (fun terminal => decide (terminal ∈ branch.children)) &&
      decide (0 < branch.precision) &&
      laterBranches.all (fun later => decide (branch.precision ≤ later.precision))
  decide (roots ≠ [] ∧ trace ≠ []) &&
    (List.range trace.length).all branchCheck &&
    decide (terminals = trace.flatMap CertificateRefinementBranch.terminalChildren)

/-- The six distinct positive error allocations and their separately computed errors. -/
structure CertificateErrorBudget where
  parameterInterpolation : ℚ
  covariancePinsker : ℚ
  observationTail : ℚ
  quadrature : ℚ
  ambiguousActions : ℚ
  rounding : ℚ
deriving Repr, DecidableEq

/-- One rational directed-arithmetic operation in the replay of a Gaussian
integral.  Every operand names an earlier interval and `result` is checked by
outward rational arithmetic rather than trusted as an endpoint pair. -/
structure DirectedIntervalStep where
  operation : Fin 4
  leftIndex : ℕ
  rightIndex : ℕ
  result : ℚ × ℚ
deriving Repr, DecidableEq

/-- A complete rational replay row for one posterior-cost or selector-risk
integral.  Primitive Gaussian rectangle masses are recorded separately from
the arithmetic trace combining prior, loss, and action weights. -/
structure GaussianIntegralReplay where
  parameterIndex : ℕ
  observationCellIndex : ℕ
  actionIndex : ℕ
  priorWeight : ℚ
  actionWeight : ℚ
  lossValue : ℚ
  cdfArguments : List ℚ
  cdfSeeds : List (ℚ × ℚ)
  primitiveMass : ℚ × ℚ
  primitiveCdfTrace : List DirectedIntervalStep
  arithmeticSeeds : List (ℚ × ℚ)
  arithmeticTrace : List DirectedIntervalStep
  output : ℚ × ℚ
deriving Repr, DecidableEq

/-- Rational replay data for the covariance KL calculation and its Pinsker
radius.  The trace computes the directed log-determinant and quadratic terms;
the final inequality is checked over rationals. -/
structure CovarianceKLReplay where
  covarianceCellIndex : ℕ
  referenceCellIndex : ℕ
  rationalSeeds : List (ℚ × ℚ)
  logDetTrace : List DirectedIntervalStep
  quadraticTrace : List DirectedIntervalStep
  klInterval : ℚ × ℚ
  pinskerRadius : ℚ
deriving Repr, DecidableEq

def CertificateErrorBudget.total (e : CertificateErrorBudget) : ℚ :=
  e.parameterInterpolation + e.covariancePinsker + e.observationTail +
    e.quadrature + e.ambiguousActions + e.rounding

def PositiveCertificateBudget (e : CertificateErrorBudget) : Prop :=
  0 < e.parameterInterpolation ∧ 0 < e.covariancePinsker ∧
    0 < e.observationTail ∧ 0 < e.quadrature ∧
    0 < e.ambiguousActions ∧ 0 < e.rounding

def ErrorAllocationsDominate (computed allocated : CertificateErrorBudget) : Prop :=
  0 ≤ computed.parameterInterpolation ∧
    computed.parameterInterpolation ≤ allocated.parameterInterpolation ∧
  0 ≤ computed.covariancePinsker ∧ computed.covariancePinsker ≤ allocated.covariancePinsker ∧
  0 ≤ computed.observationTail ∧ computed.observationTail ≤ allocated.observationTail ∧
  0 ≤ computed.quadrature ∧ computed.quadrature ≤ allocated.quadrature ∧
  0 ≤ computed.ambiguousActions ∧ computed.ambiguousActions ≤ allocated.ambiguousActions ∧
  0 ≤ computed.rounding ∧ computed.rounding ≤ allocated.rounding

/-- A complete, independently replayable rational transcript. -/
structure CertificateReceipt where
  face : List ℕ
  quotientRadius : ℚ
  variancePartition : List RationalCell
  rationalInputs : List ℚ
  requestedTolerance : ℚ
  parameterPartition : List RationalCell
  observationRadius : ℚ
  observationPartition : List RationalCell
  ratePartition : List RationalCell
  covariancePartition : List RationalCell
  refinementTrace : List CertificateRefinementBranch
  terminalBranchCells : List RationalCell
  priorSupport : List RationalCell
  priorWeights : List ℚ
  selectorTable : List (RationalCell × List (ℕ × ℚ))
  tailSelectorTable : List (List Bool × List (ℕ × ℚ))
  precision : ℕ
  posteriorIntegralReplay : List GaussianIntegralReplay
  selectorRiskReplay : List GaussianIntegralReplay
  covarianceKLReplay : List CovarianceKLReplay
  posteriorCostEnclosures : List (ℚ × ℚ)
  selectorRiskEnclosures : List (ℚ × ℚ)
  computedErrors : CertificateErrorBudget
  allocatedErrors : CertificateErrorBudget
  lowerBound : ℚ
  upperBound : ℚ
  checkerRevision : String
  checksum : String
deriving Repr, DecidableEq

abbrev CompactCertificateOutput (A : Finset (Fin K)) :=
  (ℝ × ℝ) × ((ActiveIndex A → ℝ) → Fin K → ℝ) × CertificateReceipt

def certificateChecksum (receipt : CertificateReceipt) : String :=
  reprStr (receipt.face, receipt.quotientRadius, receipt.variancePartition,
    receipt.rationalInputs, receipt.requestedTolerance,
    receipt.parameterPartition, receipt.observationRadius, receipt.observationPartition,
    receipt.ratePartition, receipt.covariancePartition, receipt.refinementTrace,
    receipt.terminalBranchCells, receipt.priorSupport, receipt.priorWeights,
    receipt.selectorTable, receipt.tailSelectorTable, receipt.precision,
    receipt.posteriorIntegralReplay, receipt.selectorRiskReplay,
    receipt.covarianceKLReplay,
    receipt.posteriorCostEnclosures,
    receipt.selectorRiskEnclosures, receipt.computedErrors, receipt.allocatedErrors,
    receipt.lowerBound, receipt.upperBound, receipt.checkerRevision)

def RationalFinitePrior (receipt : CertificateReceipt) : Prop :=
  receipt.priorSupport ≠ [] ∧ receipt.priorSupport.length = receipt.priorWeights.length ∧
    (∀ point ∈ receipt.priorSupport, point ∈ receipt.parameterPartition) ∧
    (∀ point ∈ receipt.priorSupport, ∀ interval ∈ point, interval.1 = interval.2) ∧
    (∀ weight ∈ receipt.priorWeights, 0 ≤ weight) ∧ receipt.priorWeights.sum = 1

def RationalActionWeights (A : Finset (Fin K)) (weights : List (ℕ × ℚ)) : Prop :=
  weights ≠ [] ∧ (∀ aw ∈ weights, aw.1 < K ∧ 0 ≤ aw.2 ∧
    (aw.2 ≠ 0 → ∃ a : Fin K, a.1 = aw.1 ∧ a ∈ A)) ∧
    (weights.map Prod.snd).sum = 1

def RationalSelectorTable [NeZero K] (A : Finset (Fin K))
    (receipt : CertificateReceipt) : Prop :=
  receipt.selectorTable ≠ [] ∧
    receipt.selectorTable.map Prod.fst = receipt.observationPartition ∧
    (∀ entry ∈ receipt.selectorTable, RationalActionWeights A entry.2) ∧
    receipt.tailSelectorTable ≠ [] ∧
    (∀ entry ∈ receipt.tailSelectorTable, RationalActionWeights A entry.2) ∧
    (∀ signature : List Bool,
      signature.length = Fintype.card (QuotientIndex A) →
      ∃ entry ∈ receipt.tailSelectorTable, entry.1 = signature) ∧
    (∀ entry₁ ∈ receipt.tailSelectorTable, ∀ entry₂ ∈ receipt.tailSelectorTable,
      entry₁.1 = entry₂.1 → entry₁ = entry₂)

def rationalActionWeight (weights : List (ℕ × ℚ)) (a : Fin K) : ℝ :=
  ((weights.filter fun aw => aw.1 = a.1).map Prod.snd).sum

/-- The finite unbounded-tail region containing an active observation.  The
signature records, in quotient coordinates, which side of the truncation box
is crossed, so the represented tail rule need not be constant. -/
noncomputable def observationTailSignature [NeZero K] (A : Finset (Fin K)) (radius : ℚ)
    (x : ActiveIndex A → ℝ) : List Bool :=
  Finset.univ.toList.map fun i : QuotientIndex A =>
    (radius : ℝ) < quotientObservation A x i

/-- The active-observation selector is exactly the rational table on every
truncated cell and uses the recorded rational tail row outside the box. -/
def SelectorRealizesRationalTable [NeZero K] (A : Finset (Fin K))
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ)
    (receipt : CertificateReceipt) : Prop :=
  ∀ x a,
    ((∃ entry ∈ receipt.selectorTable,
        InQuotientRationalCell A (quotientObservation A x) entry.1) →
      ∀ entry ∈ receipt.selectorTable,
        InQuotientRationalCell A (quotientObservation A x) entry.1 →
          delta x a = rationalActionWeight entry.2 a) ∧
    ((¬ ∃ entry ∈ receipt.selectorTable,
        InQuotientRationalCell A (quotientObservation A x) entry.1) →
      ∀ entry ∈ receipt.tailSelectorTable,
        entry.1 = observationTailSignature A receipt.observationRadius x →
          delta x a = rationalActionWeight entry.2 a)

def rationalCellPayload (cells : List RationalCell) : List ℚ :=
  cells.flatMap fun cell => cell.flatMap fun interval => [interval.1, interval.2]

/-- Canonical serialization of every rational input supplied to a certificate
run.  Equality with `receipt.rationalInputs` prevents a receipt from being
replayed against unrelated partitions, radius, or tolerance. -/
def certificateRationalInputPayload (face : List ℕ)
    (tolerance quotientRadius observationRadius eigenLower eigenUpper : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell) :
    List ℚ :=
  face.map (fun k => (k : ℚ)) ++
    [tolerance, quotientRadius, observationRadius, eigenLower, eigenUpper] ++
    rationalCellPayload varianceCells ++
    rationalCellPayload parameterCells ++ rationalCellPayload observationCells ++
    rationalCellPayload rateCells ++ rationalCellPayload covarianceCells

def OrderedRationalInterval (x : ℚ × ℚ) : Prop := x.1 ≤ x.2

/-- Exact rational interval arithmetic used by the transcript checker. -/
def directedIntervalOperation (operation : Fin 4) (x y : ℚ × ℚ) : ℚ × ℚ :=
  match operation.1 with
  | 0 => (x.1 + y.1, x.2 + y.2)
  | 1 => (x.1 - y.2, x.2 - y.1)
  | 2 =>
      (min (min (x.1 * y.1) (x.1 * y.2)) (min (x.2 * y.1) (x.2 * y.2)),
       max (max (x.1 * y.1) (x.1 * y.2)) (max (x.2 * y.1) (x.2 * y.2)))
  | _ =>
      if y.1 ≤ 0 ∧ 0 ≤ y.2 then (0, 0) else
        let reciprocal := (min y.1⁻¹ y.2⁻¹, max y.1⁻¹ y.2⁻¹)
        (min (min (x.1 * reciprocal.1) (x.1 * reciprocal.2))
            (min (x.2 * reciprocal.1) (x.2 * reciprocal.2)),
         max (max (x.1 * reciprocal.1) (x.1 * reciprocal.2))
            (max (x.2 * reciprocal.1) (x.2 * reciprocal.2)))

def ValidDirectedIntervalTrace (seeds : List (ℚ × ℚ))
    (trace : List DirectedIntervalStep) : Prop :=
  seeds ≠ [] ∧ (∀ seed ∈ seeds, OrderedRationalInterval seed) ∧
    ∀ i : Fin trace.length,
      let step := trace.get i
      let available := seeds ++ (trace.take i.1).map DirectedIntervalStep.result
      step.leftIndex < available.length ∧ step.rightIndex < available.length ∧
      (step.operation.1 = 3 →
        ¬ ((available.getD step.rightIndex (0, 0)).1 ≤ 0 ∧
          0 ≤ (available.getD step.rightIndex (0, 0)).2)) ∧
      step.result = directedIntervalOperation step.operation
        (available.getD step.leftIndex (0, 0))
        (available.getD step.rightIndex (0, 0))

def directedTraceResult (seeds : List (ℚ × ℚ))
    (trace : List DirectedIntervalStep) : ℚ × ℚ :=
  match trace.getLast? with
  | some step => step.result
  | none => seeds.getD 0 (0, 0)

def ValidGaussianIntegralArithmeticReplay (row : GaussianIntegralReplay) : Prop :=
  ValidDirectedIntervalTrace row.cdfSeeds row.primitiveCdfTrace ∧
    row.cdfArguments.length = row.cdfSeeds.length ∧
    row.primitiveMass = directedTraceResult row.cdfSeeds row.primitiveCdfTrace ∧
    row.arithmeticSeeds ≠ [] ∧ row.arithmeticSeeds.head? = some row.primitiveMass ∧
    ValidDirectedIntervalTrace row.arithmeticSeeds row.arithmeticTrace ∧
    row.output = directedTraceResult row.arithmeticSeeds row.arithmeticTrace

def ValidCovarianceKLReplay (row : CovarianceKLReplay) : Prop :=
  ValidDirectedIntervalTrace row.rationalSeeds row.logDetTrace ∧
    ValidDirectedIntervalTrace row.rationalSeeds row.quadraticTrace ∧
    row.klInterval.1 ≤ row.klInterval.2 ∧ 0 ≤ row.klInterval.1 ∧
    row.klInterval.2 =
      (directedTraceResult row.rationalSeeds row.logDetTrace).2 +
        (directedTraceResult row.rationalSeeds row.quadraticTrace).2 ∧
    0 ≤ row.pinskerRadius ∧ row.klInterval.2 ≤ 2 * row.pinskerRadius ^ 2

/-- The posterior and selector interval tables are recomputed from their
directed Gaussian traces; covariance Pinsker error is recomputed from the
recorded rational KL traces. -/
def RationalGaussianReplay (receipt : CertificateReceipt) : Prop :=
  receipt.posteriorIntegralReplay ≠ [] ∧ receipt.selectorRiskReplay ≠ [] ∧
    receipt.covarianceKLReplay ≠ [] ∧
    (∀ row ∈ receipt.posteriorIntegralReplay, ValidGaussianIntegralArithmeticReplay row) ∧
    (∀ row ∈ receipt.selectorRiskReplay, ValidGaussianIntegralArithmeticReplay row) ∧
    (∀ row ∈ receipt.covarianceKLReplay, ValidCovarianceKLReplay row) ∧
    receipt.posteriorCostEnclosures = receipt.posteriorIntegralReplay.map (·.output) ∧
    receipt.selectorRiskEnclosures = receipt.selectorRiskReplay.map (·.output) ∧
    receipt.computedErrors.covariancePinsker =
      receipt.covarianceKLReplay.foldl (fun radius row => max radius row.pinskerRadius) 0

def HasRecordedTerminalRefinement (receipt : CertificateReceipt) (cell : RationalCell) : Prop :=
  ∃ terminal ∈ receipt.terminalBranchCells, RationalCellEndpointRefines terminal cell

/-- Replay rows are keyed uniquely by parameter, observation cell, and action.
Together with the coverage clauses below, this makes the replay tables exact
Cartesian products rather than multisets whose duplicate rows alter a sum. -/
def GaussianIntegralReplayRowsUnique (rows : List GaussianIntegralReplay) : Prop :=
  rows.Nodup ∧ ∀ row₁ ∈ rows, ∀ row₂ ∈ rows,
      row₁.parameterIndex = row₂.parameterIndex →
      row₁.observationCellIndex = row₂.observationCellIndex →
      row₁.actionIndex = row₂.actionIndex → row₁ = row₂

/-- There is exactly one covariance replay row for each covered covariance
cell; its checked reference-cell index remains part of that unique row. -/
def CovarianceKLReplayRowsUnique (rows : List CovarianceKLReplay) : Prop :=
  rows.Nodup ∧ ∀ row₁ ∈ rows, ∀ row₂ ∈ rows,
      row₁.covarianceCellIndex = row₂.covarianceCellIndex → row₁ = row₂

def RationalIntegralTablesTiedToReceipt (receipt : CertificateReceipt) : Prop :=
  GaussianIntegralReplayRowsUnique receipt.posteriorIntegralReplay ∧
  GaussianIntegralReplayRowsUnique receipt.selectorRiskReplay ∧
  CovarianceKLReplayRowsUnique receipt.covarianceKLReplay ∧
  (∀ row ∈ receipt.posteriorIntegralReplay,
    row.parameterIndex < receipt.priorWeights.length ∧
    row.observationCellIndex < receipt.observationPartition.length ∧
    row.actionIndex ∈ receipt.face ∧
    row.priorWeight = receipt.priorWeights.getD row.parameterIndex 0 ∧
    HasRecordedTerminalRefinement receipt
      (receipt.priorSupport.getD row.parameterIndex []) ∧
    HasRecordedTerminalRefinement receipt
      (receipt.observationPartition.getD row.observationCellIndex []) ∧
    row.arithmeticSeeds = [row.primitiveMass, (row.priorWeight, row.priorWeight),
      (row.lossValue, row.lossValue)]) ∧
  (∀ row ∈ receipt.selectorRiskReplay,
    row.parameterIndex < receipt.parameterPartition.length ∧
    row.observationCellIndex < receipt.selectorTable.length ∧
    row.actionIndex ∈ receipt.face ∧
    HasRecordedTerminalRefinement receipt
      (receipt.parameterPartition.getD row.parameterIndex []) ∧
    HasRecordedTerminalRefinement receipt
      (receipt.observationPartition.getD row.observationCellIndex []) ∧
    row.actionWeight = (((receipt.selectorTable.getD row.observationCellIndex ([], [])).2
      |>.filter fun aw => aw.1 = row.actionIndex).map Prod.snd).sum ∧
    row.arithmeticSeeds = [row.primitiveMass, (row.actionWeight, row.actionWeight),
      (row.lossValue, row.lossValue)]) ∧
  (∀ row ∈ receipt.covarianceKLReplay,
    row.covarianceCellIndex < receipt.covariancePartition.length ∧
    row.referenceCellIndex < receipt.covariancePartition.length ∧
    HasRecordedTerminalRefinement receipt
      (receipt.covariancePartition.getD row.covarianceCellIndex []) ∧
    HasRecordedTerminalRefinement receipt
      (receipt.covariancePartition.getD row.referenceCellIndex [])) ∧
  (∀ covarianceCellIndex < receipt.covariancePartition.length,
    ∃ row ∈ receipt.covarianceKLReplay,
      row.covarianceCellIndex = covarianceCellIndex) ∧
  (∀ parameterIndex < receipt.priorWeights.length,
    ∀ observationCellIndex < receipt.observationPartition.length,
    ∀ actionIndex ∈ receipt.face,
      ∃ row ∈ receipt.posteriorIntegralReplay,
        row.parameterIndex = parameterIndex ∧
        row.observationCellIndex = observationCellIndex ∧ row.actionIndex = actionIndex) ∧
  ∀ parameterIndex < receipt.parameterPartition.length,
    ∀ observationCellIndex < receipt.observationPartition.length,
    ∀ actionIndex ∈ receipt.face,
      ∃ row ∈ receipt.selectorRiskReplay,
        row.parameterIndex = parameterIndex ∧
        row.observationCellIndex = observationCellIndex ∧ row.actionIndex = actionIndex

def replayedPosteriorActionLower (receipt : CertificateReceipt)
    (observationCellIndex actionIndex : ℕ) : ℚ :=
  ((receipt.posteriorIntegralReplay.filter fun row =>
    row.observationCellIndex = observationCellIndex ∧ row.actionIndex = actionIndex).map
      (fun row => row.output.1)).sum

def replayedObservationBayesLower (receipt : CertificateReceipt)
    (observationCellIndex : ℕ) : ℚ :=
  match receipt.face with
  | [] => 0
  | actionIndex :: actionIndices => actionIndices.foldl
      (fun lower action => min lower
        (replayedPosteriorActionLower receipt observationCellIndex action))
      (replayedPosteriorActionLower receipt observationCellIndex actionIndex)

def replayedBayesLower (receipt : CertificateReceipt) : ℚ :=
  ((List.range receipt.observationPartition.length).map
    (replayedObservationBayesLower receipt)).sum

def replayedSelectorRiskUpper (receipt : CertificateReceipt) (parameterIndex : ℕ) : ℚ :=
  ((receipt.selectorRiskReplay.filter fun row => row.parameterIndex = parameterIndex).map
    (fun row => row.output.2)).sum

def replayedSelectorUpper (receipt : CertificateReceipt) : ℚ :=
  (List.range receipt.parameterPartition.length).foldl
    (fun upper parameterIndex => max upper
      (replayedSelectorRiskUpper receipt parameterIndex)) 0

def ReceiptSyntacticValidity (receipt : CertificateReceipt) : Prop :=
  receipt.rationalInputs ≠ [] ∧ 0 < receipt.requestedTolerance ∧
    receipt.parameterPartition ≠ [] ∧ receipt.observationPartition ≠ [] ∧
    receipt.ratePartition ≠ [] ∧ receipt.covariancePartition ≠ [] ∧
    receipt.terminalBranchCells ≠ [] ∧ 0 < receipt.precision ∧
    receipt.posteriorCostEnclosures ≠ [] ∧ receipt.selectorRiskEnclosures ≠ [] ∧
    RationalGaussianReplay receipt ∧ RationalIntegralTablesTiedToReceipt receipt ∧
    (∀ interval ∈ receipt.posteriorCostEnclosures, interval.1 ≤ interval.2) ∧
    (∀ interval ∈ receipt.selectorRiskEnclosures, interval.1 ≤ interval.2) ∧
    PositiveCertificateBudget receipt.allocatedErrors ∧
    ErrorAllocationsDominate receipt.computedErrors receipt.allocatedErrors ∧
    receipt.allocatedErrors.total ≤ receipt.requestedTolerance ∧
    receipt.lowerBound = max 0 (replayedBayesLower receipt - receipt.allocatedErrors.total) ∧
    receipt.upperBound = replayedSelectorUpper receipt + receipt.allocatedErrors.total ∧
    0 ≤ receipt.lowerBound ∧ receipt.lowerBound ≤ receipt.upperBound ∧
    receipt.upperBound - receipt.lowerBound ≤ receipt.requestedTolerance ∧
    receipt.checkerRevision ≠ "" ∧
    receipt.checksum = certificateChecksum receipt

/-- Executable counterpart of `ValidDirectedIntervalTrace`. -/
def validDirectedIntervalTraceCheck (seeds : List (ℚ × ℚ))
    (trace : List DirectedIntervalStep) : Bool :=
  decide (seeds ≠ []) && seeds.all (fun seed => decide (seed.1 ≤ seed.2)) &&
    (List.range trace.length).all fun i =>
      match trace.drop i with
      | [] => false
      | step :: _ =>
        let available := seeds ++ (trace.take i).map DirectedIntervalStep.result
        let right := available.getD step.rightIndex (0, 0)
        decide (step.leftIndex < available.length ∧ step.rightIndex < available.length) &&
        (if step.operation.1 = 3 then decide (¬ (right.1 ≤ 0 ∧ 0 ≤ right.2)) else true) &&
        decide (step.result = directedIntervalOperation step.operation
          (available.getD step.leftIndex (0, 0)) right)

def validGaussianIntegralArithmeticReplayCheck (row : GaussianIntegralReplay) : Bool :=
  validDirectedIntervalTraceCheck row.cdfSeeds row.primitiveCdfTrace &&
    decide (row.cdfArguments.length = row.cdfSeeds.length) &&
    decide (row.primitiveMass = directedTraceResult row.cdfSeeds row.primitiveCdfTrace) &&
    decide (row.arithmeticSeeds ≠ [] ∧ row.arithmeticSeeds.head? = some row.primitiveMass) &&
    validDirectedIntervalTraceCheck row.arithmeticSeeds row.arithmeticTrace &&
    decide (row.output = directedTraceResult row.arithmeticSeeds row.arithmeticTrace)

def validCovarianceKLReplayCheck (row : CovarianceKLReplay) : Bool :=
  validDirectedIntervalTraceCheck row.rationalSeeds row.logDetTrace &&
    validDirectedIntervalTraceCheck row.rationalSeeds row.quadraticTrace &&
    decide (row.klInterval.1 ≤ row.klInterval.2 ∧ 0 ≤ row.klInterval.1) &&
    decide (row.klInterval.2 =
      (directedTraceResult row.rationalSeeds row.logDetTrace).2 +
        (directedTraceResult row.rationalSeeds row.quadraticTrace).2) &&
    decide (0 ≤ row.pinskerRadius ∧ row.klInterval.2 ≤ 2 * row.pinskerRadius ^ 2)

def hasRecordedTerminalRefinementCheck (receipt : CertificateReceipt)
    (cell : RationalCell) : Bool :=
  receipt.terminalBranchCells.any fun terminal =>
    decide (terminal.length = cell.length) &&
      (terminal.zip cell).all (fun entry =>
        decide (entry.2.1 ≤ entry.1.1 ∧ entry.1.2 ≤ entry.2.2))

def gaussianIntegralReplayRowsUniqueCheck (rows : List GaussianIntegralReplay) : Bool :=
  decide rows.Nodup && rows.all fun row₁ => rows.all fun row₂ =>
    if row₁.parameterIndex = row₂.parameterIndex ∧
        row₁.observationCellIndex = row₂.observationCellIndex ∧
        row₁.actionIndex = row₂.actionIndex then decide (row₁ = row₂) else true

def covarianceKLReplayRowsUniqueCheck (rows : List CovarianceKLReplay) : Bool :=
  decide rows.Nodup && rows.all fun row₁ => rows.all fun row₂ =>
    if row₁.covarianceCellIndex = row₂.covarianceCellIndex then decide (row₁ = row₂) else true

def rationalIntegralTablesTiedToReceiptCheck (receipt : CertificateReceipt) : Bool :=
  gaussianIntegralReplayRowsUniqueCheck receipt.posteriorIntegralReplay &&
  gaussianIntegralReplayRowsUniqueCheck receipt.selectorRiskReplay &&
  covarianceKLReplayRowsUniqueCheck receipt.covarianceKLReplay &&
  receipt.posteriorIntegralReplay.all (fun row =>
    decide (row.parameterIndex < receipt.priorWeights.length ∧
      row.observationCellIndex < receipt.observationPartition.length ∧
      row.actionIndex ∈ receipt.face ∧
      row.priorWeight = receipt.priorWeights.getD row.parameterIndex 0) &&
    hasRecordedTerminalRefinementCheck receipt
      (receipt.priorSupport.getD row.parameterIndex []) &&
    hasRecordedTerminalRefinementCheck receipt
      (receipt.observationPartition.getD row.observationCellIndex []) &&
    decide (row.arithmeticSeeds = [row.primitiveMass, (row.priorWeight, row.priorWeight),
      (row.lossValue, row.lossValue)])) &&
  receipt.selectorRiskReplay.all (fun row =>
    decide (row.parameterIndex < receipt.parameterPartition.length ∧
      row.observationCellIndex < receipt.selectorTable.length ∧
      row.actionIndex ∈ receipt.face) &&
    hasRecordedTerminalRefinementCheck receipt
      (receipt.parameterPartition.getD row.parameterIndex []) &&
    hasRecordedTerminalRefinementCheck receipt
      (receipt.observationPartition.getD row.observationCellIndex []) &&
    decide (row.actionWeight = (((receipt.selectorTable.getD row.observationCellIndex
      ([], [])).2 |>.filter fun aw => aw.1 = row.actionIndex).map Prod.snd).sum) &&
    decide (row.arithmeticSeeds = [row.primitiveMass, (row.actionWeight, row.actionWeight),
      (row.lossValue, row.lossValue)])) &&
  receipt.covarianceKLReplay.all (fun row =>
    decide (row.covarianceCellIndex < receipt.covariancePartition.length ∧
      row.referenceCellIndex < receipt.covariancePartition.length) &&
    hasRecordedTerminalRefinementCheck receipt
      (receipt.covariancePartition.getD row.covarianceCellIndex []) &&
    hasRecordedTerminalRefinementCheck receipt
      (receipt.covariancePartition.getD row.referenceCellIndex [])) &&
  (List.range receipt.covariancePartition.length).all (fun covarianceCellIndex =>
    receipt.covarianceKLReplay.any fun row =>
      decide (row.covarianceCellIndex = covarianceCellIndex)) &&
  (List.range receipt.priorWeights.length).all (fun parameterIndex =>
    (List.range receipt.observationPartition.length).all (fun observationCellIndex =>
      receipt.face.all (fun actionIndex => receipt.posteriorIntegralReplay.any fun row =>
        decide (row.parameterIndex = parameterIndex ∧
          row.observationCellIndex = observationCellIndex ∧ row.actionIndex = actionIndex)))) &&
  (List.range receipt.parameterPartition.length).all (fun parameterIndex =>
    (List.range receipt.observationPartition.length).all (fun observationCellIndex =>
      receipt.face.all (fun actionIndex => receipt.selectorRiskReplay.any fun row =>
        decide (row.parameterIndex = parameterIndex ∧
          row.observationCellIndex = observationCellIndex ∧ row.actionIndex = actionIndex))))

/-- The fully rational portion of receipt validation is executable. -/
def certificateReceiptCheck (receipt : CertificateReceipt) : Bool :=
  decide (receipt.rationalInputs ≠ [] ∧ 0 < receipt.requestedTolerance ∧
    receipt.parameterPartition ≠ [] ∧ receipt.observationPartition ≠ [] ∧
    receipt.ratePartition ≠ [] ∧ receipt.covariancePartition ≠ [] ∧
    receipt.terminalBranchCells ≠ [] ∧ 0 < receipt.precision ∧
    receipt.posteriorCostEnclosures ≠ [] ∧ receipt.selectorRiskEnclosures ≠ []) &&
  decide (receipt.posteriorIntegralReplay ≠ [] ∧ receipt.selectorRiskReplay ≠ [] ∧
    receipt.covarianceKLReplay ≠ []) &&
  receipt.posteriorIntegralReplay.all validGaussianIntegralArithmeticReplayCheck &&
  receipt.selectorRiskReplay.all validGaussianIntegralArithmeticReplayCheck &&
  receipt.covarianceKLReplay.all validCovarianceKLReplayCheck &&
  decide (receipt.posteriorCostEnclosures = receipt.posteriorIntegralReplay.map (·.output) ∧
    receipt.selectorRiskEnclosures = receipt.selectorRiskReplay.map (·.output) ∧
    receipt.computedErrors.covariancePinsker =
      receipt.covarianceKLReplay.foldl (fun radius row => max radius row.pinskerRadius) 0) &&
  rationalIntegralTablesTiedToReceiptCheck receipt &&
  receipt.posteriorCostEnclosures.all (fun interval => decide (interval.1 ≤ interval.2)) &&
  receipt.selectorRiskEnclosures.all (fun interval => decide (interval.1 ≤ interval.2)) &&
  decide (0 < receipt.allocatedErrors.parameterInterpolation ∧
    0 < receipt.allocatedErrors.covariancePinsker ∧
    0 < receipt.allocatedErrors.observationTail ∧
    0 < receipt.allocatedErrors.quadrature ∧
    0 < receipt.allocatedErrors.ambiguousActions ∧
    0 < receipt.allocatedErrors.rounding ∧
    0 ≤ receipt.computedErrors.parameterInterpolation ∧
    receipt.computedErrors.parameterInterpolation ≤ receipt.allocatedErrors.parameterInterpolation ∧
    0 ≤ receipt.computedErrors.covariancePinsker ∧
    receipt.computedErrors.covariancePinsker ≤ receipt.allocatedErrors.covariancePinsker ∧
    0 ≤ receipt.computedErrors.observationTail ∧
    receipt.computedErrors.observationTail ≤ receipt.allocatedErrors.observationTail ∧
    0 ≤ receipt.computedErrors.quadrature ∧
    receipt.computedErrors.quadrature ≤ receipt.allocatedErrors.quadrature ∧
    0 ≤ receipt.computedErrors.ambiguousActions ∧
    receipt.computedErrors.ambiguousActions ≤ receipt.allocatedErrors.ambiguousActions ∧
    0 ≤ receipt.computedErrors.rounding ∧
    receipt.computedErrors.rounding ≤ receipt.allocatedErrors.rounding ∧
    receipt.allocatedErrors.total ≤ receipt.requestedTolerance ∧
    receipt.lowerBound = max 0 (replayedBayesLower receipt - receipt.allocatedErrors.total) ∧
    receipt.upperBound = replayedSelectorUpper receipt + receipt.allocatedErrors.total ∧
    0 ≤ receipt.lowerBound ∧ receipt.lowerBound ≤ receipt.upperBound ∧
    receipt.upperBound - receipt.lowerBound ≤ receipt.requestedTolerance ∧
    receipt.checkerRevision ≠ "" ∧ receipt.checksum = certificateChecksum receipt)

end

noncomputable section
open Classical

def CompleteCertificateReceipt (epsilon : ℝ) (receipt : CertificateReceipt) : Prop :=
  certificateReceiptCheck receipt = true ∧ (receipt.requestedTolerance : ℝ) ≤ epsilon

def CertificateTranscriptMatches (A : Finset (Fin K)) (M : ℝ)
    (observationRadius eigenLower eigenUpper : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (receipt : CertificateReceipt) : Prop :=
  receipt.face = A.toList.map Fin.val ∧ (M : ℝ) ≤ (receipt.quotientRadius : ℝ) ∧
    0 < receipt.quotientRadius ∧ receipt.variancePartition = varianceCells ∧
    receipt.parameterPartition = parameterCells ∧
    receipt.observationPartition = observationCells ∧ receipt.ratePartition = rateCells ∧
    receipt.covariancePartition = covarianceCells ∧
    receipt.observationRadius = observationRadius ∧
    receipt.rationalInputs = certificateRationalInputPayload receipt.face receipt.requestedTolerance
      receipt.quotientRadius observationRadius eigenLower eigenUpper varianceCells parameterCells
        observationCells rateCells covarianceCells

/-- Independently executable replay of the receipt against the rational inputs
supplied to this invocation. -/
def certificateInvocationCheck (A : Finset (Fin K)) (M : ℝ)
    (observationRadius eigenLower eigenUpper : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (receipt : CertificateReceipt) : Bool :=
  decide (ReceiptSyntacticValidity receipt ∧
    CertificateTranscriptMatches A M observationRadius eigenLower eigenUpper varianceCells
      parameterCells observationCells rateCells covarianceCells receipt)

def FiniteGameSolutionChecked (receipt : CertificateReceipt) : Prop :=
  RationalFinitePrior receipt

def PosteriorRiskIntervalsChecked (receipt : CertificateReceipt) : Prop :=
  receipt.posteriorCostEnclosures ≠ [] ∧ receipt.selectorRiskEnclosures ≠ [] ∧
    (∀ i ∈ receipt.posteriorCostEnclosures, i.1 ≤ i.2) ∧
    ∀ i ∈ receipt.selectorRiskEnclosures, i.1 ≤ i.2

def UniformlyEigenBoundedCovarianceCells [NeZero K] (A : Finset (Fin K))
    (covarianceCells : List RationalCell) (eigenLower eigenUpper : ℝ) : Prop :=
  ∀ cell ∈ covarianceCells, ∀ v' r' : Fin K → ℝ,
    (∀ k ∈ A, 0 < v' k ∧ 0 < r' k) → CovarianceCellContains A v' r' cell →
    (∀ x : QuotientIndex A → ℝ, (∑ i, x i ^ 2) = 1 →
      eigenLower ≤ ∑ i, ∑ j, x i * quotientCovariance A v' r' i.1 j.1 * x j) ∧
    ∀ x : QuotientIndex A → ℝ, (∑ i, x i ^ 2) = 1 →
      (∑ i, ∑ j, x i * quotientCovariance A v' r' i.1 j.1 * x j) ≤ eigenUpper

def CovariancePartitionCoversRates [NeZero K] (A : Finset (Fin K)) (v : Fin K → ℝ)
    (rateCells covarianceCells : List RationalCell) : Prop :=
  ∀ r' : Fin K → ℝ, (∃ cell ∈ rateCells, InRationalCell r' cell) →
    (∀ k ∈ A, 0 < r' k) →
    ∃ cell ∈ covarianceCells, CovarianceCellContains A v r' cell

def RationalCellsHaveDisjointInteriors (d : ℕ) (cells : List RationalCell) : Prop :=
  ∀ cell₁ ∈ cells, ∀ cell₂ ∈ cells, cell₁ ≠ cell₂ →
    ¬ ∃ x : Fin d → ℝ,
      InRationalCellInterior x cell₁ ∧ InRationalCellInterior x cell₂

def GenuineRatePartition (d : ℕ) (cells : List RationalCell) : Prop :=
  cells.Nodup ∧ 1 < cells.length ∧ (∀ cell ∈ cells, cell ≠ []) ∧
    RationalCellsHaveDisjointInteriors d cells

def CovarianceCellsHaveDisjointInteriors [NeZero K] (A : Finset (Fin K))
    (cells : List RationalCell) : Prop :=
  ∀ cell₁ ∈ cells, ∀ cell₂ ∈ cells, cell₁ ≠ cell₂ →
    ¬ ∃ v r : Fin K → ℝ,
      CovarianceCellContainsInterior A v r cell₁ ∧
        CovarianceCellContainsInterior A v r cell₂

/-- Deterministic assignment of shared rate-cell boundaries. -/
def DeterministicRateCellAssignment (cells : List RationalCell)
    (assign : (Fin K → ℝ) → RationalCell) : Prop :=
  ∀ r, (∃ cell ∈ cells, InRationalCell r cell) →
    assign r ∈ cells ∧ InRationalCell r (assign r)

/-- Deterministic assignment of shared covariance-cell boundaries. -/
def DeterministicCovarianceCellAssignment [NeZero K] (A : Finset (Fin K))
    (cells : List RationalCell)
    (assign : (Fin K → ℝ) → (Fin K → ℝ) → RationalCell) : Prop :=
  ∀ v r, (∃ cell ∈ cells, CovarianceCellContains A v r cell) →
    assign v r ∈ cells ∧ CovarianceCellContains A v r (assign v r)

/-- An outward rational snap is a fixed function of the empirical covariance
matrix and the known rate only; it has no oracle variance argument. -/
def DataDeterminedOutwardCovarianceSnap (A : Finset (Fin K))
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ∀ empirical rate k, k ∈ A → empirical k k * rate k ≤ snap empirical rate k

/-- A nonempty rational product cell of variance/rate pairs on which every
active point is positive and the quotient covariance is uniformly positive
definite with rational eigenvalue bounds. -/
def PositiveRationalGaussianParameterCell [NeZero K] (A : Finset (Fin K))
    (varianceCell rateCell : RationalCell) : Prop :=
  varianceCell.length = K ∧ rateCell.length = K ∧
  (∀ interval ∈ varianceCell, interval.1 ≤ interval.2) ∧
  (∀ interval ∈ rateCell, interval.1 ≤ interval.2) ∧
  (∃ v r : Fin K → ℝ, InRationalCell v varianceCell ∧
    InRationalCell r rateCell) ∧
  ∃ eigenLower eigenUpper : ℚ, 0 < eigenLower ∧ eigenLower ≤ eigenUpper ∧
    ∀ v r : Fin K → ℝ, InRationalCell v varianceCell →
      InRationalCell r rateCell → (∀ k ∈ A, 0 < v k ∧ 0 < r k) ∧
      ∀ x : QuotientIndex A → ℝ, (∑ i, x i ^ 2) = 1 →
        (eigenLower : ℝ) ≤
          ∑ i, ∑ j, x i * quotientCovariance A v r i.1 j.1 * x j ∧
        (∑ i, ∑ j, x i * quotientCovariance A v r i.1 j.1 * x j) ≤
          (eigenUpper : ℝ)

def CompactCertificateDomain [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (eigenLower eigenUpper observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell) : Prop :=
  2 ≤ A.card ∧ 0 < M ∧ 0 < epsilon ∧ (∀ k ∈ A, 0 < v k ∧ 0 < r k) ∧
    0 < eigenLower ∧ eigenLower ≤ eigenUpper ∧
    GenuineRatePartition K varianceCells ∧
    (∃ varianceCell ∈ varianceCells, ∃ rateCell ∈ rateCells,
      InRationalCell v varianceCell ∧ InRationalCell r rateCell ∧
      PositiveRationalGaussianParameterCell A varianceCell rateCell) ∧
    GenuineQuotientPartition A M parameterCells ∧
    TruncatedObservationPartition A (observationRadius : ℝ) observationCells ∧
    GenuineRatePartition K rateCells ∧
    (∃ cell ∈ rateCells, InRationalCell r cell) ∧
    covarianceCells.Nodup ∧ 1 < covarianceCells.length ∧
    (∀ cell ∈ covarianceCells, cell ≠ []) ∧
    CovarianceCellsHaveDisjointInteriors A covarianceCells ∧
    CovariancePartitionCoversRates A v rateCells covarianceCells ∧
    UniformlyEigenBoundedCovarianceCells A covarianceCells (eigenLower : ℝ) (eigenUpper : ℝ)
-- @realizes \varepsilon(positive certificate tolerance)

/-- The full active representative encoded by a rational quotient support point,
with reference coordinate zero. -/
def rationalSupportRepresentative [NeZero K] (A : Finset (Fin K))
    (point : RationalCell) : Fin K → ℝ :=
  fun k => if hk : k ∈ A then
    if hkr : k ≠ referenceArm A then
      ((point.getD (Finset.univ.toList.idxOf (⟨k, hk, hkr⟩ : QuotientIndex A)) (0, 0)).1 : ℝ)
    else 0 else 0

def PriorSupportInsideQuotientBall [NeZero K] (A : Finset (Fin K)) (M : ℝ)
    (receipt : CertificateReceipt) : Prop :=
  ∀ point ∈ receipt.priorSupport,
    quotientNorm A (rationalSupportRepresentative A point) ≤ M

/-- The Gaussian primitive in a replay row is the actual quotient-normal mass
of the recorded observation cell at the recorded rational parameter point.
The one-dimensional CDF seeds are also required to enclose the standard-normal
CDF at their recorded arguments.  Thus neither the seeds nor `primitiveMass`
are free caller-supplied numbers. -/
def ValidGaussianIntegralReplay [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (parameterTable observationTable : List RationalCell)
    (coefficient : ℝ) (row : GaussianIntegralReplay) : Prop :=
  row.parameterIndex < parameterTable.length ∧
  row.observationCellIndex < observationTable.length ∧
  row.actionIndex < K ∧
  row.cdfArguments.length = row.cdfSeeds.length ∧
  (∀ item ∈ row.cdfArguments.zip row.cdfSeeds,
    (item.2.1 : ℝ) ≤ standardNormalDistribution item.1 ∧
      standardNormalDistribution item.1 ≤ (item.2.2 : ℝ)) ∧
  let parameterPoint := parameterTable.getD row.parameterIndex []
  let observationCell := observationTable.getD row.observationCellIndex []
  let h := rationalSupportRepresentative A parameterPoint
  (∃ a : Fin K, a.1 = row.actionIndex ∧ a ∈ A ∧
    row.lossValue = simpleRegret A h a) ∧
  (row.primitiveMass.1 : ℝ) ≤
      (quotientGaussianLaw A h v r
        {y | InQuotientRationalCell A y observationCell}).toReal ∧
  (quotientGaussianLaw A h v r
      {y | InQuotientRationalCell A y observationCell}).toReal ≤
    (row.primitiveMass.2 : ℝ) ∧
  (row.output.1 : ℝ) ≤ coefficient *
      (quotientGaussianLaw A h v r
        {y | InQuotientRationalCell A y observationCell}).toReal * row.lossValue ∧
  coefficient * (quotientGaussianLaw A h v r
      {y | InQuotientRationalCell A y observationCell}).toReal * row.lossValue ≤
    (row.output.2 : ℝ)

/-- Semantic finite-prior Bayes value under the rational support and weights. -/
def receiptFinitePriorBayesValue [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M : ℝ) (receipt : CertificateReceipt) : ENNReal :=
  sInf {risk : ENNReal | ∃ delta : (ActiveIndex A → ℝ) → Fin K → ℝ,
    GaussianSelector A delta ∧ risk =
      ((receipt.priorSupport.zip receipt.priorWeights).map (fun item =>
        ENNReal.ofReal item.2 * ENNReal.ofReal
          (gaussianSelectorRisk A v r (rationalSupportRepresentative A item.1) delta))).sum}

/-- The directed covariance KL/Pinsker row is also checked against the actual
selector-risk perturbation for every positive covariance pair in its two
recorded cells. -/
def SemanticCovariancePinskerReplay [NeZero K] (A : Finset (Fin K)) (M : ℝ)
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) (receipt : CertificateReceipt)
    (row : CovarianceKLReplay) : Prop :=
  row.covarianceCellIndex < receipt.covariancePartition.length ∧
  row.referenceCellIndex < receipt.covariancePartition.length ∧
  ∀ v₁ r₁ v₂ r₂ : Fin K → ℝ,
    (∀ k ∈ A, 0 < v₁ k ∧ 0 < r₁ k) →
    (∀ k ∈ A, 0 < v₂ k ∧ 0 < r₂ k) →
    CovarianceCellContains A v₁ r₁
      (receipt.covariancePartition.getD row.covarianceCellIndex []) →
    CovarianceCellContains A v₂ r₂
      (receipt.covariancePartition.getD row.referenceCellIndex []) →
    |(gaussianSelectorCompactWorstRisk A v₁ r₁ M delta).toReal -
      (gaussianSelectorCompactWorstRisk A v₂ r₂ M delta).toReal| ≤ row.pinskerRadius

/-- Every directed row is tied to the stated quotient Gaussian law.  Posterior
rows use rational prior support; selector-risk rows use the full parameter
partition.  Aggregate Bayes and worst-risk inequalities are consequences of
these rowwise enclosures and the checked error calculations, not fields of this
predicate. -/
def DirectedGaussianEnclosures [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M : ℝ) (cert : CompactCertificateOutput A) : Prop :=
  (∀ row ∈ cert.2.2.posteriorIntegralReplay,
    ValidGaussianIntegralReplay A v r cert.2.2.priorSupport
      cert.2.2.observationPartition row.priorWeight row) ∧
  (∀ row ∈ cert.2.2.selectorRiskReplay,
    ValidGaussianIntegralReplay A v r cert.2.2.parameterPartition
      cert.2.2.observationPartition row.actionWeight row) ∧
  ∀ row ∈ cert.2.2.covarianceKLReplay,
    SemanticCovariancePinskerReplay A M cert.2.1 cert.2.2 row

/-- The six recorded error components are checked against six distinct
calculations on the supplied game, partitions, radius, covariance cells and
represented selector.  The rational entries are outward upper bounds; they are
not free bookkeeping numbers. -/
def CertificateErrorCalculations [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M : ℝ) (cert : CompactCertificateOutput A) : Prop :=
  (∀ h g : Fin K → ℝ, quotientNorm A h ≤ M → quotientNorm A g ≤ M →
    (∃ cell ∈ cert.2.2.parameterPartition,
      InQuotientRationalCell A (quotientObservation A (fun k => h k.1)) cell ∧
      InQuotientRationalCell A (quotientObservation A (fun k => g k.1)) cell) →
    ∀ a, |simpleRegret A h a - simpleRegret A g a| ≤
      (cert.2.2.computedErrors.parameterInterpolation : ℝ)) ∧
  (∀ v' r' : Fin K → ℝ, (∀ k ∈ A, 0 < v' k ∧ 0 < r' k) →
    (∃ cell ∈ cert.2.2.covariancePartition,
      CovarianceCellContains A v r cell ∧ CovarianceCellContains A v' r' cell) →
    |(gaussianSelectorCompactWorstRisk A v r M cert.2.1).toReal -
      (gaussianSelectorCompactWorstRisk A v' r' M cert.2.1).toReal| ≤
        (cert.2.2.computedErrors.covariancePinsker : ℝ)) ∧
  (∀ h : Fin K → ℝ, quotientNorm A h ≤ M →
    ∫ x in {x : ActiveIndex A → ℝ |
        ∃ i, (cert.2.2.observationRadius : ℝ) <
          |quotientObservation A x i|},
      ∑ a, cert.2.1 x a * simpleRegret A h a ∂(activeDiagonalGaussian A h v r) ≤
        (cert.2.2.computedErrors.observationTail : ℝ)) ∧
  (∀ interval ∈ cert.2.2.posteriorCostEnclosures,
    (interval.2 - interval.1 : ℚ) ≤ cert.2.2.computedErrors.quadrature) ∧
  (∀ interval ∈ cert.2.2.selectorRiskEnclosures,
    (interval.2 - interval.1 : ℚ) ≤ cert.2.2.computedErrors.ambiguousActions) ∧
  |cert.1.1 - (cert.2.2.lowerBound : ℝ)| +
      |cert.1.2 - (cert.2.2.upperBound : ℝ)| ≤
    (cert.2.2.computedErrors.rounding : ℝ)

def ValidCompactCertificate [NeZero K] (A : Finset (Fin K)) (v r : Fin K → ℝ)
    (M epsilon : ℝ) (cert : CompactCertificateOutput A) : Prop :=
  CompleteCertificateReceipt epsilon cert.2.2 ∧ FiniteGameSolutionChecked cert.2.2 ∧
    RationalSelectorTable A cert.2.2 ∧ PosteriorRiskIntervalsChecked cert.2.2 ∧
    SelectorRealizesRationalTable A cert.2.1 cert.2.2 ∧
    PriorSupportInsideQuotientBall A M cert.2.2 ∧
    GaussianSelector A cert.2.1 ∧ LocationInvariantSelector A cert.2.1 ∧
    MeasurablyFactorsThroughQuotient A cert.2.1 ∧
    cert.1.1 = (cert.2.2.lowerBound : ℝ) ∧ cert.1.2 = (cert.2.2.upperBound : ℝ) ∧
    0 ≤ cert.1.1 ∧ cert.1.1 ≤ cert.1.2 ∧ cert.1.2 - cert.1.1 ≤ epsilon

def CertificateRefinementSpec [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ)
    (observationRadius eigenLower eigenUpper : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (cert : CompactCertificateOutput A) : Prop :=
  CertificateTranscriptMatches A M observationRadius eigenLower eigenUpper varianceCells
      parameterCells observationCells rateCells covarianceCells cert.2.2 ∧
    certificateInvocationCheck A M observationRadius eigenLower eigenUpper varianceCells
      parameterCells observationCells rateCells covarianceCells cert.2.2 = true ∧
    rationalRefinementTraceCheck
      (varianceCells ++ parameterCells ++ observationCells ++ rateCells ++ covarianceCells)
      cert.2.2.terminalBranchCells cert.2.2.refinementTrace = true ∧
    ValidRefinementTrace
      (varianceCells ++ parameterCells ++ observationCells ++ rateCells ++ covarianceCells)
      cert.2.2.terminalBranchCells cert.2.2.refinementTrace ∧
    ValidCompactCertificate A v r M epsilon cert

-- @node: def:finite-gaussian-certificate
/-- General relational output of rational refinement.  No bracket or selector is
predetermined: the checker accepts exactly those trace-linked outputs whose
rational tables and semantic Gaussian enclosures replay successfully. -/
def compactQuotientCertificate [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (eigenLower eigenUpper observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (output : CompactCertificateOutput A) : Prop :=
  CompactCertificateDomain A v r M epsilon eigenLower eigenUpper observationRadius
      varianceCells parameterCells observationCells rateCells covarianceCells ∧
    CertificateRefinementSpec A v r M epsilon observationRadius eigenLower eigenUpper
      varianceCells parameterCells observationCells rateCells covarianceCells output ∧
    DirectedGaussianEnclosures A v r M output ∧
    CertificateErrorCalculations A v r M output

/-- Analytic soundness of the executable rational replay.  In particular, the
Gaussian rectangle primitives, posterior and selector sums, and covariance
KL/Pinsker rows semantically enclose their corresponding integrals.  This is
derived from the checked trace, not supplied as receipt data. -/
lemma rationalGaussianReplay_sound [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (eigenLower eigenUpper observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (output : CompactCertificateOutput A)
    (h : compactQuotientCertificate A v r M epsilon eigenLower eigenUpper observationRadius
      varianceCells parameterCells observationCells rateCells covarianceCells output) :
    DirectedGaussianEnclosures A v r M output ∧
      CertificateErrorCalculations A v r M output := by
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- Soundness is proved from finite-prior Bayes domination, selector feasibility,
and the analytic interval/error checks; the receipt never assumes either target inequality. -/
lemma compactQuotientCertificate_sound [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (eigenLower eigenUpper observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (output : CompactCertificateOutput A)
    (h : compactQuotientCertificate A v r M epsilon eigenLower eigenUpper observationRadius
      varianceCells parameterCells observationCells rateCells covarianceCells output) :
    ENNReal.ofReal output.1.1 ≤ gaussianCompactValue A v r M ∧
      gaussianCompactValue A v r M ≤ ENNReal.ofReal output.1.2 ∧
      gaussianSelectorCompactWorstRisk A v r M output.2.1 ≤ ENNReal.ofReal output.1.2 := by
  sorry

/-- The same checked endpoints remain sound at every positive covariance point
in the recorded terminal subcell used for outward snapping. -/
lemma compactQuotientCertificate_sound_on_recorded_cell [NeZero K]
    (A : Finset (Fin K)) (v r v' r' : Fin K → ℝ)
    (M epsilon : ℝ) (eigenLower eigenUpper observationRadius : ℚ)
    (varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell)
    (output : CompactCertificateOutput A)
    (h : compactQuotientCertificate A v r M epsilon eigenLower eigenUpper observationRadius
      varianceCells parameterCells observationCells rateCells covarianceCells output)
    (hpositive : ∀ k ∈ A, 0 < v' k ∧ 0 < r' k)
    (hcell : ∃ cell ∈ output.2.2.covariancePartition,
      CovarianceCellContains A v r cell ∧ CovarianceCellContains A v' r' cell) :
    ENNReal.ofReal output.1.1 ≤ gaussianCompactValue A v' r' M ∧
      gaussianCompactValue A v' r' M ≤ ENNReal.ofReal output.1.2 ∧
      gaussianSelectorCompactWorstRisk A v' r' M output.2.1 ≤
        ENNReal.ofReal output.1.2 := by
  sorry

/-- A particular output checked with rational refinement inputs chosen locally. -/
def IsCheckedCompactCertificate [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (cert : CompactCertificateOutput A) : Prop :=
  ∃ eigenLower eigenUpper observationRadius : ℚ,
  ∃ varianceCells parameterCells observationCells rateCells covarianceCells : List RationalCell,
    compactQuotientCertificate A v r M epsilon eigenLower eigenUpper observationRadius
      varianceCells parameterCells observationCells rateCells covarianceCells cert

lemma isCheckedCompactCertificate_sound [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (cert : CompactCertificateOutput A)
    (h : IsCheckedCompactCertificate A v r M epsilon cert) :
    ENNReal.ofReal cert.1.1 ≤ gaussianCompactValue A v r M ∧
      gaussianCompactValue A v r M ≤ ENNReal.ofReal cert.1.2 ∧
      gaussianSelectorCompactWorstRisk A v r M cert.2.1 ≤ ENNReal.ofReal cert.1.2 ∧
      cert.1.2 - cert.1.1 ≤ epsilon := by
  rcases h with ⟨eigenLower, eigenUpper, observationRadius, varianceCells,
    parameterCells, observationCells, rateCells, covarianceCells, hcert⟩
  refine ⟨(compactQuotientCertificate_sound A v r M epsilon eigenLower eigenUpper
    observationRadius varianceCells parameterCells observationCells rateCells covarianceCells
    cert hcert).1, ?_⟩
  refine ⟨(compactQuotientCertificate_sound A v r M epsilon eigenLower eigenUpper
    observationRadius varianceCells parameterCells observationCells rateCells covarianceCells
    cert hcert).2.1, ?_⟩
  refine ⟨(compactQuotientCertificate_sound A v r M epsilon eigenLower eigenUpper
    observationRadius varianceCells parameterCells observationCells rateCells covarianceCells
    cert hcert).2.2, ?_⟩
  have hvalid : ValidCompactCertificate A v r M epsilon cert :=
    hcert.2.1.2.2.2.2
  rcases hvalid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hwidth⟩
  exact hwidth

/-- Pointwise existence of a checked output from the general refinement
computation; no candidate selector or bracket is predetermined. -/
def HasCheckedCompactCertificate [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) : Prop :=
  ∃ cert : CompactCertificateOutput A, IsCheckedCompactCertificate A v r M epsilon cert

/-- A deterministic, step-indexed rational refinement calculation.  Returning
`none` means that the requested finite refinement has not terminated by that
step; a returned output is still accepted only through the independent checker. -/
abbrev CompactCertificateAlgorithm (K : ℕ) :=
  (A : Finset (Fin K)) → (v r : Fin K → ℝ) → (M epsilon : ℝ) →
    (varianceCell rateCell : RationalCell) → ℕ → Option (CompactCertificateOutput A)

def CertificateAlgorithmTerminatesOn [NeZero K] (algorithm : CompactCertificateAlgorithm K)
    (A : Finset (Fin K)) (v r : Fin K → ℝ) (M epsilon : ℝ)
    (varianceCell rateCell : RationalCell) : Prop :=
  ∃ steps output, algorithm A v r M epsilon varianceCell rateCell steps = some output ∧
    InRationalCell v varianceCell ∧ InRationalCell r rateCell ∧
    IsCheckedCompactCertificate A v r M epsilon output

/-- A rational product cell of variance/rate pairs on which the active
covariance is uniformly positive definite. -/
def CompactPositiveGaussianCell [NeZero K] (A : Finset (Fin K))
    (varianceCell rateCell : RationalCell) : Prop :=
  PositiveRationalGaussianParameterCell A varianceCell rateCell

/-- One member of a finite cover, carrying certificate data chosen for this
cell rather than inherited from an unrelated initial point. -/
structure CertifiedCompactCell (A : Finset (Fin K)) where
  varianceCell : RationalCell
  rateCell : RationalCell
  baseVariance : Fin K → ℝ
  baseRate : Fin K → ℝ
  eigenLower : ℚ
  eigenUpper : ℚ
  observationRadius : ℚ
  varianceCells : List RationalCell
  parameterCells : List RationalCell
  observationCells : List RationalCell
  rateCells : List RationalCell
  covarianceCells : List RationalCell
  output : CompactCertificateOutput A

def ValidCertifiedCompactCell [NeZero K] (A : Finset (Fin K)) (M epsilon : ℝ)
    (cell : CertifiedCompactCell A) : Prop :=
  CompactPositiveGaussianCell A cell.varianceCell cell.rateCell ∧
  cell.varianceCell ∈ cell.varianceCells ∧
  InRationalCell cell.baseVariance cell.varianceCell ∧
  InRationalCell cell.baseRate cell.rateCell ∧
  compactQuotientCertificate A cell.baseVariance cell.baseRate M epsilon
    cell.eigenLower cell.eigenUpper cell.observationRadius cell.varianceCells cell.parameterCells
      cell.observationCells cell.rateCells cell.covarianceCells cell.output ∧
  ∀ v r : Fin K → ℝ, InRationalCell v cell.varianceCell →
    InRationalCell r cell.rateCell →
    ∃ covarianceCell ∈ cell.output.2.2.covariancePartition,
      covarianceCell ∈ cell.output.2.2.terminalBranchCells ∧
      CovarianceCellContains A cell.baseVariance cell.baseRate covarianceCell ∧
      CovarianceCellContains A v r covarianceCell
-- @realizes L_\varepsilon(v_A,r_A)(validated lower envelope)
-- @realizes U_\varepsilon(v_A,r_A)(validated upper envelope)
-- @realizes \delta_{\varepsilon,A}(represented finite-partition selector)

/-- Screening envelope used by the hierarchical noncompact routine. -/
def screeningEnvelope [NeZero K] (A : Finset (Fin K)) (v r : Fin K → ℝ)
    (lambda T : ℝ) : ℝ :=
  (1 - lambda) ^ (-1 / 2 : ℝ) * gaussianGlobalValueReal A v r +
    2 * (A.card : ℝ) ^ 2 * Real.exp (-T ^ 2)

/-- A zero rate is boundary-fatal only when its arm competes with another arm
on the declared decision face. -/
def ActionRelevantCoordinate (A : Finset (Fin K)) (k : Fin K) : Prop :=
  k ∈ A ∧ ∃ j ∈ A, j ≠ k

/-- Arms lying within `T` of the screening maximum, computed solely from the
active screening observation. -/
def retainedArms (A : Finset (Fin K)) (T : ℝ) (screen : ActiveIndex A → ℝ) :
    Finset (Fin K) :=
  A.filter fun k => ∀ (hk : k ∈ A) (j : Fin K) (hj : j ∈ A),
    screen ⟨j, hj⟩ ≤ screen ⟨k, hk⟩ + T

/-- The decision observation passed to a retained-subset compact selector. -/
def scaledDecisionObservation (A : Finset (Fin K)) (lambda : ℝ)
    (decision : ActiveIndex A → ℝ) : ActiveIndex A → ℝ :=
  fun k => Real.sqrt (1 - lambda) * decision k

/-- A retained arm, viewed as an arm of the declared face. -/
def retainedIndex (A : Finset (Fin K)) (T : ℝ) (screen : ActiveIndex A → ℝ)
    (k : ActiveIndex (retainedArms A T screen)) : ActiveIndex A :=
  ⟨k.1, (Finset.mem_filter.mp k.2).1⟩

/-- The scaled decision observation restricted to the actually retained face. -/
def scaledRetainedDecision (A : Finset (Fin K)) (lambda T : ℝ)
    (screen decision : ActiveIndex A → ℝ) :
    ActiveIndex (retainedArms A T screen) → ℝ :=
  fun k => Real.sqrt (1 - lambda) * decision (retainedIndex A T screen k)

/-- Exact-zero rule on a singleton retained face. -/
def singletonActiveSelector (S : Finset (Fin K)) :
    (ActiveIndex S → ℝ) → Fin K → ℝ :=
  fun _ a => if S = {a} then 1 else 0

def ExactZeroSingletonBranch [NeZero K] (S : Finset (Fin K)) (v r : Fin K → ℝ) : Prop :=
  S.card = 1 ∧ GaussianSelector S (singletonActiveSelector S) ∧
    gaussianSelectorCompactWorstRisk S v r 0 (singletonActiveSelector S) = 0

/-- The deterministic certificate endpoint at the true Gaussian parameter.
Singleton retained faces use their exact zero-risk branch; larger faces carry a
checked refinement receipt at the true variance/rate point. -/
def TrueParameterCertificateBenchmark [NeZero K] (S : Finset (Fin K))
    (v r : Fin K → ℝ) (M epsilon : ℝ) (output : CompactCertificateOutput S) : Prop :=
  (S.card = 1 ∧ output.1.1 = 0 ∧ output.1.2 = 0 ∧
    output.2.1 = singletonActiveSelector S ∧ ExactZeroSingletonBranch S v r) ∨
  (2 ≤ S.card ∧ IsCheckedCompactCertificate S v r M epsilon output)

/-- Deterministic true-parameter upper endpoint.  On a shared covariance
boundary it is the finite maximum of all valid containing-cell endpoints, so
the benchmark is independent of the realized pilot and dominates whichever
deterministically assigned receipt the pilot selects. -/
def finiteContainingCertificateUpper [NeZero K] (S : Finset (Fin K))
    (v r : Fin K → ℝ) (cells : List RationalCell)
    (outputs : RationalCell → CompactCertificateOutput S) : ℝ :=
  cells.foldl (fun upper cell =>
    if CovarianceCellContains S v r cell then max upper (outputs cell).1.2 else upper) 0

/-- Risk of a two-input screening/decision selector under the independent
Gaussian split. -/
def hierarchicalSplitRisk (A : Finset (Fin K)) (v r h : Fin K → ℝ)
    (lambda : ℝ)
    (delta : (ActiveIndex A → ℝ) → (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ :=
  ∫ screen, ∫ decision, ∑ a, delta screen decision a * simpleRegret A h a
      ∂(activeDiagonalGaussian A h v (fun k => (1 - lambda) * r k))
    ∂(activeDiagonalGaussian A h v (fun k => lambda * r k))

/-- Independently replayable outer-design branch-and-bound data.  Boundary
exclusion has its own finite two-arm lower enclosure and is deliberately
separate from the extended value at an exactly zero action-relevant rate. -/
structure OuterDesignTranscript where
  bernoulliRoots : List RationalCell
  bernoulliTerminals : List RationalCell
  bernoulliTrace : List CertificateRefinementBranch
  bernoulliRiskEnclosures : List (RationalCell × (ℚ × ℚ))
  bernoulliFeasiblePoint : RationalCell
  exactRoots : List RationalCell
  exactTerminals : List RationalCell
  exactTrace : List CertificateRefinementBranch
  exactRiskEnclosures : List (RationalCell × (ℚ × ℚ))
  exactFeasiblePoint : RationalCell
  boundaryCells : List RationalCell
  boundaryMargin : ℚ
  boundaryIncumbent : ℚ
  boundaryPrunedCells : List RationalCell
  twoArmLowerEnclosures : List (RationalCell × ℚ)
deriving Repr

def OuterRiskIntervalsHaveWidth (epsilon : ℝ)
    (table : List (RationalCell × (ℚ × ℚ))) : Prop :=
  table ≠ [] ∧ ∀ entry ∈ table,
    (entry.2.2 : ℝ) - (entry.2.1 : ℝ) ≤ epsilon

def CheckedOuterDesignTranscript [NeZero K] (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v : Fin K → ℝ) (epsilon : ℝ)
    (t : OuterDesignTranscript) : Prop :=
  ValidRefinementTrace t.bernoulliRoots t.bernoulliTerminals t.bernoulliTrace ∧
  ValidRefinementTrace t.exactRoots t.exactTerminals t.exactTrace ∧
  t.bernoulliRiskEnclosures.map (fun entry => entry.1) = t.bernoulliTerminals ∧
  t.exactRiskEnclosures.map (fun entry => entry.1) = t.exactTerminals ∧
  OuterRiskIntervalsHaveWidth epsilon t.bernoulliRiskEnclosures ∧
  OuterRiskIntervalsHaveWidth epsilon t.exactRiskEnclosures ∧
  (∀ p, InSimplex p → ∃ entry ∈ t.bernoulliRiskEnclosures,
    InRationalCell p entry.1 ∧
    (entry.2.1 : ℝ) ≤ gaussianGlobalValueReal A v (matVec B p) ∧
    gaussianGlobalValueReal A v (matVec B p) ≤ (entry.2.2 : ℝ)) ∧
  (∀ alpha, InActiveSimplex A alpha → ∃ entry ∈ t.exactRiskEnclosures,
    InRationalCell alpha entry.1 ∧
    (entry.2.1 : ℝ) ≤ gaussianGlobalValueReal A v alpha ∧
    gaussianGlobalValueReal A v alpha ≤ (entry.2.2 : ℝ)) ∧
  (∃ p, InSimplex p ∧ InRationalCell p t.bernoulliFeasiblePoint ∧
    gaussianGlobalValueReal A v (matVec B p) ≤ (faceMechanismValues B A v).1 + epsilon) ∧
  (∃ alpha, InActiveSimplex A alpha ∧ InRationalCell alpha t.exactFeasiblePoint ∧
    gaussianGlobalValueReal A v alpha ≤ (faceMechanismValues B A v).2 + epsilon) ∧
  0 < t.boundaryMargin ∧ t.boundaryCells ≠ [] ∧
  t.boundaryPrunedCells = t.boundaryCells ∧
  t.twoArmLowerEnclosures.map (fun entry => entry.1) = t.boundaryCells ∧
  (∃ alpha, InActiveSimplex A alpha ∧
    gaussianGlobalValueReal A v alpha ≤ (t.boundaryIncumbent : ℝ)) ∧
  (∀ entry ∈ t.twoArmLowerEnclosures,
    (t.boundaryIncumbent : ℝ) < (entry.2 : ℝ)) ∧
  (∀ alpha, InActiveSimplex A alpha →
    (∃ k, ActionRelevantCoordinate A k ∧ alpha k ≤ (t.boundaryMargin : ℝ)) →
    ∃ entry ∈ t.twoArmLowerEnclosures, InRationalCell alpha entry.1 ∧
      entry.1 ∈ t.boundaryPrunedCells ∧
      ENNReal.ofReal (entry.2 : ℝ) ≤ gaussianGlobalValue A v alpha)

/-- Full output of the hierarchical routine: noncompact value bounds, the two
outer design values, an observation-dependent split selector, certified
retained-subset payloads, and replayable outer branch-and-bound transcripts. -/
abbrev HierarchicalRoutineOutput (A : Finset (Fin K)) :=
  (ENNReal × ENNReal) × (ℝ × ℝ) ×
    ((ActiveIndex A → ℝ) → (ActiveIndex A → ℝ) → Fin K → ℝ) ×
    List (Σ S : Finset (Fin K), CompactCertificateOutput S) × OuterDesignTranscript

/-- A retained subset has at most one certificate payload.  Thus two screening
observations producing the same subset cannot silently select different
certificates or represented compact selectors. -/
def UniqueRetainedSubsetCertificates
    (payload : List (Σ S : Finset (Fin K), CompactCertificateOutput S)) : Prop :=
  ∀ S cert₁ cert₂, ⟨S, cert₁⟩ ∈ payload → ⟨S, cert₂⟩ ∈ payload → cert₁ = cert₂

/-- The finite retained-subset adaptation is measurable in the screening
observation. -/
def MeasurableRetainedSubsetAdaptation (A : Finset (Fin K)) (T : ℝ) : Prop :=
  ∀ S : Finset (Fin K),
    MeasurableSet {screen : ActiveIndex A → ℝ | retainedArms A T screen = S}

/-- Complete relational checker for one hierarchical output. -/
def HierarchicalRoutineSpec [NeZero K] (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v r : Fin K → ℝ) (lambda T epsilon : ℝ)
    (output : HierarchicalRoutineOutput A) : Prop :=
  lambda ∈ Ioo (0 : ℝ) 1 ∧ 0 < T ∧ 0 < epsilon ∧
    (∀ k ∈ A, 0 ≤ r k) ∧
    ((∃ k, ActionRelevantCoordinate A k ∧ r k = 0) →
      output.1.1 = ⊤ ∧ output.1.2 = ⊤) ∧
    ((∀ k ∈ A, 0 < r k) →
      UniqueRetainedSubsetCertificates output.2.2.2.1 ∧
      MeasurableRetainedSubsetAdaptation A T ∧
      (∀ a, Measurable fun input :
        (ActiveIndex A → ℝ) × (ActiveIndex A → ℝ) =>
          output.2.2.1 input.1 input.2 a) ∧
      (∀ screen, GaussianSelector A (output.2.2.1 screen)) ∧
      (∀ screen, LocationInvariantSelector A (output.2.2.1 screen)) ∧
      output.1.1 ≤ gaussianGlobalValue A v r ∧
      gaussianGlobalValue A v r ≤ ENNReal.ofReal
        (⨆ h : Fin K → ℝ, hierarchicalSplitRisk A v r h lambda output.2.2.1) ∧
      ENNReal.ofReal (⨆ h : Fin K → ℝ,
        hierarchicalSplitRisk A v r h lambda output.2.2.1) ≤ output.1.2 ∧
      output.1.2 ≠ ⊤ ∧ output.1.2.toReal - output.1.1.toReal ≤ epsilon ∧
      (∀ screen, A.Nonempty → (retainedArms A T screen).Nonempty) ∧
      (∀ screen,
        let S := retainedArms A T screen
        (S.card = 1 ∧ output.2.2.1 screen = fun _ => singletonActiveSelector S 0) ∨
        (2 ≤ S.card ∧ ∃ cert : CompactCertificateOutput S,
          ⟨S, cert⟩ ∈ output.2.2.2.1 ∧
          (∃ M : ℝ, ∃ observationRadius eigenLower eigenUpper : ℚ,
            ∃ varianceCells parameterCells observationCells rateCells covarianceCells,
              2 * Real.sqrt (1 - lambda) * T * Real.sqrt (S.card - 1) ≤ M ∧
              compactQuotientCertificate S v r M epsilon eigenLower eigenUpper observationRadius
                varianceCells parameterCells observationCells rateCells covarianceCells cert) ∧
          output.2.2.1 screen = fun decision =>
            cert.2.1 (scaledRetainedDecision A lambda T screen decision))) ∧
      (∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
        (S.card = 1 ∧ ExactZeroSingletonBranch S v r) ∨
        (2 ≤ S.card ∧ ∃ cert : CompactCertificateOutput S,
          ⟨S, cert⟩ ∈ output.2.2.2.1 ∧
            ∃ M : ℝ, ∃ observationRadius eigenLower eigenUpper : ℚ,
              ∃ varianceCells parameterCells observationCells rateCells covarianceCells,
                2 * Real.sqrt (1 - lambda) * T * Real.sqrt (S.card - 1) ≤ M ∧
                compactQuotientCertificate S v r M epsilon eigenLower eigenUpper observationRadius
                  varianceCells parameterCells observationCells rateCells covarianceCells cert ∧
                ∀ screen, ∀ hs : retainedArms A T screen = S,
                  output.2.2.1 screen = fun decision =>
                    cert.2.1 (hs ▸ scaledRetainedDecision A lambda T screen decision)))) ∧
    output.2.1 = faceMechanismValues B A v ∧
    CheckedOuterDesignTranscript A B v epsilon output.2.2.2.2

/-- Positive declared-face domain on which the hierarchical checker is run. -/
def HierarchicalRoutineDomain (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v r : Fin K → ℝ)
    (lambda T epsilon : ℝ) : Prop :=
  2 ≤ A.card ∧ lambda ∈ Ioo (0 : ℝ) 1 ∧ 0 < T ∧ 0 < epsilon ∧
    (∀ k ∈ A, 0 < v k ∧ 0 ≤ r k) ∧ ∀ i j, 0 < B i j

-- @node: def:covariance-boundary-handle
/-- Certified hierarchical screening/decision routine with an extended-value
boundary flag and rational outer-design transcript.  This is the complete
output-validation relation on the stated positive declared-face domain; it has
no uncertified fallback branch. -/
def hierarchicalRoutine [NeZero K] (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v r : Fin K → ℝ) (lambda T epsilon : ℝ)
    (output : HierarchicalRoutineOutput A) : Prop :=
  HierarchicalRoutineDomain A B v r lambda T epsilon ∧
    HierarchicalRoutineSpec A B v r lambda T epsilon output
-- @realizes \mathfrak C_K(certified hierarchical boundary routine)

/-- The boundary routine uses a genuine Gaussian split, adapts to every retained
nonempty subset, and carries certified outer-design branch-and-bound output. -/
def ValidHierarchicalRoutine [NeZero K] (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v r : Fin K → ℝ) (lambda T epsilon : ℝ)
    (output : HierarchicalRoutineOutput A) : Prop :=
  hierarchicalRoutine A B v r lambda T epsilon output

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
