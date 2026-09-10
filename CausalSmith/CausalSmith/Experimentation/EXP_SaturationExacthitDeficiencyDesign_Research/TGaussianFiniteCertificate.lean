import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Certificate
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.GaussianGame
import Causalean.Stat.Minimax.FiniteKernelBayes
import Causalean.Stat.Minimax.Pinsker
import Causalean.Mathlib.Optimization.RationalLP

/-! # Finite validated Gaussian certificate -/

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

section

private instance : Encodable Char where
  encode := Char.toNat
  decode := fun n => some (Char.ofNat n)
  encodek := by intro c; simp [Char.ofNat_toNat]

private instance : Encodable String := Encodable.ofEquiv (List Char) {
  toFun := String.toList
  invFun := String.ofList
  left_inv := by intro s; exact String.ofList_toList
  right_inv := by intro l; exact String.toList_ofList
}

private instance : Encodable CertificateRefinementBranch :=
  Encodable.ofEquiv
    (RationalCell × List RationalCell × List RationalCell × List RationalCell × ℕ) {
      toFun := fun x => (x.parent, x.children, x.ancestry, x.terminalChildren, x.precision)
      invFun := fun (parent, children, ancestry, terminalChildren, precision) => {
        parent := parent
        children := children
        ancestry := ancestry
        terminalChildren := terminalChildren
        precision := precision }
      left_inv := by intro x; cases x; rfl
      right_inv := by rintro ⟨parent, children, ancestry, terminalChildren, precision⟩; rfl
    }

private instance : Encodable CertificateErrorBudget :=
  Encodable.ofEquiv (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) {
    toFun := fun x => (x.parameterInterpolation, x.covariancePinsker,
      x.observationTail, x.quadrature, x.ambiguousActions, x.rounding)
    invFun := fun (a, b, c, d, e, f) => {
      parameterInterpolation := a
      covariancePinsker := b
      observationTail := c
      quadrature := d
      ambiguousActions := e
      rounding := f }
    left_inv := by intro x; cases x; rfl
    right_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl
  }

private instance : Encodable DirectedIntervalStep :=
  Encodable.ofEquiv (Fin 4 × ℕ × ℕ × (ℚ × ℚ)) {
    toFun := fun x => (x.operation, x.leftIndex, x.rightIndex, x.result)
    invFun := fun (operation, leftIndex, rightIndex, result) => {
      operation := operation
      leftIndex := leftIndex
      rightIndex := rightIndex
      result := result }
    left_inv := by intro x; cases x; rfl
    right_inv := by rintro ⟨operation, leftIndex, rightIndex, result⟩; rfl
  }

private instance : Encodable GaussianIntegralReplay :=
  Encodable.ofEquiv
    (ℕ × ℕ × ℕ × ℚ × ℚ × ℚ × List ℚ × List (ℚ × ℚ) × (ℚ × ℚ) ×
      List DirectedIntervalStep × List (ℚ × ℚ) × List DirectedIntervalStep × (ℚ × ℚ)) {
      toFun := fun x => (x.parameterIndex, x.observationCellIndex, x.actionIndex,
        x.priorWeight, x.actionWeight, x.lossValue, x.cdfArguments, x.cdfSeeds,
        x.primitiveMass, x.primitiveCdfTrace, x.arithmeticSeeds, x.arithmeticTrace, x.output)
      invFun := fun (parameterIndex, observationCellIndex, actionIndex, priorWeight,
          actionWeight, lossValue, cdfArguments, cdfSeeds, primitiveMass,
          primitiveCdfTrace, arithmeticSeeds, arithmeticTrace, output) => {
        parameterIndex := parameterIndex
        observationCellIndex := observationCellIndex
        actionIndex := actionIndex
        priorWeight := priorWeight
        actionWeight := actionWeight
        lossValue := lossValue
        cdfArguments := cdfArguments
        cdfSeeds := cdfSeeds
        primitiveMass := primitiveMass
        primitiveCdfTrace := primitiveCdfTrace
        arithmeticSeeds := arithmeticSeeds
        arithmeticTrace := arithmeticTrace
        output := output }
      left_inv := by intro x; cases x; rfl
      right_inv := by
        rintro ⟨parameterIndex, observationCellIndex, actionIndex, priorWeight,
          actionWeight, lossValue, cdfArguments, cdfSeeds, primitiveMass,
          primitiveCdfTrace, arithmeticSeeds, arithmeticTrace, output⟩
        rfl
    }

private instance : Encodable CovarianceKLReplay :=
  Encodable.ofEquiv
    (ℕ × ℕ × List (ℚ × ℚ) × List DirectedIntervalStep ×
      List DirectedIntervalStep × (ℚ × ℚ) × ℚ) {
      toFun := fun x => (x.covarianceCellIndex, x.referenceCellIndex, x.rationalSeeds,
        x.logDetTrace, x.quadraticTrace, x.klInterval, x.pinskerRadius)
      invFun := fun (covarianceCellIndex, referenceCellIndex, rationalSeeds,
          logDetTrace, quadraticTrace, klInterval, pinskerRadius) => {
        covarianceCellIndex := covarianceCellIndex
        referenceCellIndex := referenceCellIndex
        rationalSeeds := rationalSeeds
        logDetTrace := logDetTrace
        quadraticTrace := quadraticTrace
        klInterval := klInterval
        pinskerRadius := pinskerRadius }
      left_inv := by intro x; cases x; rfl
      right_inv := by
        rintro ⟨covarianceCellIndex, referenceCellIndex, rationalSeeds,
          logDetTrace, quadraticTrace, klInterval, pinskerRadius⟩
        rfl
    }

private instance : Encodable CertificateReceipt :=
  Encodable.ofEquiv
    (List ℕ × ℚ × List RationalCell × List ℚ × ℚ × List RationalCell × ℚ ×
      List RationalCell × List RationalCell × List RationalCell ×
      List CertificateRefinementBranch × List RationalCell × List RationalCell × List ℚ ×
      List (RationalCell × List (ℕ × ℚ)) × List (List Bool × List (ℕ × ℚ)) × ℕ ×
      List GaussianIntegralReplay × List GaussianIntegralReplay × List CovarianceKLReplay ×
      List (ℚ × ℚ) × List (ℚ × ℚ) × CertificateErrorBudget × CertificateErrorBudget ×
      ℚ × ℚ × String × String) {
      toFun := fun x => (x.face, x.quotientRadius, x.variancePartition, x.rationalInputs,
        x.requestedTolerance, x.parameterPartition, x.observationRadius,
        x.observationPartition, x.ratePartition, x.covariancePartition, x.refinementTrace,
        x.terminalBranchCells, x.priorSupport, x.priorWeights, x.selectorTable,
        x.tailSelectorTable, x.precision, x.posteriorIntegralReplay, x.selectorRiskReplay,
        x.covarianceKLReplay, x.posteriorCostEnclosures, x.selectorRiskEnclosures,
        x.computedErrors, x.allocatedErrors, x.lowerBound, x.upperBound,
        x.checkerRevision, x.checksum)
      invFun := fun (face, quotientRadius, variancePartition, rationalInputs,
          requestedTolerance, parameterPartition, observationRadius, observationPartition,
          ratePartition, covariancePartition, refinementTrace, terminalBranchCells,
          priorSupport, priorWeights, selectorTable, tailSelectorTable, precision,
          posteriorIntegralReplay, selectorRiskReplay, covarianceKLReplay,
          posteriorCostEnclosures, selectorRiskEnclosures, computedErrors, allocatedErrors,
          lowerBound, upperBound, checkerRevision, checksum) => {
        face := face
        quotientRadius := quotientRadius
        variancePartition := variancePartition
        rationalInputs := rationalInputs
        requestedTolerance := requestedTolerance
        parameterPartition := parameterPartition
        observationRadius := observationRadius
        observationPartition := observationPartition
        ratePartition := ratePartition
        covariancePartition := covariancePartition
        refinementTrace := refinementTrace
        terminalBranchCells := terminalBranchCells
        priorSupport := priorSupport
        priorWeights := priorWeights
        selectorTable := selectorTable
        tailSelectorTable := tailSelectorTable
        precision := precision
        posteriorIntegralReplay := posteriorIntegralReplay
        selectorRiskReplay := selectorRiskReplay
        covarianceKLReplay := covarianceKLReplay
        posteriorCostEnclosures := posteriorCostEnclosures
        selectorRiskEnclosures := selectorRiskEnclosures
        computedErrors := computedErrors
        allocatedErrors := allocatedErrors
        lowerBound := lowerBound
        upperBound := upperBound
        checkerRevision := checkerRevision
        checksum := checksum }
      left_inv := by intro x; cases x; rfl
      right_inv := by
        rintro ⟨face, quotientRadius, variancePartition, rationalInputs,
          requestedTolerance, parameterPartition, observationRadius, observationPartition,
          ratePartition, covariancePartition, refinementTrace, terminalBranchCells,
          priorSupport, priorWeights, selectorTable, tailSelectorTable, precision,
          posteriorIntegralReplay, selectorRiskReplay, covarianceKLReplay,
          posteriorCostEnclosures, selectorRiskEnclosures, computedErrors, allocatedErrors,
          lowerBound, upperBound, checkerRevision, checksum⟩
        rfl
    }

/-- Three-policy treated counts `(1,2,4)` for the six-unit exact example. -/
def sixUnitCounts : Fin 3 → ℕ := fun k => Fin.cases 1 (Fin.cases 2 (fun _ => 4)) k

/-- Finite instruction set of the fixed rational refinement calculation. -/
inductive GaussianRefinementOpcode where
  | splitParameterCell | splitObservationCell | splitCovarianceCell
  | solveFinitePriorLP | solveFiniteSelectorLP | replayDirectedIntegrals
  | allocateErrors | emitCheckedCover
deriving Repr, DecidableEq

def gaussianRefinementCode : List GaussianRefinementOpcode :=
  [.splitParameterCell, .splitObservationCell, .splitCovarianceCell,
   .solveFinitePriorLP, .solveFiniteSelectorLP, .replayDirectedIntegrals,
   .allocateErrors, .emitCheckedCover]

/-- Finite code and reproducibility metadata, with no real-function field. -/
structure GaussianFiniteRefinementProgram where
  code : List GaussianRefinementOpcode
  checkerRevision : String
  checksum : String
deriving Repr, DecidableEq

def gaussianFiniteProgramChecksum (program : GaussianFiniteRefinementProgram) : String :=
  reprStr (program.code, program.checkerRevision)

/-- The one concrete program used on every rational root cell. -/
def gaussianFiniteRefinementProgram : GaussianFiniteRefinementProgram where
  code := gaussianRefinementCode
  checkerRevision := "finite-gaussian-refinement-v1"
  checksum := reprStr (gaussianRefinementCode, "finite-gaussian-refinement-v1")

def ValidGaussianFiniteRefinementProgram
    (program : GaussianFiniteRefinementProgram) : Prop :=
  program.code = gaussianRefinementCode ∧ program.checkerRevision ≠ "" ∧
    program.checksum = gaussianFiniteProgramChecksum program

/-- One run has only encoded face data, rational cells and tolerance, and a
finite stage index. -/
structure GaussianFiniteProgramInput (K : ℕ) where
  encodedFace : List ℕ
  quotientRadius : ℚ
  tolerance : ℚ
  varianceRoot : RationalCell
  rateRoot : RationalCell
deriving Repr, DecidableEq

/-- A successful finite output: terminal product cells, complete receipts, and
the finite refinement trace that produced them. -/
structure GaussianFiniteProgramOutput where
  terminalProductCells : List (RationalCell × RationalCell)
  receipts : List CertificateReceipt
  refinementTrace : List CertificateRefinementBranch
  workingPrecision : ℕ
  checksum : String
deriving Repr

private instance : Encodable GaussianFiniteProgramOutput :=
  Encodable.ofEquiv
    (List (RationalCell × RationalCell) × List CertificateReceipt ×
      List CertificateRefinementBranch × ℕ × String) {
      toFun := fun x => (x.terminalProductCells, x.receipts, x.refinementTrace,
        x.workingPrecision, x.checksum)
      invFun := fun (terminalProductCells, receipts, refinementTrace, workingPrecision,
          checksum) => {
        terminalProductCells := terminalProductCells
        receipts := receipts
        refinementTrace := refinementTrace
        workingPrecision := workingPrecision
        checksum := checksum }
      left_inv := by intro x; cases x; rfl
      right_inv := by
        rintro ⟨terminalProductCells, receipts, refinementTrace, workingPrecision, checksum⟩
        rfl
    }

def gaussianFiniteOutputChecksum (output : GaussianFiniteProgramOutput) : String :=
  reprStr (output.terminalProductCells, output.receipts, output.refinementTrace,
    output.workingPrecision)

/-- Rational-only replay predicate for a successful run. -/
def GaussianFiniteProgramRun (program : GaussianFiniteRefinementProgram)
    (input : GaussianFiniteProgramInput K) (output : GaussianFiniteProgramOutput) : Prop :=
  ValidGaussianFiniteRefinementProgram program ∧
    input.encodedFace ≠ [] ∧ 0 < input.quotientRadius ∧ 0 < input.tolerance ∧
    input.varianceRoot ≠ [] ∧ input.rateRoot ≠ [] ∧
    output.terminalProductCells ≠ [] ∧ output.receipts ≠ [] ∧
    output.terminalProductCells.length = output.receipts.length ∧
    output.refinementTrace ≠ [] ∧ 0 < output.workingPrecision ∧
    (∀ receipt ∈ output.receipts,
      certificateReceiptCheck receipt = true ∧
      receipt.face = input.encodedFace ∧
      receipt.quotientRadius = input.quotientRadius ∧
      receipt.requestedTolerance ≤ input.tolerance ∧
      receipt.upperBound - receipt.lowerBound ≤ input.tolerance ∧
      receipt.checksum = certificateChecksum receipt) ∧
    output.checksum = gaussianFiniteOutputChecksum output

/-- The rational replay is decidable independently of analytic Gaussian facts. -/
def gaussianFiniteProgramRunCheck (program : GaussianFiniteRefinementProgram)
    (input : GaussianFiniteProgramInput K) (output : GaussianFiniteProgramOutput) : Bool :=
  decide (program.code = gaussianRefinementCode ∧ program.checkerRevision ≠ "" ∧
    program.checksum = gaussianFiniteProgramChecksum program) &&
  decide (input.encodedFace ≠ [] ∧ 0 < input.quotientRadius ∧ 0 < input.tolerance ∧
    input.varianceRoot ≠ [] ∧ input.rateRoot ≠ []) &&
  decide (output.terminalProductCells ≠ [] ∧ output.receipts ≠ [] ∧
    output.terminalProductCells.length = output.receipts.length ∧
    output.refinementTrace ≠ [] ∧ 0 < output.workingPrecision) &&
  output.receipts.all (fun receipt =>
    certificateReceiptCheck receipt && decide (receipt.face = input.encodedFace) &&
    decide (receipt.quotientRadius = input.quotientRadius) &&
    decide (receipt.requestedTolerance ≤ input.tolerance) &&
    decide (receipt.upperBound - receipt.lowerBound ≤ input.tolerance) &&
    decide (receipt.checksum = certificateChecksum receipt)) &&
  rationalRefinementTraceCheck [input.varianceRoot, input.rateRoot]
    (output.terminalProductCells.flatMap fun cell => [cell.1, cell.2]) output.refinementTrace &&
  decide (output.checksum = gaussianFiniteOutputChecksum output)

/-- Decode the transcript with the given Gödel index and replay it deterministically.  This is
the executable instruction-step semantics: a step can emit only the decoded
finite rational transcript accepted by the fixed checker. -/
def gaussianFiniteProgramStep (program : GaussianFiniteRefinementProgram)
    (input : GaussianFiniteProgramInput K) (candidateIndex : ℕ) :
    Option GaussianFiniteProgramOutput :=
  match Encodable.decode candidateIndex with
  | none => none
  | some output =>
      if gaussianFiniteProgramRunCheck program input output then some output else none

/-- Execute the deterministic dovetailing refinement search through a finite
stage, retaining the first checked transcript. -/
def gaussianFiniteProgramEvaluate (program : GaussianFiniteRefinementProgram)
    (input : GaussianFiniteProgramInput K) : ℕ → Option GaussianFiniteProgramOutput
  | 0 => gaussianFiniteProgramStep program input 0
  | stage + 1 =>
      match gaussianFiniteProgramEvaluate program input stage with
      | some output => some output
      | none => gaussianFiniteProgramStep program input (stage + 1)

/-- Operational reachability for the fixed evaluator, not mere receipt
acceptance.  The stage is the actual finite execution bound. -/
def GaussianFiniteExecutionReaches (program : GaussianFiniteRefinementProgram)
    (input : GaussianFiniteProgramInput K) (stage : ℕ)
    (output : GaussianFiniteProgramOutput) : Prop :=
  gaussianFiniteProgramEvaluate program input stage = some output

/-- Every emitted evaluator result has passed the independent replay checker. -/
lemma gaussianFiniteProgramEvaluate_checked (program : GaussianFiniteRefinementProgram)
    (input : GaussianFiniteProgramInput K) (stage : ℕ)
    (output : GaussianFiniteProgramOutput)
    (hexec : GaussianFiniteExecutionReaches program input stage output) :
    gaussianFiniteProgramRunCheck program input output = true := by
  have step_checked : ∀ index output,
      gaussianFiniteProgramStep program input index = some output →
        gaussianFiniteProgramRunCheck program input output = true := by
    intro index candidate hstep
    cases hdecode : (Encodable.decode index : Option GaussianFiniteProgramOutput) with
    | none => simp [gaussianFiniteProgramStep, hdecode] at hstep
    | some decoded =>
        by_cases hcheck : gaussianFiniteProgramRunCheck program input decoded = true
        · simp [gaussianFiniteProgramStep, hdecode, hcheck] at hstep
          subst decoded
          exact hcheck
        · have hcheck' : gaussianFiniteProgramRunCheck program input decoded = false :=
            Bool.eq_false_of_not_eq_true hcheck
          simp [gaussianFiniteProgramStep, hdecode, hcheck'] at hstep
  induction stage with
  | zero =>
      exact step_checked 0 output hexec
  | succ stage ih =>
      unfold GaussianFiniteExecutionReaches at hexec
      rw [gaussianFiniteProgramEvaluate] at hexec
      cases hprevious : gaussianFiniteProgramEvaluate program input stage with
      | none =>
          rw [hprevious] at hexec
          exact step_checked (stage + 1) output hexec
      | some previous =>
          rw [hprevious] at hexec
          have hsame : previous = output := Option.some.inj hexec
          subst previous
          exact ih hprevious

/-- Semantic realization ties every returned receipt to a checked compact
certificate and makes the terminal cells cover the input root.  It does not
assume a minimax inequality. -/
def GaussianFiniteProgramOutputRealized [NeZero K] (A : Finset (Fin K))
    (M epsilon : ℝ) (input : GaussianFiniteProgramInput K)
    (output : GaussianFiniteProgramOutput) : Prop :=
  input.encodedFace = A.toList.map Fin.val ∧ M ≤ (input.quotientRadius : ℝ) ∧
  (input.tolerance : ℝ) ≤ epsilon ∧
  ∃ certifiedCells : List (CertifiedCompactCell A),
    certifiedCells ≠ [] ∧ certifiedCells.length = output.receipts.length ∧
    certifiedCells.map (fun cell => cell.output.2.2) = output.receipts ∧
    certifiedCells.map (fun cell => (cell.varianceCell, cell.rateCell)) =
      output.terminalProductCells ∧
    (∀ cell ∈ certifiedCells, ValidCertifiedCompactCell A M epsilon cell) ∧
    ∀ v r : Fin K → ℝ, InRationalCell v input.varianceRoot →
      InRationalCell r input.rateRoot →
      ∃ cell ∈ certifiedCells,
        InRationalCell v cell.varianceCell ∧ InRationalCell r cell.rateCell

/-- Analytic soundness is derived from receipt soundness, not stored in the
decidable run checker. -/
lemma gaussianFiniteProgramRun_sound [NeZero K] (A : Finset (Fin K))
    (M epsilon : ℝ) (input : GaussianFiniteProgramInput K)
    (output : GaussianFiniteProgramOutput)
    (hrun : gaussianFiniteProgramRunCheck gaussianFiniteRefinementProgram input output = true)
    (hrealized : GaussianFiniteProgramOutputRealized A M epsilon input output) :
    ∀ v r : Fin K → ℝ, InRationalCell v input.varianceRoot →
      InRationalCell r input.rateRoot →
      ∃ cell : CertifiedCompactCell A,
        (cell.varianceCell, cell.rateCell) ∈ output.terminalProductCells ∧
        InRationalCell v cell.varianceCell ∧ InRationalCell r cell.rateCell ∧
        ENNReal.ofReal cell.output.1.1 ≤ gaussianCompactValue A v r M ∧
        gaussianCompactValue A v r M ≤ ENNReal.ofReal cell.output.1.2 ∧
        gaussianSelectorCompactWorstRisk A v r M cell.output.2.1 ≤
          ENNReal.ofReal cell.output.1.2 ∧
        cell.output.1.2 - cell.output.1.1 ≤ epsilon := by
  intro v r hv hr
  rcases hrealized with ⟨_, _, _, certifiedCells, _, _, _, hpairs, hvalid, hcover⟩
  rcases hcover v r hv hr with ⟨cell, hmem, hvcell, hrcell⟩
  have hpair : (cell.varianceCell, cell.rateCell) ∈ output.terminalProductCells := by
    rw [← hpairs]
    exact List.mem_map.mpr ⟨cell, hmem, rfl⟩
  rcases hvalid cell hmem with
    ⟨hpositiveCell, _, hbaseV, hbaseR, hcertificate, hcovariance⟩
  have hpositive : ∀ k ∈ A, 0 < v k ∧ 0 < r k := by
    rcases hpositiveCell with ⟨_, _, _, _, _, eigenLower, eigenUpper, _, _, hall⟩
    exact (hall v r hvcell hrcell).1
  rcases hcovariance v r hvcell hrcell with
    ⟨covarianceCell, hcovmem, _, hbaseCov, htargetCov⟩
  have hsound := compactQuotientCertificate_sound_on_recorded_cell A
    cell.baseVariance cell.baseRate v r M epsilon cell.eigenLower cell.eigenUpper
    cell.observationRadius cell.varianceCells cell.parameterCells cell.observationCells
    cell.rateCells cell.covarianceCells cell.output hcertificate hpositive
    ⟨covarianceCell, hcovmem, hbaseCov, htargetCov⟩
  refine ⟨cell, hpair, hvcell, hrcell, hsound.1, hsound.2.1, hsound.2.2, ?_⟩
  have hrefinement : ValidCompactCertificate A cell.baseVariance cell.baseRate M epsilon
      cell.output := hcertificate.2.1.2.2.2.2
  rcases hrefinement with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hwidth⟩
  exact hwidth

/-- Termination of the concrete program on one rational root. -/
def GaussianProgramTerminatesOn [NeZero K] (A : Finset (Fin K))
    (M epsilon : ℝ) (varianceRoot rateRoot : RationalCell) : Prop :=
  ∃ input : GaussianFiniteProgramInput K, ∃ stage : ℕ,
  ∃ output : GaussianFiniteProgramOutput,
    input.encodedFace = A.toList.map Fin.val ∧
    input.varianceRoot = varianceRoot ∧ input.rateRoot = rateRoot ∧
    M ≤ (input.quotientRadius : ℝ) ∧ 0 < input.tolerance ∧
    (input.tolerance : ℝ) ≤ epsilon ∧
    GaussianFiniteExecutionReaches gaussianFiniteRefinementProgram input stage output ∧
    gaussianFiniteProgramRunCheck gaussianFiniteRefinementProgram input output = true ∧
    GaussianFiniteProgramOutputRealized A M epsilon input output

-- @node: thm:gaussian-finite-certificate
/-- The concrete rational refinement program terminates on every compact
positive cell and its replayed receipts give the claimed compact-game bounds. -/
theorem gaussian_finite_certificate {K : ℕ} [NeZero K] :
    ValidGaussianFiniteRefinementProgram gaussianFiniteRefinementProgram ∧
    (∀ (A : Finset (Fin K)) (M epsilon : ℝ)
      (varianceCell rateCell : RationalCell),
      2 ≤ A.card → 0 < M → 0 < epsilon →
      CompactPositiveGaussianCell A varianceCell rateCell →
      GaussianProgramTerminatesOn A M epsilon varianceCell rateCell) ∧
    (∃ B6 : Fin 3 → Fin 3 → ℝ,
      B6 = (hitMatrix 6 sixUnitCounts (fun _ => 1 / 3)).1 ∧
      B6 0 0 = 3125 / 7776 ∧ B6 0 1 = 64 / 243 ∧ B6 0 2 = 4 / 243 ∧
      B6 1 0 = 3125 / 15552 ∧ B6 1 1 = 80 / 243 ∧ B6 1 2 = 20 / 243 ∧
      B6 2 0 = 125 / 15552 ∧ B6 2 1 = 20 / 243 ∧ B6 2 2 = 80 / 243 ∧
      (∑ k, B6 k 0) = 2375 / 3888 ∧
      (∑ k, B6 k 1) = 164 / 243 ∧ (∑ k, B6 k 2) = 104 / 243 ∧
      (∀ l, l ≠ 1 → (∑ k, B6 k l) < ∑ k, B6 k 1) ∧
      ((fun k => B6 k 1 / (∑ i, B6 i 1)) : Fin 3 → ℝ) =
        ![16 / 41, 20 / 41, 5 / 41]) ∧
    (∀ (A : Finset (Fin K)) (M epsilon : ℝ)
      (n : ℕ) (m : Fin K → ℕ) (p v : Fin K → ℝ),
      2 ≤ A.card → 0 < M → 0 < epsilon →
      WellFormedMenu n K m → InSimplex p → (∀ k ∈ A, 0 < v k) →
      let B := (hitMatrix n m p).1
      ∃ roots : List (RationalCell × RationalCell), roots ≠ [] ∧
        (∀ root ∈ roots, CompactPositiveGaussianCell A root.1 root.2 ∧
          GaussianProgramTerminatesOn A M epsilon root.1 root.2) ∧
        ∀ p' : Fin K → ℝ, InSimplex p' →
          ∃ root ∈ roots, InRationalCell v root.1 ∧
            InRationalCell (matVec B p') root.2 ∧
            ∀ k ∈ A, 0 < matVec B p' k) ∧
    (∀ (A : Finset (Fin K)) (M epsilon : ℝ)
      (allocationSet : Set (Fin K → ℝ)),
      2 ≤ A.card → 0 < M → 0 < epsilon → IsCompact allocationSet →
      (∀ alpha ∈ allocationSet, InActiveSimplex A alpha) →
      ∀ v : Fin K → ℝ, (∀ k ∈ A, 0 < v k) →
      ∃ roots : List (RationalCell × RationalCell), roots ≠ [] ∧
        (∀ root ∈ roots, CompactPositiveGaussianCell A root.1 root.2 ∧
          GaussianProgramTerminatesOn A M epsilon root.1 root.2) ∧
        ∀ alpha ∈ allocationSet, ∃ root ∈ roots,
          InRationalCell v root.1 ∧ InRationalCell alpha root.2) ∧
    (∀ (A : Finset (Fin K)) (M epsilon : ℝ) (v : Fin K → ℝ),
      2 ≤ A.card → 0 < M → 0 < epsilon → (∀ k ∈ A, 0 < v k) →
      ¬ ∃ roots : List (RationalCell × RationalCell), roots ≠ [] ∧
        (∀ root ∈ roots, GaussianProgramTerminatesOn A M epsilon root.1 root.2) ∧
        ∀ alpha : Fin K → ℝ, InActiveSimplex A alpha →
          ∃ root ∈ roots, InRationalCell v root.1 ∧ InRationalCell alpha root.2) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
