import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Certificate
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.HitFactorization
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.ScheduleLawBridge
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.WeakCompactness
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitBernoulli
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitCRFace
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TGaussianFiniteCertificate
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TOracleTransferBernoulli
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TOracleTransferCR
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.CanonicalRepresentatives
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TTwoPolicyMinimax
import Causalean.Mathlib.Optimization.RationalLP

set_option linter.unusedVariables false
set_option linter.style.openClassical false

/-! # Uniform boundary certificate -/

open scoped BigOperators ENNReal
open MeasureTheory Filter Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- The prespecified three-way primitive split. -/
def IsStageIndexedThreeWaySplit (pilot screen decision : ℕ → ℕ)
    (lambda : ℕ → ℝ) : Prop :=
  Tendsto pilot atTop atTop ∧ Tendsto screen atTop atTop ∧
    Tendsto decision atTop atTop ∧
    Tendsto (fun C => (pilot C : ℝ) / C) atTop (nhds 0) ∧
    Tendsto (fun C => (screen C : ℝ) / C - lambda C) atTop (nhds 0) ∧
    Tendsto (fun C => (decision C : ℝ) / C - (1 - lambda C)) atTop (nhds 0) ∧
    ∀ C, pilot C + screen C + decision C = C

/-- Bernoulli primitive risk, integrating over pilot, screen, and decision. -/
def bernoulliThreeWayPrimitiveRisk (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (A : Finset (Fin K)) (lambda : ℝ)
    (pilotSize screenSize decisionSize : ℕ)
    (selector : (Fin pilotSize → Record K n) → (ActiveIndex A → ℝ) →
      (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ :=
  ∫ pilotRecords, ∫ screenRecords, ∫ decisionRecords,
    ∑ a, selector pilotRecords (calibratedEstimator screenRecords m A).2
        (calibratedEstimator decisionRecords m A).2 a *
      simpleRegret A (exactSliceWelfare P m) a
      ∂(Measure.pi fun _ : Fin decisionSize => bernoulliObservedLaw P p m)
    ∂(Measure.pi fun _ : Fin screenSize => bernoulliObservedLaw P p m)
  ∂(Measure.pi fun _ : Fin pilotSize => bernoulliObservedLaw P p m)

/-- Exact-count analogue of the unconditional three-way risk. -/
def crThreeWayPrimitiveRisk (P : Measure (Schedule n))
    (pilotCounts screenCounts decisionCounts : Fin K → ℕ)
    (m : Fin K → ℕ) (A : Finset (Fin K)) (lambda : ℝ)
    (pilotSize screenSize decisionSize : ℕ)
    (selector : (Fin pilotSize → Record K n) → (ActiveIndex A → ℝ) →
      (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ :=
  ∫ pilotRecords, ∫ screenRecords, ∫ decisionRecords,
    ∑ a, selector pilotRecords (calibratedEstimator screenRecords m A).2
        (calibratedEstimator decisionRecords m A).2 a *
      simpleRegret A (exactSliceWelfare P m) a
      ∂(crObservedLaw (C := decisionSize) P decisionCounts m)
    ∂(crObservedLaw (C := screenSize) P screenCounts m)
  ∂(crObservedLaw (C := pilotSize) P pilotCounts m)

/-- Part of Bernoulli primitive regret incurred by policies separated from the
best policy by at least the fixed welfare gap. -/
def bernoulliFixedGapInferiorContribution (P : Measure (Schedule n))
    (p : Fin K → ℝ) (m : Fin K → ℕ) (A : Finset (Fin K)) (lambda gap : ℝ)
    (pilotSize screenSize decisionSize : ℕ)
    (selector : (Fin pilotSize → Record K n) → (ActiveIndex A → ℝ) →
      (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ :=
  ∫ pilotRecords, ∫ screenRecords, ∫ decisionRecords,
    ∑ a, selector pilotRecords (calibratedEstimator screenRecords m A).2
        (calibratedEstimator decisionRecords m A).2 a *
      (if gap ≤ simpleRegret A (exactSliceWelfare P m) a then
        simpleRegret A (exactSliceWelfare P m) a else 0)
      ∂(Measure.pi fun _ : Fin decisionSize => bernoulliObservedLaw P p m)
    ∂(Measure.pi fun _ : Fin screenSize => bernoulliObservedLaw P p m)
  ∂(Measure.pi fun _ : Fin pilotSize => bernoulliObservedLaw P p m)

/-- Exact-count fixed-gap inferior-policy contribution. -/
def crFixedGapInferiorContribution (P : Measure (Schedule n))
    (pilotCounts screenCounts decisionCounts : Fin K → ℕ)
    (m : Fin K → ℕ) (A : Finset (Fin K)) (lambda gap : ℝ)
    (pilotSize screenSize decisionSize : ℕ)
    (selector : (Fin pilotSize → Record K n) → (ActiveIndex A → ℝ) →
      (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ :=
  ∫ pilotRecords, ∫ screenRecords, ∫ decisionRecords,
    ∑ a, selector pilotRecords (calibratedEstimator screenRecords m A).2
        (calibratedEstimator decisionRecords m A).2 a *
      (if gap ≤ simpleRegret A (exactSliceWelfare P m) a then
        simpleRegret A (exactSliceWelfare P m) a else 0)
      ∂(crObservedLaw (C := decisionSize) P decisionCounts m)
    ∂(crObservedLaw (C := screenSize) P screenCounts m)
  ∂(crObservedLaw (C := pilotSize) P pilotCounts m)

/-- Finite instruction set for the rational hierarchical program. -/
inductive HierarchicalProgramOpcode where
  | validateDeclaredFace | enumerateRetainedFaces | runCompactCertificates
  | assembleSelectorTables | branchBernoulliSimplex | branchExactSimplex
  | excludeBoundary | emitOutput
deriving Repr, DecidableEq

def hierarchicalProgramCode : List HierarchicalProgramOpcode :=
  [.validateDeclaredFace, .enumerateRetainedFaces, .runCompactCertificates,
   .assembleSelectorTables, .branchBernoulliSimplex, .branchExactSimplex,
   .excludeBoundary, .emitOutput]

/-- Exactly the finite rational inputs required by one program invocation. -/
structure HierarchicalProgramInput (K : ℕ) where
  encodedDeclaredFace : List ℕ
  covarianceCell : RationalCell
  designCell : RationalCell
  tolerance : ℚ
  stageIndex : ℕ
deriving Repr, DecidableEq

/-- Finite represented active selector table for one retained face. -/
structure EncodedRetainedSelector where
  encodedFace : List ℕ
  quotientRadius : ℚ
  observationPartition : List RationalCell
  actionWeights : List (RationalCell × List (ℕ × ℚ))
  tailActionWeights : List (List Bool × List (ℕ × ℚ))
deriving Repr, DecidableEq

/-- Rational program output.  The real-valued selector and risk interpretation
are deliberately absent and are supplied by `HierarchicalProgramSemanticEvaluation`. -/
structure HierarchicalProgramOutput where
  lowerBound : ℚ
  upperBound : ℚ
  stageIndex : ℕ
  splitFraction : ℚ
  screeningThreshold : ℚ
  selectors : List EncodedRetainedSelector
  terminalCells : List RationalCell
  certificates : List (List ℕ × CertificateReceipt)
  outerTranscript : OuterDesignTranscript
  workingPrecision : ℕ
  checkerRevision : String
  checksum : String
deriving Repr

/-- The implementation carrier is a finite rational-input program.  Its only
executable field consumes the encoded face, rational covariance/design cells,
rational tolerance, and stage index packaged by `HierarchicalProgramInput`,
and returns finite rational tables.  It contains no real-valued selector or
other unrestricted real-function implementation field. -/
structure FiniteRationalHierarchicalProgram (K : ℕ) where
  code : List HierarchicalProgramOpcode
  checkerRevision : String
  checksum : String
  run : HierarchicalProgramInput K → HierarchicalProgramOutput

def hierarchicalProgramChecksum (program : FiniteRationalHierarchicalProgram K) : String :=
  reprStr (program.code, program.checkerRevision)

def ValidFiniteRationalHierarchicalProgram
    (program : FiniteRationalHierarchicalProgram K) : Prop :=
  program.code = hierarchicalProgramCode ∧ program.checkerRevision ≠ "" ∧
    program.checksum = hierarchicalProgramChecksum program

def hierarchicalProgramOutputChecksum (output : HierarchicalProgramOutput) : String :=
  reprStr (output.lowerBound, output.upperBound, output.stageIndex, output.splitFraction,
    output.screeningThreshold, output.selectors, output.terminalCells,
    output.certificates, output.outerTranscript, output.workingPrecision,
    output.checkerRevision)

/-- Fully decidable finite replay of a hierarchical program run. -/
def HierarchicalProgramRun (program : FiniteRationalHierarchicalProgram K)
    (input : HierarchicalProgramInput K) (output : HierarchicalProgramOutput) : Prop :=
  ValidFiniteRationalHierarchicalProgram program ∧
    input.encodedDeclaredFace ≠ [] ∧ input.covarianceCell ≠ [] ∧
    input.designCell ≠ [] ∧ 0 < input.tolerance ∧ 0 < input.stageIndex ∧
    0 ≤ output.lowerBound ∧ output.lowerBound ≤ output.upperBound ∧
    output.upperBound - output.lowerBound ≤ input.tolerance ∧
    output.stageIndex = input.stageIndex ∧
    output.splitFraction ∈ Ioo (0 : ℚ) 1 ∧ 0 < output.screeningThreshold ∧
    output.selectors ≠ [] ∧ output.terminalCells ≠ [] ∧
    output.certificates ≠ [] ∧ output.workingPrecision > 0 ∧
    (output.selectors.map EncodedRetainedSelector.encodedFace).Nodup ∧
    (∀ selector ∈ output.selectors, 0 < selector.quotientRadius) ∧
    (output.certificates.map Prod.fst).Nodup ∧
    output.selectors.map (fun selector =>
      (selector.encodedFace, selector.quotientRadius)) =
        output.certificates.map (fun item => (item.1, item.2.quotientRadius)) ∧
    (∀ item ∈ output.certificates,
      certificateReceiptCheck item.2 = true ∧ item.2.face = item.1 ∧
      item.2.requestedTolerance ≤ input.tolerance ∧
      item.2.upperBound - item.2.lowerBound ≤ input.tolerance ∧
      item.2.checksum = certificateChecksum item.2) ∧
    output.terminalCells = output.certificates.flatMap (fun item => item.2.terminalBranchCells) ∧
    output.checkerRevision = program.checkerRevision ∧
    output.checksum = hierarchicalProgramOutputChecksum output

def hierarchicalProgramRunCheck (program : FiniteRationalHierarchicalProgram K)
    (input : HierarchicalProgramInput K) (output : HierarchicalProgramOutput) : Bool :=
  decide (ValidFiniteRationalHierarchicalProgram program) &&
  decide (input.encodedDeclaredFace ≠ [] ∧ input.covarianceCell ≠ [] ∧
    input.designCell ≠ [] ∧ 0 < input.tolerance ∧ 0 < input.stageIndex) &&
  decide (0 ≤ output.lowerBound ∧ output.lowerBound ≤ output.upperBound ∧
    output.upperBound - output.lowerBound ≤ input.tolerance ∧
    output.stageIndex = input.stageIndex ∧
    output.splitFraction ∈ Ioo (0 : ℚ) 1 ∧ 0 < output.screeningThreshold ∧
    output.selectors ≠ [] ∧ output.terminalCells ≠ [] ∧
    output.certificates ≠ [] ∧ output.workingPrecision > 0 ∧
    (output.selectors.map EncodedRetainedSelector.encodedFace).Nodup ∧
    (∀ selector ∈ output.selectors, 0 < selector.quotientRadius) ∧
    (output.certificates.map Prod.fst).Nodup ∧
    output.selectors.map (fun selector =>
      (selector.encodedFace, selector.quotientRadius)) =
        output.certificates.map (fun item => (item.1, item.2.quotientRadius))) &&
  output.certificates.all (fun item =>
    certificateReceiptCheck item.2 && decide (item.2.face = item.1) &&
    decide (item.2.requestedTolerance ≤ input.tolerance) &&
    decide (item.2.upperBound - item.2.lowerBound ≤ input.tolerance) &&
    decide (item.2.checksum = certificateChecksum item.2)) &&
  decide (output.terminalCells =
    output.certificates.flatMap (fun item => item.2.terminalBranchCells)) &&
  rationalRefinementTraceCheck output.outerTranscript.bernoulliRoots
    output.outerTranscript.bernoulliTerminals output.outerTranscript.bernoulliTrace &&
  rationalRefinementTraceCheck output.outerTranscript.exactRoots
    output.outerTranscript.exactTerminals output.outerTranscript.exactTrace &&
  decide (output.checkerRevision = program.checkerRevision ∧
    output.checksum = hierarchicalProgramOutputChecksum output)

/-- The finite program is deterministic and terminates on every valid rational
input.  Its computed output is checked directly, and uniqueness identifies any
other accepted output with that computation. -/
def FiniteHierarchicalProgramOperational
    (program : FiniteRationalHierarchicalProgram K) : Prop :=
  ValidFiniteRationalHierarchicalProgram program ∧
    (∀ input, input.encodedDeclaredFace ≠ [] → input.covarianceCell ≠ [] →
      input.designCell ≠ [] → 0 < input.tolerance → 0 < input.stageIndex →
      hierarchicalProgramRunCheck program input (program.run input) = true ∧
        ∀ output, hierarchicalProgramRunCheck program input output = true →
          output = program.run input)

/-- Assemble the declared-face selector from the retained-face semantic rules. -/
def assembleDeclaredFaceSelector (A : Finset (Fin K)) (T : ℝ)
    (subfaceRule : ∀ S : Finset (Fin K),
      (ActiveIndex S → ℝ) → (ActiveIndex S → ℝ) → Fin K → ℝ)
    (screen decision : ActiveIndex A → ℝ) : Fin K → ℝ :=
  let S := retainedArms A T screen
  subfaceRule S (fun k => screen (retainedIndex A T screen k))
    (fun k => decision (retainedIndex A T screen k))

/-- Decode the valid indices recorded by a finite face table. -/
def decodeEncodedFace [NeZero K] (face : List ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun k => k.1 ∈ face

/-- Canonical finite-table evaluation: use the first containing observation
cell, and otherwise the first row matching the recorded tail signature. -/
noncomputable def decodeEncodedRetainedSelector [NeZero K]
    (S : Finset (Fin K)) (encoded : EncodedRetainedSelector)
    (x : ActiveIndex S → ℝ) (a : Fin K) : ℝ := by
  classical
  let qx := quotientObservation S x
  match encoded.actionWeights.find? (fun entry =>
      decide (InQuotientRationalCell S qx entry.1)) with
  | some entry => exact rationalActionWeight entry.2 a
  | none =>
      let signature := observationTailSignature S encoded.quotientRadius x
      match encoded.tailActionWeights.find? (fun entry => entry.1 == signature) with
      | some entry => exact rationalActionWeight entry.2 a
      | none => exact 0

/-- The unique retained-face row is selected by its finite encoded face. -/
def encodedSelectorForFace [NeZero K] (output : HierarchicalProgramOutput)
    (S : Finset (Fin K)) : Option EncodedRetainedSelector :=
  output.selectors.find? fun encoded =>
    encoded.encodedFace == S.toList.map Fin.val

/-- Canonical declared-face selector decoded only from the finite output
tables and their tail signatures. -/
noncomputable def decodeHierarchicalProgramSelector [NeZero K]
    (A : Finset (Fin K)) (output : HierarchicalProgramOutput)
    (screen decision : ActiveIndex A → ℝ) (a : Fin K) : ℝ := by
  classical
  let T := (output.screeningThreshold : ℝ)
  let S := retainedArms A T screen
  if hsingle : S.card = 1 then
    exact singletonActiveSelector S (scaledRetainedDecision A
      (output.splitFraction : ℝ) T screen decision) a
  else
    match encodedSelectorForFace output S with
    | some encoded =>
        exact decodeEncodedRetainedSelector S encoded
          (scaledRetainedDecision A (output.splitFraction : ℝ) T screen decision) a
    | none => exact 0

/-- Canonical dependent compact-certificate payload decoded from one receipt
row. -/
noncomputable def decodeCertificatePayload [NeZero K]
    (item : List ℕ × CertificateReceipt) :
    Σ S : Finset (Fin K), CompactCertificateOutput S := by
  classical
  let S := decodeEncodedFace (K := K) item.1
  let selector : (ActiveIndex S → ℝ) → Fin K → ℝ := fun x a =>
    decodeEncodedRetainedSelector S
      { encodedFace := item.1
        quotientRadius := item.2.quotientRadius
        observationPartition := item.2.observationPartition
        actionWeights := item.2.selectorTable
        tailActionWeights := item.2.tailSelectorTable } x a
  exact ⟨S, ((item.2.lowerBound : ℝ), (item.2.upperBound : ℝ)), selector, item.2⟩

/-- The real semantics is a canonical decode of one checked finite output.
No semantic witness is selected by choice. -/
noncomputable def decodeHierarchicalProgramOutput [NeZero K]
    (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ) (v : Fin K → ℝ)
    (encoded : HierarchicalProgramOutput) : HierarchicalRoutineOutput A :=
  ((ENNReal.ofReal encoded.lowerBound, ENNReal.ofReal encoded.upperBound),
    faceMechanismValues B A v,
    decodeHierarchicalProgramSelector A encoded,
    encoded.certificates.map (decodeCertificatePayload (K := K)),
    encoded.outerTranscript)

/-- The separate real-valued semantics of a successful finite output.  Receipt
equality ties every semantic compact selector to the rational certificate that
the program emitted. -/
def HierarchicalProgramSemanticEvaluation [NeZero K]
    (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ) (v r : Fin K → ℝ)
    (input : HierarchicalProgramInput K) (encoded : HierarchicalProgramOutput)
    (semantic : HierarchicalRoutineOutput A) : Prop :=
  semantic = decodeHierarchicalProgramOutput A B v encoded ∧
    input.encodedDeclaredFace = A.toList.map Fin.val ∧
    InRationalCell r input.designCell ∧
    CovarianceCellContains A v r input.covarianceCell ∧
    encoded.selectors = encoded.certificates.map (fun item =>
      { encodedFace := item.1
        quotientRadius := item.2.quotientRadius
        observationPartition := item.2.observationPartition
        actionWeights := item.2.selectorTable
        tailActionWeights := item.2.tailSelectorTable }) ∧
    hierarchicalRoutine A B v r (encoded.splitFraction : ℝ)
      (encoded.screeningThreshold : ℝ) (input.tolerance : ℝ) semantic

/-- Soundness of real evaluation is a theorem derived from the finite replay
and the analytic compact-certificate bounds. -/
lemma hierarchicalProgramSemanticEvaluation_sound [NeZero K]
    (program : FiniteRationalHierarchicalProgram K) (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v r : Fin K → ℝ)
    (input : HierarchicalProgramInput K) (encoded : HierarchicalProgramOutput)
    (semantic : HierarchicalRoutineOutput A)
    (hrun : hierarchicalProgramRunCheck program input encoded = true)
    (hsemantic : HierarchicalProgramSemanticEvaluation A B v r input encoded semantic) :
    semantic.1.1 ≤ gaussianGlobalValue A v r ∧
      gaussianGlobalValue A v r ≤ ENNReal.ofReal
        (⨆ h : Fin K → ℝ, hierarchicalSplitRisk A v r h
          (encoded.splitFraction : ℝ) semantic.2.2.1) ∧
      ENNReal.ofReal (⨆ h : Fin K → ℝ, hierarchicalSplitRisk A v r h
        (encoded.splitFraction : ℝ) semantic.2.2.1) ≤ semantic.1.2 ∧
      semantic.1.2.toReal - semantic.1.1.toReal ≤ (input.tolerance : ℝ) := by
  rcases hsemantic with ⟨hdecode, _, _, _, _, hroutine⟩
  have hlo : semantic.1.1 = ENNReal.ofReal encoded.lowerBound := by
    simp [hdecode, decodeHierarchicalProgramOutput]
  have hup : semantic.1.2 = ENNReal.ofReal encoded.upperBound := by
    simp [hdecode, decodeHierarchicalProgramOutput]
  rcases hroutine with ⟨hdomain, hspec⟩
  rcases hspec with ⟨_, _, _, hrnonneg, hboundary, hpositiveSpec, _, _⟩
  have hpositive : ∀ k ∈ A, 0 < r k := by
    intro k hk
    have hrnonneg := hrnonneg k hk
    refine lt_of_le_of_ne hrnonneg ?_
    intro hrzero
    have hcard := hdomain.1
    have hnonempty : (A.erase k).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsub : A ⊆ {k} := by
        intro j hj
        by_contra hjk
        have : j ∈ A.erase k := Finset.mem_erase.mpr ⟨by simpa using hjk, hj⟩
        simpa [hempty] using this
      have : A.card ≤ 1 := by
        calc A.card ≤ ({k} : Finset (Fin K)).card := Finset.card_le_card hsub
          _ = 1 := by simp
      omega
    obtain ⟨j, hjA, hjne⟩ : ∃ j ∈ A, j ≠ k := by
      obtain ⟨j, hj⟩ := hnonempty
      exact ⟨j, (Finset.mem_erase.mp hj).2, (Finset.mem_erase.mp hj).1⟩
    have hrel : ActionRelevantCoordinate A k := ⟨hk, ⟨j, hjA, hjne⟩⟩
    have htop := hboundary ⟨k, hrel, hrzero.symm⟩
    have : semantic.1.1 = ⊤ := htop.1
    rw [hlo] at this
    simpa using this
  rcases hpositiveSpec hpositive with
    ⟨_, _, _, _, _, hlower, hmiddle, hupper, _, hgap, _⟩
  exact ⟨hlower, hmiddle, hupper, hgap⟩

/-- A finite rational invocation assembled from the data-selected cells. -/
def hierarchicalProgramInput (A : Finset (Fin K)) (covarianceCell designCell : RationalCell)
    (tolerance : ℚ) (stage : ℕ) : HierarchicalProgramInput K where
  encodedDeclaredFace := A.toList.map Fin.val
  covarianceCell := covarianceCell
  designCell := designCell
  tolerance := tolerance
  stageIndex := stage

/-- Empirical covariance statistic computed from the pilot records alone. -/
def pilotCovarianceStatistic (O : Fin C → Record K n) (m : Fin K → ℕ)
    (A : Finset (Fin K)) : Fin K → Fin K → ℝ :=
  empiricalCovariance (fun k o => if hk : k ∈ A then
    if o.2.1 ∈ exactSlice n (m k) then
      recordWelfare n o - (calibratedEstimator O m A).1 k else 0 else 0) O

/-- Concrete deterministic outward snap of the empirical diagonal. -/
def deterministicPilotOutwardSnap (empirical : Fin K → Fin K → ℝ)
    (rate : Fin K → ℝ) : Fin K → ℝ :=
  fun k => max 0 (empirical k k * rate k)

lemma deterministicPilotOutwardSnap_valid (A : Finset (Fin K)) :
    DataDeterminedOutwardCovarianceSnap A deterministicPilotOutwardSnap := by
  intro empirical rate k hk
  exact le_max_right _ _

/-- Canonical boundary rule for an ordered finite covariance partition: take
the first containing cell.  Thus shared boundaries are resolved by list order,
not by an unconstrained choice function. -/
noncomputable def firstContainingCovarianceCell [NeZero K]
    (A : Finset (Fin K)) (cells : List RationalCell)
    (v rate : Fin K → ℝ) : RationalCell := by
  classical
  exact (cells.find? fun cell => decide (CovarianceCellContains A v rate cell)).getD []

lemma firstContainingCovarianceCell_valid [NeZero K]
    (A : Finset (Fin K)) (cells : List RationalCell) :
    DeterministicCovarianceCellAssignment A cells
      (firstContainingCovarianceCell A cells) := by sorry

/-- Every fibre of the canonical first-containing-cell rule is measurable;
this is the pilot-measurability fact used after composing with the empirical
covariance statistic. -/
lemma firstContainingCovarianceCell_measurable_preimage [NeZero K]
    (A : Finset (Fin K)) (cells : List RationalCell) (cell : RationalCell) :
    MeasurableSet {vr : (Fin K → ℝ) × (Fin K → ℝ) |
      firstContainingCovarianceCell A cells vr.1 vr.2 = cell} := by sorry

def snappedVarianceFromPilot (A : Finset (Fin K)) (O : Fin C → Record K n)
    (m : Fin K → ℕ) (rate : Fin K → ℝ)
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) : Fin K → ℝ :=
  snap (pilotCovarianceStatistic O m A) rate

def selectedCovarianceCell [NeZero K] (A : Finset (Fin K)) (O : Fin C → Record K n)
    (m : Fin K → ℕ) (rate : Fin K → ℝ)
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ)
    (cells : List RationalCell) : RationalCell :=
  firstContainingCovarianceCell A cells (snappedVarianceFromPilot A O m rate snap) rate

/-- The good-pilot event is explicitly data-determined; it says that the cell
selected from the empirical snap also contains the true covariance. -/
def PilotCovarianceGoodEvent [NeZero K] (A : Finset (Fin K))
    (P : Measure (Schedule n)) (O : Fin C → Record K n) (m : Fin K → ℕ)
    (rate : Fin K → ℝ)
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ)
    (cells : List RationalCell) : Prop :=
  let snappedV := snappedVarianceFromPilot A O m rate snap
  let cell := selectedCovarianceCell A O m rate snap cells
  2 ≤ A.card ∧ CovarianceCellContains A snappedV rate cell ∧
    CovarianceCellContains A (fun k => sliceVariance P (m k)) rate cell

/-- Characteristic-function formulation of a sequence-indexed `sqrt(C)`
Gaussian approximation. -/
def SequenceSqrtCBlockGaussianApproximation (A : Finset (Fin K))
    (block : ℕ → ℕ) (law : ∀ C, Measure (Fin (block C) → Record K n))
    (center : ℕ → ActiveIndex A → ℝ)
    (statistic : ∀ C, (Fin (block C) → Record K n) → ActiveIndex A → ℝ)
    (covariance : ℕ → ActiveIndex A → ActiveIndex A → ℝ) : Prop :=
  ∀ t : ActiveIndex A → ℝ,
    Tendsto (fun C => (∫ O, Real.cos (∑ k, t k *
      (Real.sqrt C * (statistic C O k - center C k))) ∂(law C)) -
      Real.exp (-((∑ i, ∑ j, t i * covariance C i j * t j) / 2)))
      atTop (nhds 0) ∧
    Tendsto (fun C => ∫ O, Real.sin (∑ k, t k *
      (Real.sqrt C * (statistic C O k - center C k))) ∂(law C)) atTop (nhds 0)

/-- Explicit independence witness for screening and decision blocks. -/
def IndependentScreenDecisionBlocks {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (screenLaw : Measure X) (decisionLaw : Measure Y) (jointLaw : Measure (X × Y)) : Prop :=
  jointLaw = screenLaw.prod decisionLaw

/-- Both primitive designs have a fixed limiting split fraction, independent
screen/decision blocks, covariances `Sigma_N/lambda_N` and
`Sigma_N/(1-lambda_N)`, and the displayed decision rescaling. -/
def SequenceIndexedThreeWayGaussianClause [NeZero K]
    (Pseq : ℕ → Measure (Schedule n)) (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (allocations : Set (Fin K → ℝ))
    (counts : (Fin K → ℝ) → ℕ → Fin K → ℕ) (m : Fin K → ℕ)
    (fixedLambda : ℝ) (lambda : ℕ → ℝ) (screen decision : ℕ → ℕ) : Prop :=
  fixedLambda ∈ Ioo (0 : ℝ) 1 ∧ Tendsto lambda atTop (nhds fixedLambda) ∧
  (∀ alpha ∈ allocations, InActiveSimplex A alpha) ∧
  (∀ alpha ∈ allocations, ∀ N, ∑ k, counts alpha N k = N) ∧
  (∀ alpha ∈ allocations, ∀ N k, k ∉ A → counts alpha N k = 0) ∧
  (∀ p, InSimplex p →
    let rate := matVec B p
    let center := fun N k => exactSliceWelfare (Pseq N) m k.1
    let SigmaScreen := fun N (i j : ActiveIndex A) =>
      if i = j then sliceVariance (Pseq N) (m i.1) / (lambda N * rate i.1) else 0
    let SigmaDecision := fun N (i j : ActiveIndex A) =>
      if i = j then sliceVariance (Pseq N) (m i.1) / ((1 - lambda N) * rate i.1) else 0
    (∃ jointLaw : ∀ N, Measure ((Fin (screen N) → Record K n) ×
        (Fin (decision N) → Record K n)), ∀ N,
      IndependentScreenDecisionBlocks
        (Measure.pi fun _ : Fin (screen N) => bernoulliObservedLaw (Pseq N) p m)
        (Measure.pi fun _ : Fin (decision N) => bernoulliObservedLaw (Pseq N) p m)
        (jointLaw N)) ∧
    SequenceSqrtCBlockGaussianApproximation A screen
      (fun N => Measure.pi fun _ : Fin (screen N) => bernoulliObservedLaw (Pseq N) p m)
      center (fun _ O k => (calibratedEstimator O m A).2 k) SigmaScreen ∧
    SequenceSqrtCBlockGaussianApproximation A decision
      (fun N => Measure.pi fun _ : Fin (decision N) => bernoulliObservedLaw (Pseq N) p m)
      center (fun _ O k => (calibratedEstimator O m A).2 k) SigmaDecision ∧
    SequenceSqrtCBlockGaussianApproximation A decision
      (fun N => Measure.pi fun _ : Fin (decision N) => bernoulliObservedLaw (Pseq N) p m)
      center (fun N O k => center N k + Real.sqrt (1 - lambda N) *
        ((calibratedEstimator O m A).2 k - center N k))
      (fun N i j => if i = j then sliceVariance (Pseq N) (m i.1) / rate i.1 else 0)) ∧
  (∀ alpha ∈ allocations,
    let center := fun N k => exactSliceWelfare (Pseq N) m k.1
    let SigmaScreen := fun N (i j : ActiveIndex A) =>
      if i = j then sliceVariance (Pseq N) (m i.1) / (lambda N * alpha i.1) else 0
    let SigmaDecision := fun N (i j : ActiveIndex A) =>
      if i = j then sliceVariance (Pseq N) (m i.1) / ((1 - lambda N) * alpha i.1) else 0
    (∃ jointLaw : ∀ N, Measure ((Fin (screen N) → Record K n) ×
        (Fin (decision N) → Record K n)), ∀ N,
      IndependentScreenDecisionBlocks
        (crObservedLaw (C := screen N) (Pseq N) (counts alpha (screen N)) m)
        (crObservedLaw (C := decision N) (Pseq N) (counts alpha (decision N)) m)
        (jointLaw N)) ∧
    SequenceSqrtCBlockGaussianApproximation A screen
      (fun N => crObservedLaw (C := screen N) (Pseq N) (counts alpha (screen N)) m)
      center (fun _ O k => (calibratedEstimator O m A).2 k) SigmaScreen ∧
    SequenceSqrtCBlockGaussianApproximation A decision
      (fun N => crObservedLaw (C := decision N) (Pseq N) (counts alpha (decision N)) m)
      center (fun _ O k => (calibratedEstimator O m A).2 k) SigmaDecision ∧
    SequenceSqrtCBlockGaussianApproximation A decision
      (fun N => crObservedLaw (C := decision N) (Pseq N) (counts alpha (decision N)) m)
      center (fun N O k => center N k + Real.sqrt (1 - lambda N) *
        ((calibratedEstimator O m A).2 k - center N k))
      (fun N i j => if i = j then sliceVariance (Pseq N) (m i.1) / alpha i.1 else 0))

/-- Genuine finite covariance partitions for every retained non-singleton
face, including deterministic assignment on shared boundaries.  Singleton
faces bypass covariance certification and use the exact zero-risk rule. -/
def RetainedFaceCovariancePartitions [NeZero K] (A : Finset (Fin K))
    (cells : Finset (Fin K) → List RationalCell)
    (eigenLower eigenUpper : ℝ) : Prop :=
  0 < eigenLower ∧ eigenLower ≤ eigenUpper ∧
  ∀ S, 2 ≤ S.card → S ⊆ A → cells S ≠ [] ∧ (cells S).Nodup ∧
    1 < (cells S).length ∧ (∀ cell ∈ cells S, cell ≠ []) ∧
    CovarianceCellsHaveDisjointInteriors S (cells S) ∧
    DeterministicCovarianceCellAssignment S (cells S)
      (firstContainingCovarianceCell S (cells S)) ∧
    UniformlyEigenBoundedCovarianceCells S (cells S) eigenLower eigenUpper

/-- Canonical real evaluation of the program's computed finite output. -/
noncomputable def evaluatedSemanticOutput [NeZero K]
    (program : FiniteRationalHierarchicalProgram K) (S : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (v rate : Fin K → ℝ)
    (input : HierarchicalProgramInput K) : HierarchicalRoutineOutput S :=
  decodeHierarchicalProgramOutput S B v (program.run input)

/-- Program-level noncompact and outer-design certificate. -/
def UniformBoundaryProgramCertificate [NeZero K] (A : Finset (Fin K))
    (program : FiniteRationalHierarchicalProgram K) (B : Fin K → Fin K → ℝ)
    (v r : Fin K → ℝ) : Prop :=
  ((∃ k, ActionRelevantCoordinate A k ∧ r k = 0) → gaussianGlobalValue A v r = ⊤) ∧
  ((∀ k ∈ A, 0 < r k) → ∀ epsilon > 0,
    ∃ input : HierarchicalProgramInput K,
      let encoded := program.run input
      let semantic := evaluatedSemanticOutput program A B v r input
      0 < input.tolerance ∧ (input.tolerance : ℝ) ≤ epsilon ∧
      hierarchicalProgramRunCheck program input encoded = true ∧
      HierarchicalProgramSemanticEvaluation A B v r input encoded semantic ∧
      semantic.1.1 ≤ gaussianGlobalValue A v r ∧
      gaussianGlobalValue A v r ≤ ENNReal.ofReal
        (⨆ h : Fin K → ℝ, hierarchicalSplitRisk A v r h
          (encoded.splitFraction : ℝ) semantic.2.2.1) ∧
      ENNReal.ofReal (⨆ h : Fin K → ℝ, hierarchicalSplitRisk A v r h
        (encoded.splitFraction : ℝ) semantic.2.2.1) ≤ semantic.1.2 ∧
      semantic.1.2.toReal - semantic.1.1.toReal ≤ epsilon ∧
      CheckedOuterDesignTranscript A B v epsilon semantic.2.2.2.2)

/-- Triangular arrays are bounded schedule laws covered by the same finite
prespecified facewise covariance partitions on non-singleton retained faces.
Singleton faces have no quotient covariance and use the exact branch. -/
def UniformCertifiedTriangularScheduleArray [NeZero K]
    (Pseq : ℕ → Measure (Schedule n)) (m : Fin K → ℕ) (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (allocations : Set (Fin K → ℝ))
    (cells : Finset (Fin K) → List RationalCell) : Prop :=
  (∀ alpha ∈ allocations, InActiveSimplex A alpha) ∧
  ∀ N, WellFormedScheduleLaw (Pseq N) ∧
    ∀ S, 2 ≤ S.card → S ⊆ A →
      (∀ p, InSimplex p → ∃ cell ∈ cells S,
        CovarianceCellContains S (fun k => sliceVariance (Pseq N) (m k))
          (matVec B p) cell) ∧
      ∀ alpha ∈ allocations, ∃ cell ∈ cells S,
        CovarianceCellContains S (fun k => sliceVariance (Pseq N) (m k)) alpha cell

/-- Non-singleton true-parameter benchmark obtained by evaluating the same
finite program at the current triangular-array slice variance. -/
def TrueProgramEvaluation [NeZero K] (program : FiniteRationalHierarchicalProgram K)
    (S : Finset (Fin K)) (B : Fin K → Fin K → ℝ) (P : Measure (Schedule n))
    (m : Fin K → ℕ) (rate : Fin K → ℝ) (tolerance : ℚ)
    (expectedSplit : ℝ) (stage : ℕ)
    (cells : List RationalCell)
    (rateAssign : (Fin K → ℝ) → RationalCell) : Prop :=
  2 ≤ S.card ∧
    let trueV := fun k => sliceVariance P (m k)
    let input := hierarchicalProgramInput S
      (firstContainingCovarianceCell S cells trueV rate) (rateAssign rate) tolerance stage
    let encoded := program.run input
    hierarchicalProgramRunCheck program input encoded = true ∧
      encoded.stageIndex = stage ∧ (encoded.splitFraction : ℝ) = expectedSplit ∧
      HierarchicalProgramSemanticEvaluation S B trueV rate input encoded
        (evaluatedSemanticOutput program S B trueV rate input) ∧
      ∀ item ∈ (evaluatedSemanticOutput program S B trueV rate input).2.2.2.1,
        let M := (item.2.2.2.quotientRadius : ℝ)
        IsCompact (canonicalFaceRepresentatives item.1 M) ∧
          ExactQuotientBallRepresentativeCoverage item.1 M
            (canonicalFaceRepresentatives item.1 M)

/-- Non-singleton good-event evaluation at the pilot-computed outward snap.
Both covariance containment clauses refer to the deterministic selected cell. -/
def EmpiricalProgramEvaluation [NeZero K]
    (program : FiniteRationalHierarchicalProgram K) (S : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (P : Measure (Schedule n))
    (O : Fin C → Record K n) (m : Fin K → ℕ) (rate : Fin K → ℝ)
    (tolerance : ℚ) (expectedSplit : ℝ) (stage : ℕ)
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ)
    (cells : List RationalCell)
    (rateAssign : (Fin K → ℝ) → RationalCell) : Prop :=
  2 ≤ S.card ∧
    let snappedV := snappedVarianceFromPilot S O m rate snap
    let selectedCell := selectedCovarianceCell S O m rate snap cells
    let input := hierarchicalProgramInput S selectedCell (rateAssign rate) tolerance stage
    let encoded := program.run input
    hierarchicalProgramRunCheck program input encoded = true ∧
      encoded.stageIndex = stage ∧ (encoded.splitFraction : ℝ) = expectedSplit ∧
      HierarchicalProgramSemanticEvaluation S B snappedV rate input encoded
        (evaluatedSemanticOutput program S B snappedV rate input) ∧
      CovarianceCellContains S (fun k => sliceVariance P (m k)) rate selectedCell ∧
      CovarianceCellContains S snappedV rate selectedCell

/-- Pilot-selected selector.  Singleton faces use the canonical exact-zero
rule without inspecting a covariance cell.  On a non-singleton face the good
branch evaluates the finite program at the data-determined snap, while only
the bad branch uses the active-supported fallback. -/
noncomputable def empiricalProgramSelector [NeZero K]
    (program : FiniteRationalHierarchicalProgram K) (S : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (P : Measure (Schedule n))
    (O : Fin C → Record K n) (m : Fin K → ℕ) (rate : Fin K → ℝ)
    (tolerance : ℚ) (stage : ℕ)
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ)
    (cells : List RationalCell)
    (rateAssign : (Fin K → ℝ) → RationalCell)
    (fallback : (ActiveIndex S → ℝ) → Fin K → ℝ)
    (screen decision : ActiveIndex S → ℝ) : Fin K → ℝ :=
  if S.card = 1 then singletonActiveSelector S decision else
    if PilotCovarianceGoodEvent S P O m rate snap cells then
      let snappedV := snappedVarianceFromPilot S O m rate snap
      let cell := selectedCovarianceCell S O m rate snap cells
      let input := hierarchicalProgramInput S cell (rateAssign rate) tolerance stage
      (evaluatedSemanticOutput program S B snappedV rate input).2.2.1 screen decision
    else fallback decision

/-- Per-action joint measurability of the empirical selector in pilot,
screening, and decision inputs.  The rate is fixed by each Bernoulli or CR
clause; no supremum ranges over pilot realizations. -/
def JointlyMeasurableEmpiricalProgramSelector {C : ℕ} [NeZero K]
    (program : FiniteRationalHierarchicalProgram K) (S : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (P : Measure (Schedule n))
    (m : Fin K → ℕ) (rate : Fin K → ℝ) (tolerance : ℚ) (stage : ℕ)
    (snap : (Fin K → Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ)
    (cells : List RationalCell) (rateAssign : (Fin K → ℝ) → RationalCell)
    (fallback : (ActiveIndex S → ℝ) → Fin K → ℝ) : Prop :=
  ∀ a, Measurable fun input :
      (Fin C → Record K n) × (ActiveIndex S → ℝ) × (ActiveIndex S → ℝ) =>
    empiricalProgramSelector program S B P input.1 m rate tolerance stage snap cells
      rateAssign fallback input.2.1 input.2.2 a

/-- True benchmark for one triangular slice.  A singleton has exact upper
value zero; a non-singleton is evaluated by the same finite program at
`sliceVariance P`, with deterministic boundary assignment of its covariance
cell. -/
noncomputable def trueProgramUpper [NeZero K]
    (program : FiniteRationalHierarchicalProgram K) (S : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) (P : Measure (Schedule n)) (m : Fin K → ℕ)
    (rate : Fin K → ℝ) (tolerance : ℚ) (stage : ℕ)
    (cells : List RationalCell)
    (rateAssign : (Fin K → ℝ) → RationalCell) : ℝ :=
  if S.card = 1 then 0 else
    let trueV := fun k => sliceVariance P (m k)
    let input := hierarchicalProgramInput S
      (firstContainingCovarianceCell S cells trueV rate) (rateAssign rate) tolerance stage
    ((program.run input).upperBound : ℝ)

/-- Sequence-indexed unconditional transfer.  True benchmarks occur only
inside the `Pseq` binder and are evaluations of the same finite program.
Every empirical snap is the displayed measurable function of pilot data. -/
def TriangularArrayUniformTransfer {n : ℕ} [NeZero K]
    (A : Finset (Fin K)) (program : FiniteRationalHierarchicalProgram K)
    (B : Fin K → Fin K → ℝ) (allocations : Set (Fin K → ℝ))
    (counts : (Fin K → ℝ) → ℕ → Fin K → ℕ) (m : Fin K → ℕ)
    (cells : Finset (Fin K) → List RationalCell) : Prop :=
  (∀ alpha ∈ allocations, InActiveSimplex A alpha) ∧
  (∀ alpha ∈ allocations, ∀ N, ∑ k, counts alpha N k = N) ∧
  (∀ alpha ∈ allocations, ∀ N k, k ∉ A → counts alpha N k = 0) ∧
  ∃ epsilon : ℕ → ℚ, (∀ N, 0 < epsilon N) ∧
    Tendsto (fun N => (epsilon N : ℝ)) atTop (nhds 0) ∧
  ∃ fixedLambda : ℝ, fixedLambda ∈ Ioo (0 : ℝ) 1 ∧
  ∃ lambda : ℕ → ℝ, (∀ N, lambda N ∈ Ioo (0 : ℝ) 1) ∧
    Tendsto lambda atTop (nhds fixedLambda) ∧
  ∃ pilot screen decision : ℕ → ℕ,
    IsStageIndexedThreeWaySplit pilot screen decision lambda ∧
  ∃ eigenLower eigenUpper : ℝ,
    RetainedFaceCovariancePartitions A cells eigenLower eigenUpper ∧
  ∃ rateCells : Finset (Fin K) → List RationalCell,
  ∃ rateAssign : ∀ S : Finset (Fin K), (Fin K → ℝ) → RationalCell,
    (∀ S, 2 ≤ S.card → S ⊆ A → GenuineRatePartition K (rateCells S) ∧
      DeterministicRateCellAssignment (rateCells S) (rateAssign S)) ∧
  ∃ fallback : ∀ S : Finset (Fin K), (ActiveIndex S → ℝ) → Fin K → ℝ,
  ∀ Pseq : ℕ → Measure (Schedule n),
    UniformCertifiedTriangularScheduleArray Pseq m A B allocations cells →
    SequenceIndexedThreeWayGaussianClause Pseq A B allocations counts m fixedLambda lambda
      screen decision ∧
    (∀ S, S.Nonempty → S ⊆ A → GaussianSelector S (fallback S)) ∧
    (∀ S N (p : {p : Fin K → ℝ // InSimplex p}), S.card = 1 → S ⊆ A →
      ExactZeroSingletonBranch S (fun k => sliceVariance (Pseq N) (m k))
        (matVec B p.1)) ∧
    (∀ S N (alpha : {a : Fin K → ℝ // a ∈ allocations}), S.card = 1 → S ⊆ A →
      ExactZeroSingletonBranch S (fun k => sliceVariance (Pseq N) (m k)) alpha.1) ∧
    (∀ S N (rate : Fin K → ℝ), 2 ≤ S.card → S ⊆ A →
      MeasurableSet {O : Fin (pilot N) → Record K n |
        PilotCovarianceGoodEvent S (Pseq N) O m rate deterministicPilotOutwardSnap
          (cells S)}) ∧
    Tendsto (fun N => sSup {prob : ℝ | ∃ S : Finset (Fin K),
      2 ≤ S.card ∧ S ⊆ A ∧ ∃ p : {p : Fin K → ℝ // InSimplex p},
      prob = ((Measure.pi fun _ : Fin (pilot N) => bernoulliObservedLaw (Pseq N) p.1 m)
        {O | ¬ PilotCovarianceGoodEvent S (Pseq N) O m (matVec B p.1)
          deterministicPilotOutwardSnap
          (cells S)}).toReal}) atTop (nhds 0) ∧
    Tendsto (fun N => sSup {prob : ℝ | ∃ S : Finset (Fin K),
      2 ≤ S.card ∧ S ⊆ A ∧ ∃ alpha : {a : Fin K → ℝ // a ∈ allocations},
      prob = (crObservedLaw (C := pilot N) (Pseq N) (counts alpha.1 (pilot N)) m
        {O | ¬ PilotCovarianceGoodEvent S (Pseq N) O m alpha.1
          deterministicPilotOutwardSnap
          (cells S)}).toReal}) atTop (nhds 0) ∧
    (∀ S N (p : {p : Fin K → ℝ // InSimplex p}), 2 ≤ S.card → S ⊆ A →
      TrueProgramEvaluation program S B (Pseq N) m (matVec B p.1) (epsilon N) (lambda N)
        (N + 1)
        (cells S) (rateAssign S)) ∧
    (∀ S N (alpha : {a : Fin K → ℝ // a ∈ allocations}), 2 ≤ S.card → S ⊆ A →
      TrueProgramEvaluation program S B (Pseq N) m alpha.1 (epsilon N) (lambda N) (N + 1)
        (cells S) (rateAssign S)) ∧
    (∀ S N (O : Fin (pilot N) → Record K n)
      (p : {p : Fin K → ℝ // InSimplex p}), 2 ≤ S.card → S ⊆ A →
      PilotCovarianceGoodEvent S (Pseq N) O m (matVec B p.1)
        deterministicPilotOutwardSnap (cells S) →
      EmpiricalProgramEvaluation program S B (Pseq N) O m (matVec B p.1)
        (epsilon N) (lambda N) (N + 1) deterministicPilotOutwardSnap (cells S)
          (rateAssign S)) ∧
    (∀ S N (O : Fin (pilot N) → Record K n)
      (alpha : {a : Fin K → ℝ // a ∈ allocations}), 2 ≤ S.card → S ⊆ A →
      PilotCovarianceGoodEvent S (Pseq N) O m alpha.1 deterministicPilotOutwardSnap
        (cells S) →
      EmpiricalProgramEvaluation program S B (Pseq N) O m alpha.1
        (epsilon N) (lambda N) (N + 1) deterministicPilotOutwardSnap (cells S)
          (rateAssign S)) ∧
    (∀ S N (p : {p : Fin K → ℝ // InSimplex p}), S.Nonempty → S ⊆ A →
      JointlyMeasurableEmpiricalProgramSelector (C := pilot N) program S B (Pseq N) m
        (matVec B p.1) (epsilon N) (N + 1) deterministicPilotOutwardSnap (cells S)
          (rateAssign S) (fallback S)) ∧
    (∀ S N (alpha : {a : Fin K → ℝ // a ∈ allocations}), S.Nonempty → S ⊆ A →
      JointlyMeasurableEmpiricalProgramSelector (C := pilot N) program S B (Pseq N) m
        alpha.1 (epsilon N) (N + 1) deterministicPilotOutwardSnap (cells S)
          (rateAssign S) (fallback S)) ∧
    (∀ S, 2 ≤ S.card → S ⊆ A → ∀ M ≥ 0,
      IsCompact (canonicalFaceRepresentatives S M) ∧
        ExactQuotientBallRepresentativeCoverage S M
          (canonicalFaceRepresentatives S M)) ∧
    (∀ S, S.Nonempty → S ⊆ A → ∀ M ≥ 0,
      ∃ scaledRegretBound ≥ 0, ∀ (N : ℕ) h (x : ActiveIndex S → ℝ),
        h ∈ canonicalFaceRepresentatives S M →
        Real.sqrt N * |∑ a, fallback S x a * simpleRegret S
          (exactSliceWelfare (leastFavourablePath (Pseq N) A m h (Real.sqrt N)⁻¹) m) a| ≤
          scaledRegretBound) ∧
    Filter.limsup (fun (N : ℕ) => sSup {gap : ℝ |
      ∃ p : {p : Fin K → ℝ // InSimplex p}, ∃ h : Fin K → ℝ,
      gap = Real.sqrt N * bernoulliThreeWayPrimitiveRisk
        (leastFavourablePath (Pseq N) A m h (Real.sqrt N)⁻¹) p.1 m A (lambda N)
        (pilot N) (screen N) (decision N)
        (empiricalProgramSelector program A B (Pseq N) · m (matVec B p.1)
          (epsilon N) (N + 1) deterministicPilotOutwardSnap (cells A)
            (rateAssign A) (fallback A)) -
        trueProgramUpper program A B (Pseq N) m (matVec B p.1) (epsilon N) (N + 1)
          (cells A) (rateAssign A)}) atTop ≤ 0 ∧
    Filter.limsup (fun (N : ℕ) => sSup {gap : ℝ |
      ∃ alpha : {a : Fin K → ℝ // a ∈ allocations}, ∃ h : Fin K → ℝ,
      gap = Real.sqrt N * crThreeWayPrimitiveRisk
        (leastFavourablePath (Pseq N) A m h (Real.sqrt N)⁻¹)
        (counts alpha.1 (pilot N)) (counts alpha.1 (screen N))
        (counts alpha.1 (decision N)) m A (lambda N) (pilot N) (screen N) (decision N)
        (empiricalProgramSelector program A B (Pseq N) · m alpha.1
          (epsilon N) (N + 1) deterministicPilotOutwardSnap (cells A)
            (rateAssign A) (fallback A)) -
        trueProgramUpper program A B (Pseq N) m alpha.1 (epsilon N) (N + 1)
          (cells A) (rateAssign A)}) atTop ≤ 0 ∧
    (∀ fixedGap > 0,
      Tendsto (fun (N : ℕ) => sSup {contribution : ℝ |
        ∃ p : {p : Fin K → ℝ // InSimplex p},
        contribution = Real.sqrt N * bernoulliFixedGapInferiorContribution
          (Pseq N) p.1 m A (lambda N) fixedGap (pilot N) (screen N) (decision N)
          (empiricalProgramSelector program A B (Pseq N) · m (matVec B p.1)
            (epsilon N) (N + 1) deterministicPilotOutwardSnap (cells A)
              (rateAssign A) (fallback A))}) atTop (nhds 0) ∧
      Tendsto (fun (N : ℕ) => sSup {contribution : ℝ |
        ∃ alpha : {a : Fin K → ℝ // a ∈ allocations},
        contribution = Real.sqrt N * crFixedGapInferiorContribution
          (Pseq N) (counts alpha.1 (pilot N)) (counts alpha.1 (screen N))
          (counts alpha.1 (decision N)) m A (lambda N) fixedGap
          (pilot N) (screen N) (decision N)
          (empiricalProgramSelector program A B (Pseq N) · m alpha.1
            (epsilon N) (N + 1) deterministicPilotOutwardSnap (cells A)
              (rateAssign A) (fallback A))}) atTop (nhds 0))

/-- Contract for the supplied root partitions in the displayed face. -/
def CertifiedCovarianceCellContract [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (varianceCells rateCells covarianceCells : List RationalCell) : Prop :=
  GenuineRatePartition K varianceCells ∧ GenuineRatePartition K rateCells ∧
  (∃ cell ∈ varianceCells, InRationalCell v cell) ∧
  (∃ cell ∈ rateCells, InRationalCell r cell) ∧
  covarianceCells.Nodup ∧ 1 < covarianceCells.length ∧
  (∀ cell ∈ covarianceCells, cell ≠ []) ∧
  CovarianceCellsHaveDisjointInteriors A covarianceCells ∧
  (∃ cell ∈ covarianceCells, CovarianceCellContains A v r cell) ∧
  CovariancePartitionCoversRates A v rateCells covarianceCells ∧
  (∃ rateAssignment : (Fin K → ℝ) → RationalCell,
    DeterministicRateCellAssignment rateCells rateAssignment) ∧
  DeterministicCovarianceCellAssignment A covarianceCells
    (firstContainingCovarianceCell A covarianceCells) ∧
  ∃ eigenLower eigenUpper : ℝ, 0 < eigenLower ∧ eigenLower ≤ eigenUpper ∧
    UniformlyEigenBoundedCovarianceCells A covarianceCells eigenLower eigenUpper

-- @node: thm:uniform-boundary-certificate
/-- The finite rational program gives the noncompact Gaussian and outer-design
certificates and transfers them through empirical three-way splits for every
covered triangular schedule array. -/
theorem uniform_boundary_certificate {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (allocations : Set (Fin K → ℝ))
    (bernoulliLabelLaw : (Fin K → ℝ) → Measure (Fin C → Fin K))
    (bernoulliJointLaw : (Fin K → ℝ) → Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (crLabelLaw : (Fin K → ℝ) → Measure (Fin C → Fin K))
    (crJointLaw : (Fin K → ℝ) → Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (bernoulliAssignmentLaw crAssignmentLaw : AssignmentKernel C K n)
    (p : Fin K → ℝ) (counts : (Fin K → ℝ) → ℕ → Fin K → ℕ)
    (alpha v r : Fin K → ℝ) (mNat : Fin K → ℕ)
    (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ) (tauLower : ℝ)
    (certifiedVarianceCells certifiedRateCells certifiedCovarianceCells : List RationalCell)
    (h_iid : IidSchedules P0 sampleLaw) (h_isolated : IsolatedClusters sampleLaw)
    (h_bernoulli_labels : ∀ p, InSimplex p → BernoulliLabelIid p (bernoulliLabelLaw p))
    (h_bernoulli_indep : ∀ p, InSimplex p →
      BernoulliLabelScheduleIndep sampleLaw (bernoulliLabelLaw p) (bernoulliJointLaw p))
    (h_bernoulli_units : ∀ p, InSimplex p →
      BernoulliUnits mNat P0 (bernoulliLabelLaw p) bernoulliAssignmentLaw)
    (h_allocations : IsCompact allocations ∧ allocations.Nonempty ∧
      ∀ alpha ∈ allocations, InActiveSimplex A alpha)
    (h_cr_labels : ∀ alpha ∈ allocations, CrLabelVector (counts alpha C) (crLabelLaw alpha))
    (h_cr_indep : ∀ alpha ∈ allocations,
      CrLabelScheduleIndep sampleLaw (crLabelLaw alpha) (crJointLaw alpha))
    (h_cr_shares : ∀ alpha ∈ allocations, CrActiveShares (counts alpha) alpha A)
    (h_cr_slices : ∀ alpha ∈ allocations,
      CrExactSlices mNat P0 (crLabelLaw alpha) crAssignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 mNat A tauLower)
    (hmenu : WellFormedMenu n K mNat) (hp : InSimplex p)
    (hcounts : (∀ alpha ∈ allocations, ∀ N, ∑ k, counts alpha N k = N) ∧
      ∀ alpha ∈ allocations, ∀ N k, k ∉ A → counts alpha N k = 0)
    (hB : B = (hitMatrix n mNat p).1)
    (hA : 2 ≤ A.card) (hv : ∀ k ∈ A, 0 < v k) (hr : ∀ k ∈ A, 0 ≤ r k)
    (hargmax : ∀ k, k ∈ A ↔ ∀ j, exactSliceWelfare P0 mNat j ≤ exactSliceWelfare P0 mNat k)
    (hcertifiedCells : CertifiedCovarianceCellContract A v r certifiedVarianceCells
      certifiedRateCells certifiedCovarianceCells)
    (hrateCoverage :
      (∀ p, InSimplex p → ∃ cell ∈ certifiedRateCells, InRationalCell (matVec B p) cell) ∧
      ∀ alpha ∈ allocations, ∃ cell ∈ certifiedRateCells, InRationalCell alpha cell) :
    ∃ program : FiniteRationalHierarchicalProgram K,
      FiniteHierarchicalProgramOperational program ∧
      ∃ faceCovarianceCells : Finset (Fin K) → List RationalCell,
        faceCovarianceCells A = certifiedCovarianceCells ∧
        UniformBoundaryProgramCertificate A program B v r ∧
        TriangularArrayUniformTransfer (n := n) A program B allocations counts mNat
          faceCovarianceCells := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
