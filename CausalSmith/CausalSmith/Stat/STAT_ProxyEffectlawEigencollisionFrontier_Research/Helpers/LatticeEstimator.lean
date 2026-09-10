import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SummaryClosure
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.RepresentativeSpectralCertificate
import Mathlib.Analysis.Matrix.Order

/-! Finite-library and no-advice lattice estimator carriers. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set
open scoped MatrixOrder

/-- Polynomial aggregate spectral projectors and the positive law they determine at one feasible
representative.  The law is not supplied independently: its atoms and masses are definitionally
the displayed projector formula. -/
structure RepresentativeSpectralData (k dx dz : ℕ) (radius threshold : ℝ)
    (s : SummarySpace dx dz) where
  basis : SignalBasis dx k
  spans : basis.SpansSignal s
  armwiseFullRank : ∀ t : Bool, Function.Injective (Matrix.toEuclideanLin
    (observedProxyMoment s t * basis.V))
  thresholdRetainsExactlySignal : ∀ j,
    threshold ≤ singularValue (stackedProxyMoment s) j ↔ j < k
  eigenvalue : Fin k → ℝ
  eigenvalue_complete : ∀ z : ℂ, MatrixEigenvalue
      (compressedOperator s basis spans) z → ∃ i, z = eigenvalue i
  lawValid : AtomicLaw.Valid
    (⟨fun i => ∑ a, leftAnchor s basis a *
        (∑ b, (polynomialAggregateProjector
          (compressedOperator s basis spans) eigenvalue i) a b *
          rightAnchor basis b), eigenvalue⟩ : AtomicLaw k radius)

noncomputable def RepresentativeSpectralData.effectLaw {k dx dz : ℕ} {radius threshold : ℝ}
    {s : SummarySpace dx dz} (D : RepresentativeSpectralData k dx dz radius threshold s) :
    AtomicLaw.LawModulo k radius :=
  AtomicLaw.LawModulo.ofProbabilityLaw
    ⟨⟨fun i => ∑ a, leftAnchor s D.basis a *
        (∑ b, (polynomialAggregateProjector
          (compressedOperator s D.basis D.spans) D.eigenvalue i) a b *
          rightAnchor D.basis b), D.eigenvalue⟩, D.lawValid⟩

/-- Coordinatewise membership in one deterministic half-open summary cube. -/
def InSummaryBox {dx dz : ℕ} (L : ℝ) (s : SummarySpace dx dz) : Prop :=
  (∀ i j, s.M0 i j ∈ Set.Icc (-L) L) ∧
  (∀ i j, s.M1 i j ∈ Set.Icc (-L) L) ∧
  (∀ i j, s.N0 i j ∈ Set.Icc (-L) L) ∧
  (∀ i j, s.N1 i j ∈ Set.Icc (-L) L) ∧
  ∀ i, s.mX i ∈ Set.Icc (-L) L

def InHalfOpenSummaryCube {dx dz : ℕ} (scale : ℝ) (lo s : SummarySpace dx dz) : Prop :=
  (∀ i j, lo.M0 i j ≤ s.M0 i j ∧ s.M0 i j < lo.M0 i j + scale) ∧
  (∀ i j, lo.M1 i j ≤ s.M1 i j ∧ s.M1 i j < lo.M1 i j + scale) ∧
  (∀ i j, lo.N0 i j ≤ s.N0 i j ∧ s.N0 i j < lo.N0 i j + scale) ∧
  (∀ i j, lo.N1 i j ≤ s.N1 i j ∧ s.N1 i j < lo.N1 i j + scale) ∧
  ∀ i, lo.mX i ≤ s.mX i ∧ s.mX i < lo.mX i + scale

noncomputable def summaryLexKey {dx dz : ℕ} (s : SummarySpace dx dz) : List ℝ :=
  ((Finset.univ.toList.flatMap fun i : Fin dz =>
      Finset.univ.toList.map fun j : Fin dx => s.M0 i j) ++
   (Finset.univ.toList.flatMap fun i : Fin dz =>
      Finset.univ.toList.map fun j : Fin dx => s.M1 i j) ++
   (Finset.univ.toList.flatMap fun i : Fin dz =>
      Finset.univ.toList.map fun j : Fin dx => s.N0 i j) ++
   (Finset.univ.toList.flatMap fun i : Fin dz =>
      Finset.univ.toList.map fun j : Fin dx => s.N1 i j) ++
   Finset.univ.toList.map fun i : Fin dx => s.mX i)

def SummaryLexLE {dx dz : ℕ} (s q : SummarySpace dx dz) : Prop :=
  summaryLexKey s = summaryLexKey q ∨ List.Lex (· < ·) (summaryLexKey s) (summaryLexKey q)

/-- A faithfully well-formed class-dependent grid library of feasible representatives. -/
structure NetLibrary (k dx dz n : ℕ) (L pi0 sigma0 : ℝ) where
  index : Type
  finiteIndex : Fintype index
  summary : index → SummarySpace dx dz
  representative_feasible : ∀ i, summary i ∈ admissibleImage k dx dz L pi0 sigma0
  scale : ℝ
  scale_eq : scale = (Real.sqrt n)⁻¹ /
    (4 * Real.sqrt (dz * dx) + Real.sqrt dx)
  covers : ∀ q, q ∈ admissibleImage k dx dz L pi0 sigma0 →
    ∃ i, dS (summary i) q ≤ (Real.sqrt n)⁻¹
  cube : index → Set (SummarySpace dx dz)
  cubeLower : index → SummarySpace dx dz
  cubeLower_on_grid : ∀ i,
    (∀ a b, ∃ z : ℤ, (cubeLower i).M0 a b = -L + scale * z) ∧
    (∀ a b, ∃ z : ℤ, (cubeLower i).M1 a b = -L + scale * z) ∧
    (∀ a b, ∃ z : ℤ, (cubeLower i).N0 a b = -L + scale * z) ∧
    (∀ a b, ∃ z : ℤ, (cubeLower i).N1 a b = -L + scale * z) ∧
    ∀ a, ∃ z : ℤ, (cubeLower i).mX a = -L + scale * z
  cube_eq_halfOpen : ∀ i, cube i =
    {s | InSummaryBox L s ∧ InHalfOpenSummaryCube scale (cubeLower i) s}
  representative_in_cube : ∀ i, summary i ∈ cube i
  cubes_disjoint : Set.PairwiseDisjoint Set.univ cube
  meeting_cube_complete : ∀ q, q ∈ admissibleImage k dx dz L pi0 sigma0 →
    ∃ i, q ∈ cube i
  cube_diameter : ∀ i q, q ∈ cube i → dS q (summary i) ≤ (Real.sqrt n)⁻¹
  lexRank : index → ℕ
  lexRank_injective : Function.Injective lexRank
  lexRank_order : ∀ i j, lexRank i ≤ lexRank j ↔ SummaryLexLE (cubeLower i) (cubeLower j)
  k_pos : 0 < k
  radius_nonneg : 0 ≤ effectRadius dz L sigma0
  index_nonempty_iff : Nonempty index ↔ admissibleImage k dx dz L pi0 sigma0 ≠ ∅

local instance {k dx dz n L pi0 sigma0} (A : NetLibrary k dx dz n L pi0 sigma0) :
    Fintype A.index := A.finiteIndex

/-- The actual finite list scanned by the advised estimator. -/
noncomputable def NetLibrary.indexList {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) : List A.index :=
  (Finset.univ : Finset A.index).toList

/-- One exact-real comparison step: keep the closer representative, breaking distance ties by
the prescribed lexicographic rank. -/
noncomputable def NetLibrary.betterIndex {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz)
    (i j : A.index) : A.index :=
  if dS (A.summary j) s < dS (A.summary i) s then j
  else if dS (A.summary i) s < dS (A.summary j) s then i
  else if A.lexRank j < A.lexRank i then j else i

/-- Exhaustive smallest-index nearest-library search, implemented by a fold over the actual finite
library rather than supplied as an oracle field. -/
noncomputable def nearestLibraryIndex {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz) : Option A.index :=
  match A.indexList with
  | [] => none
  | i :: is => some (is.foldl (A.betterIndex s) i)

private def NetLibrary.Dominates {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz)
    (i j : A.index) : Prop :=
  dS (A.summary i) s ≤ dS (A.summary j) s ∧
    (dS (A.summary i) s = dS (A.summary j) s → A.lexRank i ≤ A.lexRank j)

private lemma NetLibrary.dominates_refl
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz) (i : A.index) :
    A.Dominates s i i := ⟨le_rfl, fun _ => le_rfl⟩

private lemma NetLibrary.dominates_trans
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz)
    {i j l : A.index} (hij : A.Dominates s i j) (hjl : A.Dominates s j l) :
    A.Dominates s i l := by
  refine ⟨hij.1.trans hjl.1, ?_⟩
  intro hil
  have hijEq : dS (A.summary i) s = dS (A.summary j) s :=
    le_antisymm hij.1 (hil ▸ hjl.1)
  have hjlEq : dS (A.summary j) s = dS (A.summary l) s := hijEq.symm.trans hil
  exact (hij.2 hijEq).trans (hjl.2 hjlEq)

private lemma NetLibrary.betterIndex_dominates
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz)
    (i j : A.index) :
    A.Dominates s (A.betterIndex s i j) i ∧
      A.Dominates s (A.betterIndex s i j) j := by
  unfold betterIndex Dominates
  by_cases hji : dS (A.summary j) s < dS (A.summary i) s
  · rw [if_pos hji]
    exact ⟨⟨hji.le, fun h => False.elim (ne_of_lt hji h)⟩,
      ⟨le_rfl, fun _ => le_rfl⟩⟩
  · have hij : dS (A.summary i) s ≤ dS (A.summary j) s := le_of_not_gt hji
    by_cases hij' : dS (A.summary i) s < dS (A.summary j) s
    · rw [if_neg hji, if_pos hij']
      exact ⟨⟨le_rfl, fun _ => le_rfl⟩,
        ⟨hij'.le, fun h => False.elim (ne_of_lt hij' h)⟩⟩
    · have heq : dS (A.summary i) s = dS (A.summary j) s :=
        le_antisymm hij (le_of_not_gt hij')
      by_cases hr : A.lexRank j < A.lexRank i
      · simp [hji, hij', hr, heq, hr.le]
      · have hir : A.lexRank i ≤ A.lexRank j := le_of_not_gt hr
        simp [hji, hij', hr, heq, hir]

private lemma NetLibrary.foldl_betterIndex_dominates
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz)
    (i : A.index) (is : List A.index) :
    ∀ j ∈ i :: is, A.Dominates s (is.foldl (A.betterIndex s) i) j := by
  induction is generalizing i with
  | nil =>
      intro j hj
      simp only [List.foldl_nil, List.mem_singleton] at hj
      subst j
      exact A.dominates_refl s i
  | cons a as ih =>
      intro j hj
      have hpair := A.betterIndex_dominates s i a
      have htail := ih (A.betterIndex s i a)
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hj with rfl | hj
      · exact A.dominates_trans s (htail _ (by simp)) hpair.1
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact A.dominates_trans s (htail _ (by simp)) hpair.2
        · exact htail j (by simp [hj])

/-- Successful exhaustive fold selection minimizes distance over the whole library and uses the
stored lexicographic rank to break every distance tie. -/
lemma nearestLibraryIndex_spec
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (s : SummarySpace dx dz)
    (i : A.index) (hsel : nearestLibraryIndex A s = some i) :
    (∀ j, dS (A.summary i) s ≤ dS (A.summary j) s) ∧
      ∀ j, dS (A.summary i) s = dS (A.summary j) s → A.lexRank i ≤ A.lexRank j := by
  unfold nearestLibraryIndex at hsel
  generalize hlist : A.indexList = xs at hsel
  cases xs with
  | nil => simp at hsel
  | cons a as =>
      simp only at hsel
      have hi : as.foldl (A.betterIndex s) a = i := Option.some.inj hsel
      subst i
      have hall := A.foldl_betterIndex_dominates s a as
      constructor
      · intro j
        exact (hall j (by
          rw [← hlist]
          simp [NetLibrary.indexList])).1
      · intro j hj
        exact (hall j (by
          rw [← hlist]
          simp [NetLibrary.indexList])).2 hj

-- keep: reusable feasibility-to-spectral-certificate bridge for alternate finite-net estimators
/-- Feasibility of a raw advised summary implies all spectral facts needed by the stored-summary
rule.  In particular, these are conclusions of the model assumptions, not certificates bundled
into the advice. -/
lemma representativeSpectralData_exists {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (s : SummarySpace dx dz) (hs : s ∈ admissibleImage k dx dz L pi0 sigma0) :
    Nonempty (RepresentativeSpectralData k dx dz (effectRadius dz L sigma0)
      (pi0 * sigma0 ^ 2 / 2) s) := by
  classical
  rcases hs with ⟨Q, hQs⟩
  subst s
  letI := Q.prob
  obtain ⟨facts⟩ := modelCompressedSpectralFacts_exists Q
  have hradius : 0 < effectRadius dz L sigma0 := by
    rcases Q.model.coreDomain with ⟨hk, _, hkz, hL, _, _, hsigma, _⟩
    have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
    unfold effectRadius
    positivity
  have hlatent := quotientLawRaw_valid Q.P Q.model
  have hmass : (∀ u, 0 ≤ latentMass Q.P u) ∧ ∑ u, latentMass Q.P u = 1 :=
    ⟨hlatent.1, hlatent.2.1⟩
  have hbound (u : Fin k) : facts.diagonalization.eigenvalue u ∈
      Set.Icc (-effectRadius dz L sigma0) (effectRadius dz L sigma0) := by
    rw [facts.eigenvalue_coordinates]
    exact hlatent.2.2 u
  obtain ⟨value, hinj, hcomplete, hvalueBound, hweightNonneg, hweightSum⟩ :=
    CausalSmith.Substrate.CollisionSafeSpectralLaw.exists_polynomialSpectralLaw
      facts.diagonalization hradius (latentMass Q.P)
        (leftAnchor Q.summary facts.basis) (rightAnchor facts.basis)
        hmass hbound facts.left_coordinates facts.right_coordinates
  refine ⟨{
    basis := facts.basis
    spans := facts.spans
    armwiseFullRank := facts.armwiseFullRank
    thresholdRetainsExactlySignal := facts.thresholdRetainsExactlySignal
    eigenvalue := value
    eigenvalue_complete := ?_
    lawValid := ?_ }⟩
  · intro z hz
    have hz' : CausalSmith.Substrate.CollisionSafeSpectralLaw.ComplexMatrixEigenvalue
        (compressedOperator Q.summary facts.basis facts.spans) z := hz
    obtain ⟨u, hu⟩ :=
      CausalSmith.Substrate.CollisionSafeSpectralLaw.complexEigenvalue_mem_diagonal
        facts.diagonalization hz'
    obtain ⟨i, hi⟩ := hcomplete u
    exact ⟨i, hu.trans (congrArg ((↑) : ℝ → ℂ) hi.symm)⟩
  · refine ⟨?_, ?_, hvalueBound⟩
    · intro i
      simpa [polynomialAggregateProjector,
        CausalSmith.Substrate.CollisionSafeSpectralLaw.polynomialSpectralProjector] using
          hweightNonneg i
    · simpa [polynomialAggregateProjector,
        CausalSmith.Substrate.CollisionSafeSpectralLaw.polynomialSpectralProjector] using
          hweightSum

/-- The operation classes charged by the paper's fixed-dimensional exact-real model. -/
structure NetOperationCount where
  arithmetic : ℕ
  comparison : ℕ
  singularValue : ℕ
  rootIsolation : ℕ

def NetOperationCount.total (cost : NetOperationCount) : ℕ :=
  cost.arithmetic + cost.comparison + cost.singularValue + cost.rootIsolation

/-- Primitive instructions in the fixed-dimensional exact-real implementation. -/
inductive NetPrimitiveOperation where
  | arithmetic
  | comparison
  | singularValue
  | rootIsolation
  deriving DecidableEq

def NetPrimitiveOperation.cost : NetPrimitiveOperation → NetOperationCount
  | .arithmetic => ⟨1, 0, 0, 0⟩
  | .comparison => ⟨0, 1, 0, 0⟩
  | .singularValue => ⟨0, 0, 1, 0⟩
  | .rootIsolation => ⟨0, 0, 0, 1⟩

def NetOperationCount.add (a b : NetOperationCount) : NetOperationCount :=
  ⟨a.arithmetic + b.arithmetic, a.comparison + b.comparison,
    a.singularValue + b.singularValue, a.rootIsolation + b.rootIsolation⟩

def netTraceCost (trace : List NetPrimitiveOperation) : NetOperationCount :=
  trace.foldl (fun cost op => cost.add op.cost) ⟨0, 0, 0, 0⟩

/-- Result returned by the singular-value primitive at one feasible representative.  Its basis,
rank certificates, and threshold decision are the data produced by this execution, not separately
supplied advice. -/
structure ThresholdedSignalExecution {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (s : SummarySpace dx dz) where
  basis : SignalBasis dx k
  spans : basis.SpansSignal s
  armwiseFullRank : ∀ t : Bool, Function.Injective (Matrix.toEuclideanLin
    (observedProxyMoment s t * basis.V))
  thresholdRetainsExactlySignal : ∀ j,
    pi0 * sigma0 ^ 2 / 2 ≤ singularValue (stackedProxyMoment s) j ↔ j < k
  trace : List NetPrimitiveOperation
  trace_eq : trace = List.replicate 3 .singularValue

/-- Result returned by fixed-degree real-root isolation and projector-mass arithmetic after the
singular-value execution.  The validity certificate concerns exactly the atoms and projector
masses returned by this execution. -/
structure RootIsolationMassExecution {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (s : SummarySpace dx dz) (signal : ThresholdedSignalExecution
      (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s) where
  eigenvalue : Fin k → ℝ
  eigenvalue_complete : ∀ z : ℂ, MatrixEigenvalue
      (compressedOperator s signal.basis signal.spans) z → ∃ i, z = eigenvalue i
  lawValid : AtomicLaw.Valid
    (⟨fun i => ∑ a, leftAnchor s signal.basis a *
        (∑ b, (polynomialAggregateProjector
          (compressedOperator s signal.basis signal.spans) eigenvalue i) a b *
          rightAnchor signal.basis b), eigenvalue⟩ :
      AtomicLaw k (effectRadius dz L sigma0))
  trace : List NetPrimitiveOperation
  trace_eq : trace = [.rootIsolation, .arithmetic]

/-- One execution of the result-bearing singular-value and root-isolation primitives. -/
structure ExactRealSpectralRun {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (s : SummarySpace dx dz) where
  signal : ThresholdedSignalExecution
    (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s
  roots : RootIsolationMassExecution (s := s) (L := L) signal

/-- Exact-real primitives at fixed admissible dimensions and constants.  The combined primitive
threads feasibility into both singular-value thresholding and root isolation, so no root run can
be requested at an arbitrary summary. -/
structure ExactRealPrimitivesAt (k dx dz : ℕ) (L pi0 sigma0 : ℝ) where
  spectralRun : (s : SummarySpace dx dz) →
    s ∈ admissibleImage k dx dz L pi0 sigma0 →
      ExactRealSpectralRun (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s

/-- A uniform provider of fixed-parameter exact-real primitives, requested only on the admissible
core parameter domain. -/
abbrev ExactRealPrimitives :=
  {k dx dz : ℕ} → {L pi0 sigma0 : ℝ} →
    CoreParameterDomain k dx dz L pi0 sigma0 →
      ExactRealPrimitivesAt k dx dz L pi0 sigma0

/-- Feasibility identifies the admissible positive parameter domain carried by its model law. -/
lemma admissibleImage_coreParameterDomain {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    {s : SummarySpace dx dz} (hs : s ∈ admissibleImage k dx dz L pi0 sigma0) :
    CoreParameterDomain k dx dz L pi0 sigma0 := by
  rcases hs with ⟨Q, _⟩
  letI := Q.prob
  exact Q.model.coreDomain

-- keep: public nonvacuity certificate for the exact-real primitive carrier audited by F2.5/F5
/-- The exact-real primitive carrier is inhabited: representative spectral data on every
admissible summary supplies a combined fixed-parameter run. -/
theorem exactRealPrimitives_nonempty : Nonempty ExactRealPrimitives := by
  classical
  refine ⟨fun {k dx dz} {L pi0 sigma0} _ => ⟨fun s hs => ?_⟩⟩
  let D := Classical.choice (representativeSpectralData_exists s hs)
  let signal : ThresholdedSignalExecution
      (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s :=
    { basis := D.basis
      spans := D.spans
      armwiseFullRank := D.armwiseFullRank
      thresholdRetainsExactlySignal := D.thresholdRetainsExactlySignal
      trace := List.replicate 3 .singularValue
      trace_eq := rfl }
  refine ({
    signal := signal
    roots := {
      eigenvalue := D.eigenvalue
      eigenvalue_complete := D.eigenvalue_complete
      lawValid := ?_
      trace := [.rootIsolation, .arithmetic]
      trace_eq := rfl } } : ExactRealSpectralRun
        (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s)
  exact D.lawValid

/-- The representative spectral datum computed by an exact-real spectral execution. -/
noncomputable def ExactRealSpectralRun.output {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    {s : SummarySpace dx dz} (run : ExactRealSpectralRun
      (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s) :
    RepresentativeSpectralData k dx dz (effectRadius dz L sigma0)
      (pi0 * sigma0 ^ 2 / 2) s where
  basis := run.signal.basis
  spans := run.signal.spans
  armwiseFullRank := run.signal.armwiseFullRank
  thresholdRetainsExactlySignal := run.signal.thresholdRetainsExactlySignal
  eigenvalue := run.roots.eigenvalue
  eigenvalue_complete := run.roots.eigenvalue_complete
  lawValid := run.roots.lawValid

/-- The trace is assembled from the two result-bearing primitive executions that produced the
spectral output. -/
def ExactRealSpectralRun.trace {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    {s : SummarySpace dx dz} (run : ExactRealSpectralRun
      (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s) :
    List NetPrimitiveOperation :=
  run.signal.trace ++ run.roots.trace

/-- Execute the result-bearing singular-value and root-isolation primitives.  No choice operator
or precomputed spectral selector participates in this definition. -/
noncomputable def exactRealSpectralRun {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (s : SummarySpace dx dz)
    (hs : s ∈ admissibleImage k dx dz L pi0 sigma0) :
    ExactRealSpectralRun (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s :=
  (primitives (admissibleImage_coreParameterDomain hs)).spectralRun s hs

/-- Instructions used to form all coordinates of the empirical summary. -/
def netSummaryTrace (n dx dz : ℕ) : List NetPrimitiveOperation :=
  List.replicate (n * (4 * dz * dx + dx)) .arithmetic

/-- Instructions used by the actual fold over the representative list.  Each distance evaluates
four fixed-dimensional operator norms, its scalar coordinate arithmetic, and one comparison. -/
noncomputable def netSearchTrace {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) : List NetPrimitiveOperation :=
  A.indexList.flatMap fun _ =>
    List.replicate (4 * dz * dx + dx) .arithmetic ++
      List.replicate 4 .singularValue ++ [.comparison]

/-- The result and exact primitive trace of the finite-library program. -/
structure NetProgramResult {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) where
  selected : Option A.index
  law : AtomicLaw.LawModulo k (effectRadius dz L sigma0)
  trace : List NetPrimitiveOperation

/-- The operationally linked exact-real program: form the summary, exhaustively scan the finite
library, then run singular-value thresholding and fixed-degree root isolation only at the selected
representative. -/
noncomputable def netExactRealProgram {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) :
    NetProgramResult A :=
  let baseTrace := netSummaryTrace n dx dz ++ netSearchTrace A
  match hsel : nearestLibraryIndex A (empSummary sample) with
  | none =>
      { selected := none
        law := AtomicLaw.LawModulo.deltaZeroLaw A.k_pos A.radius_nonneg
        trace := baseTrace }
  | some i =>
      let run := exactRealSpectralRun primitives (A.summary i) (A.representative_feasible i)
      { selected := some i
        law := run.output.effectLaw
        trace := baseTrace ++ run.trace }

/-- The advised finite-library estimator is the output of the explicit exhaustive-search and
spectral program; the only advice is the representative-summary library.
    @realizes \(\widehat\nu_n^{\mathrm{net}}\)(nearest finite-library law) -/
-- @node: def:finite-net-law-estimator
noncomputable def netLawEstimator {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) :
    AtomicLaw.LawModulo k (effectRadius dz L sigma0) :=
  (netExactRealProgram primitives A sample).law

/-- The operation count is computed from the trace of the very execution producing the estimate. -/
noncomputable def netOperationCount {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) :
    NetOperationCount :=
  netTraceCost (netExactRealProgram primitives A sample).trace

/-- A completed primitive run has the fixed five-operation spectral tail. -/
lemma ExactRealSpectralRun.trace_eq_fixed {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    {s : SummarySpace dx dz}
    (run : ExactRealSpectralRun (k := k) (L := L) (pi0 := pi0) (sigma0 := sigma0) s) :
    run.trace = List.replicate 3 .singularValue ++ [.rootIsolation, .arithmetic] := by
  unfold ExactRealSpectralRun.trace
  rw [run.signal.trace_eq, run.roots.trace_eq]

/-- The operational program trace is definitionally linked to the selected primitive run. -/
lemma netExactRealProgram_trace_eq
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) :
    (netExactRealProgram primitives A sample).trace =
      netSummaryTrace n dx dz ++ netSearchTrace A ++
        match (netExactRealProgram primitives A sample).selected with
        | none => []
        | some i => (exactRealSpectralRun primitives (A.summary i)
            (A.representative_feasible i)).trace := by
  unfold netExactRealProgram
  split <;> simp

/-- On a successful exhaustive selection, the returned law is exactly the law produced by the
result-bearing spectral run at that selected representative. -/
lemma netLawEstimator_eq_of_selected
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) (i : A.index)
    (hsel : (netExactRealProgram primitives A sample).selected = some i) :
    netLawEstimator primitives A sample =
      (exactRealSpectralRun primitives (A.summary i)
        (A.representative_feasible i)).output.effectLaw := by
  unfold netLawEstimator
  unfold netExactRealProgram at hsel ⊢
  split at *
  · simp_all
  · rename_i j hj
    change some j = some i at hsel
    have hji : j = i := Option.some.inj hsel
    subst i
    rfl

/-- Every result-bearing spectral execution returns a valid representative law. -/
lemma exactRealSpectralRun_output_valid
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ} (primitives : ExactRealPrimitives)
    (s : SummarySpace dx dz) (hs : s ∈ admissibleImage k dx dz L pi0 sigma0) :
    AtomicLaw.Valid
      ((exactRealSpectralRun primitives s hs).output.effectLaw.representative.1) := by
  exact (exactRealSpectralRun primitives s hs).output.effectLaw.representative.2

/-- A concrete structured-lattice estimator interface. -/
structure LatticeEstimator (k dx dz n : ℕ) (radius : ℝ) where
  summaryRule : SummarySpace dx dz → AtomicLaw.LawModulo k radius
  summaryRule_measurable : Measurable summaryRule
  estimate : (Fin n → Obs dx dz) → AtomicLaw.LawModulo k radius
  measurable : Measurable estimate
  atomFloor : ℝ
  atomFloor_valid : ∀ sample,
    AtomicLaw.AtomFloor atomFloor (estimate sample).representative.1
  estimate_eq : estimate = fun sample => summaryRule (empSummary sample)
  candidateCount : ℕ

/-- The exhaustive-search work count: one pass over the sample and one fixed-dimensional
criterion evaluation for every enumerated lattice point. -/
def latticeOperationCount {k dx dz n : ℕ} {radius : ℝ}
    (A : LatticeEstimator k dx dz n radius) : ℕ :=
  n + A.candidateCount

/-- One point in the prescribed no-advice product lattice. -/
structure StructuredLatticePoint (k dx : ℕ) (radius : ℝ) where
  gridBasis : RectMatrix dx k
  V : RectMatrix dx k
  R : RectMatrix k k
  weight : Fin k → ℝ
  effect : Fin k → ℝ
  lawValid : AtomicLaw.Valid (⟨weight, effect⟩ : AtomicLaw k radius)

noncomputable def latticeHeight (k dx n : ℕ) (pi0 sigma0 : ℝ) : ℕ :=
  ⌈Real.sqrt n⌉₊ + ⌈pi0⁻¹⌉₊ + 2 * k +
    ⌈4 * Real.sqrt (dx * k)⌉₊ + ⌈2 * k / sigma0⌉₊

noncomputable def latticeMesh (k dx n : ℕ) (pi0 sigma0 : ℝ) : ℝ :=
  (latticeHeight k dx n pi0 sigma0 : ℝ)⁻¹

/-- The displayed constant `C_lat` from the structured-lattice construction.
    @realizes \(C_{\mathrm{lat}}\)(explicit positive structured-lattice constant) -/
noncomputable def prescribedLatticeConstant
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : ℝ :=
  let Ltau := effectRadius dz L sigma0
  let s0 := pi0 * sigma0 ^ 2
  let cV := 4 * Real.sqrt (dx * k)
  let KD := 4 * Real.sqrt k * L * Ltau / sigma0
  let AD := 8 / (3 * s0) + 32 * L / s0 ^ 2
  let Kf := 16 * Real.sqrt dx * k * L ^ 2 / sigma0 ^ 2
  let cD := 2 * KD * cV + 4 * k * Real.sqrt k * L * Ltau / sigma0 ^ 2 +
    2 * Real.sqrt k * L / sigma0 + k * Ltau / sigma0
  let cm := 2 * Real.sqrt k * L * cV + k + k * L
  let cb := k + 2 * Real.sqrt k * L * cV
  let cgrid := cD + cm + cb
  let Blat := 2 * (AD + 1) + cgrid
  max (8 * Ltau / s0) ((Ltau + KD + L * Kf) * Blat)

def ThresholdRecoversMatrixDimension {rows cols : ℕ}
    (k : ℕ) (threshold : ℝ) (G : RectMatrix rows cols) : Prop :=
  (∀ j, j < k → threshold ≤ singularValue G j) ∧
  ∀ j, k ≤ j → singularValue G j < threshold

def ThresholdRecoversDimension {dx dz : ℕ}
    (k : ℕ) (threshold : ℝ) (s : SummarySpace dx dz) : Prop :=
  ThresholdRecoversMatrixDimension k threshold (stackedProxyMoment s)

-- @node: inverseGramSqrt_exists
lemma inverseGramSqrt_exists {k dx : ℕ} (G : RectMatrix dx k)
    (_hG : 1 / 2 ≤ signalMinSingular G) :
    ∃ H : RectMatrix k k, H.PosSemidef ∧ H * H = (G.transpose * G)⁻¹ := by
  have hgram : (G.transpose * G).PosSemidef := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial G]
    exact Matrix.posSemidef_conjTranspose_mul_self G
  have hinv : ((G.transpose * G)⁻¹).PosSemidef := hgram.inv
  refine ⟨CFC.sqrt ((G.transpose * G)⁻¹), ?_, ?_⟩
  · exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  · simpa [pow_two] using CFC.sq_sqrt ((G.transpose * G)⁻¹)

/-- The inverse positive square root of the Gram matrix used in the paper's polar factor. -/
noncomputable def inverseGramSqrt {k dx : ℕ} (G : RectMatrix dx k)
    (hG : 1 / 2 ≤ signalMinSingular G) : RectMatrix k k :=
  Classical.choose (inverseGramSqrt_exists G hG)

/-- The unique prescribed polar-factor basis `G (G^T G)^(-1/2)`. -/
noncomputable def prescribedPolarFactor {k dx : ℕ} (G : RectMatrix dx k)
    (hG : 1 / 2 ≤ signalMinSingular G) : RectMatrix dx k :=
  G * inverseGramSqrt G hG

/-- Exact grid, polar-factor, conditioning, simplex-floor, and clipped-support constraints. -/
def StructuredLatticePoint.WellFormed {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0)) : Prop :=
  let H := latticeHeight k dx n pi0 sigma0
  let q := latticeMesh k dx n pi0 sigma0
  (∀ i j, ∃ z : ℤ, θ.gridBasis i j = q * z ∧ |θ.gridBasis i j| ≤ 1) ∧
  (∃ hG : 1 / 2 ≤ signalMinSingular θ.gridBasis,
    θ.V = prescribedPolarFactor θ.gridBasis hG) ∧
  (∀ i j, ∑ a, θ.V a i * θ.V a j = if i = j then 1 else 0) ∧
  (∀ i j, ∃ z : ℤ, θ.R i j = q * z) ∧
  sigma0 / 2 ≤ signalMinSingular θ.R ∧ ‖matrixCLM θ.R‖ ≤ 2 * Real.sqrt k * L ∧
  (∃ a : Fin k → ℕ, (∀ u, ⌈pi0 * H⌉₊ ≤ a u ∧ θ.weight u = a u / H) ∧
    ∑ u, a u = H) ∧
  ∀ u, θ.effect u ∈ Set.Icc (-effectRadius dz L sigma0) (effectRadius dz L sigma0) ∧
    ∃ z : ℤ, θ.effect u = q * z

noncomputable def structuredCandidateOperator {k dx : ℕ} {radius : ℝ}
    (θ : StructuredLatticePoint k dx radius) : RectMatrix dx dx :=
  θ.V * θ.R⁻¹ * Matrix.diagonal θ.effect * θ.R * θ.V.transpose

noncomputable def empiricalCompressedOperator {dx dz : ℕ}
    (threshold : ℝ) (s : SummarySpace dx dz) : RectMatrix dx dx :=
  thresholdedPenroseInverse threshold s.M1 * s.N1 -
    thresholdedPenroseInverse threshold s.M0 * s.N0

noncomputable def structuredLatticeCriterion {k dx dz : ℕ} {radius : ℝ}
    (threshold : ℝ) (s : SummarySpace dx dz)
    (θ : StructuredLatticePoint k dx radius) : ℝ :=
  ‖matrixCLM (structuredCandidateOperator θ - empiricalCompressedOperator threshold s)‖ +
  Real.sqrt (∑ i, ((∑ u, θ.V i u * (∑ v, θ.R v u * θ.weight v)) - s.mX i) ^ 2) +
  Real.sqrt (∑ u, ((∑ v, θ.R u v * (∑ i, θ.V i v * firstBasis dx i)) - 1) ^ 2)

noncomputable def StructuredLatticePoint.effectLaw {k dx : ℕ} {radius : ℝ}
    (θ : StructuredLatticePoint k dx radius) : AtomicLaw.LawModulo k radius :=
  AtomicLaw.LawModulo.ofProbabilityLaw ⟨⟨θ.weight, θ.effect⟩, θ.lawValid⟩

noncomputable def structuredLatticeLexKey {k dx : ℕ} {radius : ℝ}
    (θ : StructuredLatticePoint k dx radius) : List ℝ :=
  (Finset.univ.toList.flatMap fun i : Fin dx =>
      Finset.univ.toList.map fun j : Fin k => θ.V i j) ++
  (Finset.univ.toList.flatMap fun i : Fin k =>
      Finset.univ.toList.map fun j : Fin k => θ.R i j) ++
  (Finset.univ.toList.map fun i : Fin k => θ.weight i) ++
  (Finset.univ.toList.map fun i : Fin k => θ.effect i)

def StructuredLatticePoint.LexLE {k dx : ℕ} {radius : ℝ}
    (θ φ : StructuredLatticePoint k dx radius) : Prop :=
  structuredLatticeLexKey θ = structuredLatticeLexKey φ ∨
    List.Lex (· < ·) (structuredLatticeLexKey θ) (structuredLatticeLexKey φ)

/-- The estimator is exactly the first minimizer of the displayed `H_n`/`q_n` lattice, its
candidate count is an actual exhaustive list size, and its runtime accounts for that search. -/
def IsPrescribedStructuredLattice {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0)) : Prop :=
  ∃ (candidate : Fin A.candidateCount →
      StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (first : (Fin n → Obs dx dz) → Fin A.candidateCount),
    (∀ i, StructuredLatticePoint.WellFormed (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0) (candidate i)) ∧
    (∀ θ : StructuredLatticePoint k dx (effectRadius dz L sigma0),
      StructuredLatticePoint.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0) θ → ∃ i,
        (candidate i).V = θ.V ∧ (candidate i).R = θ.R ∧
        (candidate i).weight = θ.weight ∧ (candidate i).effect = θ.effect) ∧
    (∀ i j, (candidate i).V = (candidate j).V →
      (candidate i).R = (candidate j).R →
      (candidate i).weight = (candidate j).weight →
      (candidate i).effect = (candidate j).effect → i = j) ∧
    (∀ i j, i ≤ j ↔ StructuredLatticePoint.LexLE (candidate i) (candidate j)) ∧
    (∀ sample i, structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample)
        (candidate (first sample)) ≤
      structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) (candidate i)) ∧
    (∀ sample i, structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample)
        (candidate (first sample)) =
      structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) (candidate i) →
      first sample ≤ i) ∧
    A.estimate = fun sample => (candidate (first sample)).effectLaw

/-- The explicit lattice-law output. @realizes \(\widehat\lambda_n\)(no-advice lattice estimate) -/
noncomputable def latticeLaw {k dx dz n : ℕ} {radius : ℝ}
    (A : LatticeEstimator k dx dz n radius) :
    (Fin n → Obs dx dz) → AtomicLaw.LawModulo k radius :=
  A.estimate

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
