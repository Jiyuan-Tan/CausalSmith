import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.World
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.Deriv.Basic
import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions

/-!
# Cyclic structural completions

Fixed-representative and law-level completion fibers for nonsingular cyclic linear systems. No
spectral-radius or dynamic-stability restriction is imposed.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

universe u

abbrev SquareMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The structural normalization is the reused unit-diagonal predicate, not merely square-matrix
typing. -/
-- @node: ass:unit-structural-diagonal
def UnitStructuralDiagonal {n : ℕ} (Q : SquareMatrix n) : Prop :=
  Causalean.Discovery.LinearDisentanglement.Quantitative.UnitDiagonal Q
  -- @realizes Qmat(Q_ii = 1 for every structural equation)

def deleteSquare {n : ℕ} (Q : SquareMatrix n) (x : Fin n) :
    Matrix {i : Fin n // i ≠ x} {i : Fin n // i ≠ x} ℝ :=
  Q.submatrix Subtype.val Subtype.val

def deleteRowCol {p n : ℕ} (C : MixingMatrix p n) (x : Fin p) (j : Fin n) :
    Matrix {i : Fin p // i ≠ x} {k : Fin n // k ≠ j} ℝ :=
  C.submatrix Subtype.val Subtype.val

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ)
  (x : Fin p) -- @realizes x(treatment coordinate in Obs)
  (y : {i : Fin p // i ≠ x}) -- @realizes y(outcome coordinate in Obs excluding x)

/-- Structural coefficient matrix `B = I - Q`. -/
def structuralCoefficients (Q : SquareMatrix n) : SquareMatrix n := 1 - Q
  -- @realizes B(B = I - Qmat)

/-- The equilibrium random vector `V = Q⁻¹ H ε`. -/
noncomputable def equilibriumVector (Q H : SquareMatrix n) (ε : Fin n → Ω → ℝ) : Ω → Vec n :=
  fun ω i => ∑ j, (Q⁻¹ * H) i j * ε j ω
  -- @realizes V(V = Qmat inverse Hmat epsilon)

-- @node: ass:source-assignment
def MonomialSourceAssignment (H : SquareMatrix n) : Prop :=
  (∀ i, ∃! j, H i j ≠ 0) ∧ (∀ j, ∃! i, H i j ≠ 0)

-- @node: ass:observational-solvability
def ObservationalSolvability (Q : SquareMatrix n) : Prop := Q.det ≠ 0

-- @node: ass:fixed-law-match
def FixedLawMatch (C : MixingMatrix p n) (hpn : p ≤ n) (Q H : SquareMatrix n) : Prop :=
  ∀ i j, (Q⁻¹ * H) (Fin.castLE hpn i) j = C i j

-- @node: ass:postintervention-solvability
def PostinterventionSolvability (Q : SquareMatrix n) (x : Fin n) : Prop :=
  (deleteSquare Q x).det ≠ 0

/-- Fixed-law completion membership, with exactly the five atomized core conditions. -/
-- @node: def:completion-fiber
structure CompletionFiber (C : MixingMatrix p n) (hpn : p ≤ n) (x : Fin p)
    (Q H : SquareMatrix n) : Prop where
  unitDiagonal : UnitStructuralDiagonal Q
    -- @realizes Qmat(unit diagonal structural equation matrix)
  monomial : MonomialSourceAssignment H -- @realizes Hmat(monomial source assignment matrix)
  solvable : ObservationalSolvability Q -- @realizes Mcomp(observationally solvable pair Q,H)
  fixedLaw : FixedLawMatch C hpn Q H -- @realizes Fx(observed block of Q inverse H equals C)
  postSolvable : PostinterventionSolvability Q (Fin.castLE hpn x)
    -- @realizes Fx(postintervention minor at x is nonsingular)

/-- The unique source assigned by a monomial disturbance matrix. -/
-- @node: def:assigned-source
noncomputable def assignedSource (H : SquareMatrix n) (hH : MonomialSourceAssignment H)
    (i : Fin n) : Fin n :=
  Classical.choose (hH.1 i)
  -- @realizes sassign(unique nonzero column of row i)

/-- Equilibrium effect of a postintervention-solvable fixed-law completion. -/
-- @node: def:equilibrium-effect
noncomputable def equilibriumEffect (C : MixingMatrix p n) (hpn : p ≤ n)
    (x : Fin p) (y : {i : Fin p // i ≠ x}) (Q H : SquareMatrix n)
    (_hM : CompletionFiber C hpn x Q H) : ℝ :=
  Q⁻¹ (Fin.castLE hpn y.1) (Fin.castLE hpn x) /
    Q⁻¹ (Fin.castLE hpn x) (Fin.castLE hpn x)
  -- @realizes theta(theta_y<-x = Qinv_yx / Qinv_xx)

/-- A law-level completion is a dependent tuple `(m,Q,H,xi)` with `p ≤ m` and a
nonsingular structural matrix. Nonsingularity makes the inverse-defined endogenous vector a
genuine solution of `Q V = H xi`. -/
-- @node: def:observational-law-completion
def LawCompletion (p : ℕ) : Type (u + 1) :=
  Σ Ω : Type u, Σ mΩ : MeasurableSpace Ω, Σ μ : @Measure Ω mΩ,
    Σ m : {m : ℕ // p ≤ m},
      {z : SquareMatrix m.1 × SquareMatrix m.1 × (Fin m.1 → Ω → ℝ) //
        ObservationalSolvability z.1}
  -- @realizes Mlaw(each completion packages its own measurable carrier and measure)

namespace LawCompletion

def carrier (M : LawCompletion.{u} p) : Type u := M.1

def measurableSpace (M : LawCompletion.{u} p) : MeasurableSpace M.carrier := M.2.1

instance instMeasurableSpace (M : LawCompletion.{u} p) : MeasurableSpace M.carrier :=
  M.measurableSpace

def measure (M : LawCompletion.{u} p) : Measure M.carrier := M.2.2.1

def dim (M : LawCompletion.{u} p) : ℕ := M.2.2.2.1.1
  -- @realizes mMlaw(completion dimension at least p)

def Q (M : LawCompletion.{u} p) : SquareMatrix M.dim := M.2.2.2.2.1.1
  -- @realizes Qlaw(real mMlaw by mMlaw structural matrix)

def H (M : LawCompletion.{u} p) : SquareMatrix M.dim := M.2.2.2.2.1.2.1
  -- @realizes Hlaw(real mMlaw by mMlaw source assignment matrix)

def xi (M : LawCompletion.{u} p) : Fin M.dim → M.carrier → ℝ := M.2.2.2.2.1.2.2
  -- @realizes xilaw(mMlaw real random variables)

def solvable (M : LawCompletion.{u} p) : ObservationalSolvability M.Q := M.2.2.2.2.2

def liftObserved (M : LawCompletion.{u} p) (i : Fin p) : Fin M.dim :=
  Fin.castLE M.2.2.2.1.2 i

noncomputable def observedMixing (M : LawCompletion.{u} p) : MixingMatrix p M.dim :=
  fun i j => (M.Q⁻¹ * M.H) (M.liftObserved i) j
  -- @realizes Alaw(observed block of Qlaw inverse Hlaw)

noncomputable def endogenous (M : LawCompletion.{u} p) : M.carrier → Vec M.dim :=
  equilibriumVector M.Q M.H M.xi
  -- @realizes Vlaw(equilibrium satisfying Qlaw Vlaw = Hlaw xilaw)

lemma endogenous_equilibrium (M : LawCompletion.{u} p) :
    ∀ ω, M.Q.mulVec (M.endogenous ω) = M.H.mulVec (fun j => M.xi j ω) := by
  intro ω
  change M.Q.mulVec ((M.Q⁻¹ * M.H).mulVec _) = _
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv M.Q ((isUnit_iff_ne_zero).2 M.solvable), Matrix.one_mul]

end LawCompletion

/-- Law-level fiber membership. The grouped source and irreducibility fields spell out all core
conditions while keeping the construction's eight logical clauses. -/
-- @node: def:law-completion-fiber
structure LawCompletionFiber (P : Measure (Vec p)) (x : Fin p)
    (M : LawCompletion.{u} p) : Prop where
  probability : IsProbabilityMeasure M.measure
  unitDiagonal : UnitStructuralDiagonal M.Q
  monomial : MonomialSourceAssignment M.H
  postSolvable : PostinterventionSolvability M.Q (M.liftObserved x)
  sourceConditions :
    ProbabilityTheory.iIndepFun M.xi M.measure ∧
      NondegenerateSources M.measure M.xi ∧ NonGaussianSources M.measure M.xi
  irreducible : NonzeroColumns M.observedMixing ∧ DistinctDirections M.observedMixing
  lawMatch : observedLaw M.measure M.observedMixing M.xi = P
    -- @realizes Flaw(source-minimal same-law postintervention-solvable fiber)

/-- The unique disturbance source assigned to an observed equation in a law completion. -/
-- @node: def:law-assigned-source
noncomputable def lawAssignedSource {M : LawCompletion.{u} p}
    (hM : LawCompletionFiber P x M) (i : Fin p) : Fin M.dim :=
  assignedSource M.H hM.monomial (M.liftObserved i)
  -- @realizes slaw(unique k with Hlaw_ik nonzero)

/-- Alignment to the unique reference projective direction on its intrinsic uniqueness domain.
Consumers derive the uniqueness witness from OICA uniqueness rather than adding it to the fiber. -/
def HasUniqueAlignedSource {M : LawCompletion.{u} p}
    (hM : LawCompletionFiber P x M) (C : MixingMatrix p n) (i : Fin p) : Prop :=
  ∃! j : Fin n,
    projectiveClass (M.observedMixing.col
      (lawAssignedSource (P := P) (x := x) hM i)) =
      projectiveClass (C.col j)

-- @node: def:law-aligned-source
noncomputable def alignedSource {M : LawCompletion.{u} p}
    (hM : LawCompletionFiber P x M) (C : MixingMatrix p n) (i : Fin p)
    (hunique : HasUniqueAlignedSource (P := P) (x := x) hM C i) : Fin n :=
  Classical.choose hunique
  -- @realizes salign(unique reference direction aligned with law-assigned source)

/-- Embed an observed nonintervened coordinate into the reduced postintervention system. -/
def LawCompletion.liftObservedAway (M : LawCompletion.{u} p) (x : Fin p)
    (i : {i : Fin p // i ≠ x}) : {k : Fin M.dim // k ≠ M.liftObserved x} :=
  ⟨M.liftObserved i.1, by
    intro h
    apply i.2
    have hv : (M.liftObserved i.1).val = (M.liftObserved x).val :=
      congrArg (fun z : Fin M.dim => z.val) h
    apply Fin.ext
    exact hv⟩

/-- The reduced postintervention equilibrium path.  For a realized source vector `sourceState`,
it solves `Q_{-x,-x} V_{-x} = H_{-x,:} sourceState - Q_{-x,x} t`. -/
noncomputable def lawInterventionPath (M : LawCompletion.{u} p) (x : Fin p)
    (i : {i : Fin p // i ≠ x}) (sourceState : Vec M.dim) (t : ℝ) : ℝ :=
  let xx := M.liftObserved x
  let rhs : {k : Fin M.dim // k ≠ xx} → ℝ := fun k =>
    M.H.mulVec sourceState k.1 - M.Q k.1 xx * t
  (deleteSquare M.Q xx)⁻¹.mulVec rhs (M.liftObservedAway x i)

/-- Observed hard-intervention response, kept in derivative form. -/
-- @node: def:observed-response-vector
noncomputable def observedResponse {P : Measure (Vec p)} (M : LawCompletion.{u} p) (x : Fin p)
    (_hM : LawCompletionFiber P x M) :
    {i : Fin p // i ≠ x} → ℝ :=
  fun i => deriv (lawInterventionPath M x i 0) 0
  -- @realizes rhoLaw(vector of derivatives of postintervention equilibrium)

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
