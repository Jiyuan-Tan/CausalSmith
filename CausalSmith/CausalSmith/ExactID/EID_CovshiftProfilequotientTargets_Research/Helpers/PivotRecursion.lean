import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Certificate
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Subset-memoized pivot recursion

Order-independent Schur residuals, the global proportionality pivot test, and
the accepted depth-`r` leaves.
-/

open scoped BigOperators
open Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

variable {d E r : ℕ}

/-- Canonically ordered selection matrix for a finite subset. -/
def subsetSelection (S : Finset (Fin d)) : Matrix {j // j ∈ S} (Fin d) ℝ :=
  fun i j => if i.1 = j then 1 else 0
  -- @realizes PS(selection of coordinates in Sset)

/-- Closed-form aggregate residual after eliminating a subset. -/
noncomputable def subsetResidual (Q : RealMatrix d) (S : Finset (Fin d)) : RealMatrix d :=
  let P := subsetSelection S
  Q - Q * P.transpose * (P * Q * P.transpose)⁻¹ * P * Q
  -- @realizes RS(R_S = Q - Q_:S Q_SS⁻¹ Q_S:)

/-- Closed-form environment residual after eliminating a subset. -/
noncomputable def subsetEnvironmentResidual (Q Δ : RealMatrix d)
    (S : Finset (Fin d)) : RealMatrix d :=
  let P := subsetSelection S
  let A : RealMatrix d := 1 - Q * P.transpose * (P * Q * P.transpose)⁻¹ * P
  A * Δ * A.transpose
  -- @realizes MeS(M_e,S = A Delta_e A^T)

/-- Global proportionality pivot test at state `S`. -/
noncomputable def PivotAdmissible (Q : RealMatrix d)
    (Δ : Environment E → RealMatrix d) (S : Finset (Fin d)) (j : Fin d) : Prop :=
  j ∉ S ∧
    let R := subsetResidual Q S
    0 < R j j ∧
      ∀ e : Fin E,
        let Me := subsetEnvironmentResidual Q (Δ e.succ) S
        0 ≤ Me j j ∧
          ∀ i, R j j * Me i j = Me j j * R i j
  -- @realizes Pivot(admissible positive global proportionality pivot)

/-- The same admissibility test evaluated on an operational residual pair. -/
def OperationalPivotAdmissible (R : RealMatrix d)
    (Me : Environment E → RealMatrix d) (S : Finset (Fin d)) (j : Fin d) : Prop :=
  j ∉ S ∧ 0 < R j j ∧
    ∀ e : Fin E, 0 ≤ Me e.succ j j ∧
      ∀ i, R j j * Me e.succ i j = Me e.succ j j * R i j

/-- Normalized pivot column used by the child update. -/
noncomputable def pivotDirection (R : RealMatrix d) (j : Fin d) : Fin d → ℝ :=
  fun i => R i j / R j j

/-- Aggregate Schur update at one pivot. -/
noncomputable def pivotAggregateUpdate (R : RealMatrix d) (j : Fin d) : RealMatrix d :=
  R - R j j • Matrix.vecMulVec (pivotDirection R j) (pivotDirection R j)

/-- A reachable operational run.  The initial constructor installs `(Q, Δ)`
at the empty memo key, and the child constructor is exactly the stated
one-coordinate Schur update. -/
inductive PivotRun (Q : RealMatrix d) (Δ : Environment E → RealMatrix d) (r : ℕ) :
    Finset (Fin d) → RealMatrix d → (Environment E → RealMatrix d) → Prop
  | initial : PivotRun Q Δ r ∅ Q Δ
  | child {S R Me j} : PivotRun Q Δ r S R Me → S.card < r →
      OperationalPivotAdmissible R Me S j →
      PivotRun Q Δ r (insert j S) (pivotAggregateUpdate R j)
        (fun e => Me e - Me e j j •
          Matrix.vecMulVec (pivotDirection R j) (pivotDirection R j))

/-- Subsets that occur as memo keys in an actual run. -/
def reachablePivotSubsets (Q : RealMatrix d)
    (Δ : Environment E → RealMatrix d) (r : ℕ) : Set (Finset (Fin d)) :=
  {S | ∃ R Me, PivotRun Q Δ r S R Me}

/-- The subset selected before position `k` of an ordering. -/
noncomputable def prefixSet (t : Fin r → Fin d) (k : Fin r) : Finset (Fin d) :=
  (Finset.univ.filter fun i => i < k).image t

/-- Depth-`r` subsets reached by the operational recursion. -/
def acceptedPivotLeaves (Q : RealMatrix d)
    (Δ : Environment E → RealMatrix d) (r : ℕ) : Set (Finset (Fin d)) :=
  {S | S ∈ reachablePivotSubsets Q Δ r ∧ S.card = r}

/-- Aggregate of the nonbaseline shifts. -/
def aggregateOfShifts (Δ : Environment E → RealMatrix d) : RealMatrix d :=
  ∑ e : Fin E, Δ e.succ
  -- @realizes Q(Qbar = sum of the nonbaseline Delta_e)

/-- Package containing every memoized residual and accepted leaf. -/
structure SubsetPivotState (d E r : ℕ) where
  aggregate : RealMatrix d
  shifts : Environment E → RealMatrix d
  run : Finset (Fin d) → RealMatrix d → (Environment E → RealMatrix d) → Prop
  reachable : Set (Finset (Fin d))
  residual : Finset (Fin d) → RealMatrix d
  environmentResidual : Environment E → Finset (Fin d) → RealMatrix d
  admissible : Finset (Fin d) → Fin d → Prop
  leaves : Set (Finset (Fin d))

-- @node: def:subset-pivot-recursion
noncomputable def subsetPivotRecursion (Δ : Environment E → RealMatrix d)
    (_hΔ0 : Δ 0 = 0) (_hΔsymm : ∀ e, (Δ e).IsHermitian)
    (r : ℕ) : SubsetPivotState d E r :=
  let Q := aggregateOfShifts Δ
  { aggregate := Q
    shifts := Δ
    run := PivotRun Q Δ r
    reachable := reachablePivotSubsets Q Δ r
    residual := subsetResidual Q
    environmentResidual e := subsetEnvironmentResidual Q (Δ e)
    admissible := PivotAdmissible Q Δ
    leaves := acceptedPivotLeaves Q Δ r }
  -- @realizes Delta(baseline Delta_0 = 0)
  -- @realizes Sset(subset memoization key with card at most r)

end CausalSmith.ExactID.CovshiftProfilequotientTargets
