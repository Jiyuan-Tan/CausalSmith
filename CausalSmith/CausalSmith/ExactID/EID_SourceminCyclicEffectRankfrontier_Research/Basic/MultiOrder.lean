import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Sampling
import Mathlib.Data.Set.Card

/-!
# Heterogeneous-order population oracle

The handle uses exact law moments and set-theoretic minimization. It has no finite-sample or
executable-complexity interpretation.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable def lawRawMoment {p nu : ℕ} (P : Measure (Vec p))
    (I : Fin nu → Fin p) (B : Finset (Fin nu)) : ℝ :=
  ∫ z, ∏ k ∈ B, z (I k) ∂P

noncomputable def lawCumulantTensor {p nu : ℕ} (P : Measure (Vec p)) :
    (Fin nu → Fin p) → ℝ :=
  fun I => ∑ pi : Finpartition (Finset.univ : Finset (Fin nu)),
    (-1 : ℝ) ^ (pi.parts.card - 1) * (Nat.factorial (pi.parts.card - 1) : ℝ) *
      ∏ B ∈ pi.parts, lawRawMoment P I B

def CPDecomposition {p nu : ℕ} (T : (Fin nu → Fin p) → ℝ)
    (R : ℕ) (gamma : Fin R → ℝ) (z : Fin R → Vec p) : Prop :=
  (∀ h, gamma h ≠ 0 ∧ z h ≠ 0) ∧
  T = fun I => ∑ h, gamma h * ∏ k, z h (I k)

def ThreeBlockCPDecomposition {p nu : ℕ} (T : (Fin nu → Fin p) → ℝ)
    (ell₁ ell₂ ell₃ R : ℕ) (gamma : Fin R → ℝ) (z : Fin R → Vec p) : Prop :=
  ell₁ + ell₂ + ell₃ = nu ∧ CPDecomposition T R gamma z

def IsLeastFeasibleRank {p nu n : ℕ} (T : (Fin nu → Fin p) → ℝ) (R : ℕ) : Prop :=
  R ≤ n ∧ (∃ gamma z, CPDecomposition T R gamma z) ∧
    ∀ S < R, ¬ ∃ gamma z, CPDecomposition T S gamma z

/-- Direction classes appearing in any least-rank decomposition of the exact order-`nu` tensor.
The three-block reshape has degrees `(n-1,n-1,nu-2n+2)`. -/
def orderDirectionClasses {p n : ℕ} (P : Measure (Vec p)) (nu : ℕ) :
    Set (Set (Vec p)) :=
  {D | 2 * n - 1 ≤ nu ∧ ∃ R gamma z,
    IsLeastFeasibleRank (n := n) (lawCumulantTensor (nu := nu) P) R ∧
    ThreeBlockCPDecomposition (lawCumulantTensor (nu := nu) P)
      (n - 1) (n - 1) (nu - 2 * n + 2) R gamma z ∧
    ∃ h, D = projectiveClass (z h)}

def selectedOrderDirectionClasses {p : ℕ} (rankAt : ℕ → ℕ)
    (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p) (nu : ℕ) :
    Set (Set (Vec p)) :=
  {D | ∃ h, D = projectiveClass (directionAt nu h)}

/-- An explicit choice of one least feasible decomposition at every order processed through `K`. -/
def ValidMultiOrderSelection {p : ℕ} (P : Measure (Vec p)) (n K : ℕ)
    (rankAt : ℕ → ℕ) (weightAt : (nu : ℕ) → Fin (rankAt nu) → ℝ)
    (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p) : Prop :=
  ∀ nu, 2 * n - 1 ≤ nu → nu ≤ K →
    IsLeastFeasibleRank (n := n) (lawCumulantTensor (nu := nu) P) (rankAt nu) ∧
    ThreeBlockCPDecomposition (lawCumulantTensor (nu := nu) P)
      (n - 1) (n - 1) (nu - 2 * n + 2) (rankAt nu) (weightAt nu) (directionAt nu)

def cumulativeSelectedDirectionClasses {p n : ℕ} (rankAt : ℕ → ℕ)
    (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p) (nu : ℕ) :
    Set (Set (Vec p)) :=
  {D | ∃ k, 2 * n - 1 ≤ k ∧ k ≤ nu ∧
    D ∈ selectedOrderDirectionClasses rankAt directionAt k}

noncomputable def stoppingOrder {p : ℕ} (n K : ℕ) (rankAt : ℕ → ℕ)
    (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p) : Option ℕ :=
  let candidates := (Finset.range (K + 1)).filter fun nu =>
    2 * n - 1 ≤ nu ∧
      (cumulativeSelectedDirectionClasses (n := n) rankAt directionAt nu).ncard = n
  if h : candidates.Nonempty then some (candidates.min' h) else none

inductive MultiOrderHandleResult (p K : ℕ) where
  | complete (stop : ℕ) (directions : Set (Set (Vec p)))
  | increaseCap (nextCap : ℕ) (strictIncrease : K < nextCap)
      (directionsSoFar : Set (Set (Vec p)))

def MultiOrderHandleResult.directions : MultiOrderHandleResult p K → Set (Set (Vec p))
  | .complete _ D => D
  | .increaseCap _ _ D => D

-- @env: S5
variable {p : ℕ} (P : Measure (Vec p)) (n K : ℕ)

/-- The coupled exact-cumulant handle unions projective classes in increasing order and stops at
the first processed order whose exact-projective union has cardinality `n`; increasing `K`
continues processing if no such order has yet appeared. -/
-- @node: def:multi-order-handle
noncomputable def multiOrderHandle (P : Measure (Vec p)) (n K : ℕ)
    (_hK : 2 * n - 1 ≤ K) (nextCap : ℕ) (hnext : K < nextCap)
    (rankAt : ℕ → ℕ)
    (weightAt : (nu : ℕ) → Fin (rankAt nu) → ℝ)
    (directionAt : (nu : ℕ) → Fin (rankAt nu) → Vec p)
    (_hselection : ValidMultiOrderSelection P n K rankAt weightAt directionAt) :
    MultiOrderHandleResult p K :=
  match stoppingOrder n K rankAt directionAt with
  | some nu => .complete nu
      (cumulativeSelectedDirectionClasses (n := n) rankAt directionAt nu)
  | none => .increaseCap nextCap hnext
      (cumulativeSelectedDirectionClasses (n := n) rankAt directionAt K)
  -- @realizes Hmulti(exact heterogeneous-order recovery handle)

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
