import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Finite-incidence duality and refinement

Primal fibers, explicit unnormalised dual faces, label-blind embeddings, and
the strict-refinement region.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators
open Set

variable {O T OBlind : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]

/-- The lower dual feasible polyhedron. -/
def lowerDualFeasible (G : SLCCIncidence O T OBlind) : Set (ℝ × (O → ℝ)) :=
  {aLam | ∀ t, aLam.1 + ∑ o, G.B o t * aLam.2 o ≤ G.h t}
  -- @realizes D_L_dual(alpha 1 + Bᵀ lambda ≤ h_e)

/-- The upper dual feasible polyhedron. -/
def upperDualFeasible (G : SLCCIncidence O T OBlind) : Set (ℝ × (O → ℝ)) :=
  {aLam | ∀ t, G.h t ≤ aLam.1 + ∑ o, G.B o t * aLam.2 o}
  -- @realizes D_U_dual(alpha 1 + Bᵀ lambda ≥ h_e)

/-- The affine dual objective at observable law `p`. -/
def dualObjective (p : O → ℝ) (aLam : ℝ × (O → ℝ)) : ℝ :=
  aLam.1 + ∑ o, aLam.2 o * p o

/-- All unnormalised optimal lower-dual solutions. -/
def lowerOptimalFace (G : SLCCIncidence O T OBlind) (p : O → ℝ) :
    Set (ℝ × (O → ℝ)) :=
  {aLam | aLam ∈ lowerDualFeasible G ∧ dualObjective p aLam = lowerEndpoint G p}
  -- @realizes Lambda_L(all lower-dual optima)

/-- All unnormalised optimal upper-dual solutions. -/
def upperOptimalFace (G : SLCCIncidence O T OBlind) (p : O → ℝ) :
    Set (ℝ × (O → ℝ)) :=
  {aLam | aLam ∈ upperDualFeasible G ∧ dualObjective p aLam = upperEndpoint G p}
  -- @realizes Lambda_U(all upper-dual optima)

/-- Full dual pairs representable using only blind rows. -/
def embeddedBlindDual (G : SLCCIncidence O T OBlind) : Set (ℝ × (O → ℝ)) :=
  {aLam | ∃ μ : OBlind → ℝ, ∀ o, aLam.2 o = ∑ b, G.K b o * μ b}
  -- @realizes E_K((alpha,K_blindᵀ mu))

/-- The bundled full and blind-embedded endpoint dual faces. -/
structure DualRefinementData (O : Type*) where
  lowerFeasible : Set (ℝ × (O → ℝ))
  upperFeasible : Set (ℝ × (O → ℝ))
  lowerFace : Set (ℝ × (O → ℝ))
  upperFace : Set (ℝ × (O → ℝ))
  blindSubspace : Set (ℝ × (O → ℝ))

/-- Full feasible polyhedra, optimal faces, and the embedded blind subspace. -/
-- @node: def:dual-refinement-faces
def dualRefinementFaces (G : SLCCIncidence O T OBlind) (p : O → ℝ) :
    DualRefinementData O :=
  { lowerFeasible := lowerDualFeasible G
    upperFeasible := upperDualFeasible G
    lowerFace := lowerOptimalFace G p
    upperFace := upperOptimalFace G p
    blindSubspace := embeddedBlindDual G }

/-- The full-data laws where both blind bounds are strictly improved. -/
-- @node: def:strict-refinement-region
noncomputable def strictRefinementRegion (G : SLCCIncidence O T OBlind) :
    Set (O → ℝ) :=
  {p | p ∈ observablePolytope G ∧
    (blindEndpointPrograms G p).1 < lowerEndpoint G p ∧
    upperEndpoint G p < (blindEndpointPrograms G p).2}
  -- @realizes S_strict(two-sided strict-refinement laws)

/-- A finite maximum-of-affine representation on a domain. -/
def FiniteAffineMaxOn (s : Set (O → ℝ)) (f : (O → ℝ) → ℝ) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → O → ℝ, ∃ b : Fin n → ℝ,
    ∀ p ∈ s, f p = sSup {x | ∃ i, x = b i + ∑ o, a i o * p o}

/-- A finite minimum-of-affine representation on a domain. -/
def FiniteAffineMinOn (s : Set (O → ℝ)) (f : (O → ℝ) → ℝ) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → O → ℝ, ∃ b : Fin n → ℝ,
    ∀ p ∈ s, f p = sInf {x | ∃ i, x = b i + ∑ o, a i o * p o}

/-- Finite incidence programs attain, satisfy strong duality, have nonempty
optimal faces, and are continuous finite piecewise-affine value functions. -/
-- @node: lem:finite-incidence-duality-continuity
lemma finite_incidence_duality_continuity (G : SLCCIncidence O T OBlind) :
    (∀ p ∈ observablePolytope G,
      (∃ w ∈ responseFiber G p, targetFunctional G w = lowerEndpoint G p) ∧
      (∃ w ∈ responseFiber G p, targetFunctional G w = upperEndpoint G p) ∧
      lowerEndpoint G p = sSup (dualObjective p '' lowerDualFeasible G) ∧
      upperEndpoint G p = sInf (dualObjective p '' upperDualFeasible G) ∧
      (lowerOptimalFace G p).Nonempty ∧ (upperOptimalFace G p).Nonempty) ∧
    FiniteAffineMaxOn (observablePolytope G) (lowerEndpoint G) ∧
    FiniteAffineMinOn (observablePolytope G) (upperEndpoint G) ∧
    ContinuousOn (lowerEndpoint G) (observablePolytope G) ∧
    ContinuousOn (upperEndpoint G) (observablePolytope G) ∧
    ContinuousOn (fun p => (blindEndpointPrograms G p).1) (observablePolytope G) ∧
    ContinuousOn (fun p => (blindEndpointPrograms G p).2) (observablePolytope G) := by
  sorry

/-- Forgetting revealed labels enlarges every primal fiber and hence every
identified interval. -/
-- @node: lem:z-blind-coarsening
lemma z_blind_coarsening (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) (hp : p ∈ observablePolytope G) :
    responseFiber G p ⊆
        {w | w ∈ stdSimplex ℝ T ∧ (blindIncidence G).mulVec w = blindLaw G p} ∧
      Set.Icc (lowerEndpoint G p) (upperEndpoint G p) ⊆
        Set.Icc (blindEndpointPrograms G p).1 (blindEndpointPrograms G p).2 := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
