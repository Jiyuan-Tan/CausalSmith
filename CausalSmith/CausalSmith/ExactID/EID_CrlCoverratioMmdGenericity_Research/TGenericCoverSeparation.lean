import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.AnalyticEdgePerturbation
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.GDelta.Basic
import Mathlib.Order.Cover

/-!
# Generic cover separation

This file states the open-dense direct-edge result and its residual
Gaussian-MMD ancestral-cover consequence, including the empty-graph case.
-/

open Set
open scoped Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: thm:generic-cover-separation
/-- In every nonempty fixed-DAG sign stratum, direct-edge moment separation is open dense and
implies an open dense residual ancestral-cover MMD region with closed nowhere-dense complement. -/
theorem generic_cover_separation
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (π : Equiv.Perm (Fin n))
    (hne : (Set.univ : Set (StratumPoint G s)).Nonempty) :
    IsOpen (edgeSeparatedSet (G := G) (s := s) π) ∧
    Dense (edgeSeparatedSet (G := G) (s := s) π) ∧
    edgeSeparatedSet (G := G) (s := s) π ⊆
      coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π ∧
    IsOpen (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) ∧
    Dense (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) ∧
    IsMeagre ((coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π)ᶜ) ∧
    IsClosed ((coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π)ᶜ) ∧
    IsNowhereDense ((coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π)ᶜ) ∧
    ((∀ j i, ¬ G.edge j i) →
      edgeSeparatedSet (G := G) (s := s) π = Set.univ ∧
      coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π = Set.univ) := by sorry

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
