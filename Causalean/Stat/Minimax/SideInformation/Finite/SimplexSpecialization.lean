/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.SideInformation.Finite.Main

/-!
# Closed finite-simplex parameter spaces

This module specializes the convergence theorem to model classes represented
as closed subsets of a finite probability simplex, the form used by finite
discrete-law applications.
-/

public section

open Set Filter Topology

namespace Causalean.Stat.Minimax.FiniteSideInformation

variable {I X C : Type*} [Fintype I] [Fintype X] [Fintype C]
  [DecidableEq C] [Nonempty C]

/-- A [closed subset](hyp:hK) of a finite probability simplex is [compact](goal). -/
theorem isCompact_closed_finitePmf {K : Set (FinitePmf I)} (hK : IsClosed K) :
    IsCompact K := by
  -- Proof plan: a closed subset of the compact finite probability simplex is compact.
  exact hK.isCompact

/-- Restricting an [atom coordinate](hyp:i) to a [closed finite-simplex model class](hyp:K)
gives a [continuous parameter coordinate](goal). -/
theorem continuous_closed_finitePmf_coordinate (K : Set (FinitePmf I)) (i : I) :
    Continuous (fun w : K ↦ w.1.1 i) := by
  -- Proof plan: compose subtype-value maps with the continuous atom evaluation map.
  exact (continuous_atom I i).comp continuous_subtype_val

/-- For a [nonempty closed model class inside a finite simplex](hyp:hK,hKne), [finite labeled
and finite nonempty side alphabets](hyp:X,C), [continuous simplex-valid label and side
coordinates](hyp:hp,hq,hpcont,hqcont), and a [continuous bounded target](hyp:htau,hlu,htau_mem),
the [empirical-side minimax values converge to the exact-side benchmark](goal). -/
theorem closedSimplex_finiteSideInfo_minimax_tendsto
    (K : Set (FinitePmf I)) (hK : IsClosed K) (hKne : K.Nonempty)
    (p : K → X → ℝ) (q : K → C → ℝ) (tau : K → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hpcont : ∀ x, Continuous (fun theta ↦ p theta x))
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) (htau : Continuous tau)
    (hlu : l ≤ u) (htau_mem : ∀ theta, tau theta ∈ Set.Icc l u) :
    Tendsto (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) atTop
      (nhds (exactSideMinimaxValue p q hq tau l u)) := by
  -- Proof plan: install compactness and nonemptiness instances on K, then apply the main theorem.
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  letI : Nonempty K := hKne.to_subtype
  exact finiteSideInfo_minimax_tendsto p q tau hp hq hpcont hqcont htau hlu htau_mem

end Causalean.Stat.Minimax.FiniteSideInformation
