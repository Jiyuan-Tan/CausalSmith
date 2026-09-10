/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Topology.Sequences

/-!
# Subsequential limits

This module relates limits along strictly increasing subsequences to mapped
cluster points and proves compactness of the subsequential-limit set when a
sequence is eventually contained in a compact set.
-/

open Filter Topology

namespace Causalean.Mathlib.Topology

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/-- For [a sequence in a first-countable space](hyp:x), [a point is the limit
along a strictly increasing subsequence exactly when it is a mapped cluster
point at infinity](goal). -/
theorem isSubsequentialLimit_iff_mapClusterPt (x : ℕ → X) (a : X) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds a)) ↔
      MapClusterPt a atTop x := by
  constructor
  · rintro ⟨φ, hφ, hlim⟩
    exact hlim.mapClusterPt.of_comp hφ.tendsto_atTop
  · exact fun h ↦ h.tendsto_subseq

variable [T2Space X]

/-- If [a sequence is eventually contained in a compact set](hyp:hs,hx), then
[its set of limits along strictly increasing subsequences is nonempty and
compact](goal). -/
theorem subsequentialLimitSet_nonempty_compact_of_eventually_mem_compact
    (x : ℕ → X) {s : Set X} (hs : IsCompact s)
    (hx : ∀ᶠ n in atTop, x n ∈ s) :
    (∃ y : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (x ∘ φ) atTop (nhds y)) ∧
      IsCompact {y : X | ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (x ∘ φ) atTop (nhds y)} := by
  obtain ⟨y, _hy, φ, hφ, hy⟩ := hs.tendsto_subseq' hx.frequently
  refine ⟨⟨y, φ, hφ, hy⟩, ?_⟩
  have heq : {y : X | ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (nhds y)} = {y : X | MapClusterPt y atTop x} := by
    ext z
    exact isSubsequentialLimit_iff_mapClusterPt x z
  rw [heq]
  apply hs.of_isClosed_subset
  · simpa only [MapClusterPt] using
      (isClosed_setOfPred_clusterPt (f := Filter.map x atTop))
  · intro z hz
    exact hs.isClosed.mem_of_mapClusterPt hz hx

end Causalean.Mathlib.Topology
