import Causalean.Mathlib.Topology.SubsequentialLimits
import Mathlib.Topology.Instances.Real.Lemmas

/-! Stability of cluster sets under asymptotically vanishing perturbations. -/

open Filter Topology

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: clusterValue_iff_mapClusterPt
/-- For a real sequence, [a point is the limit along a strictly increasing
subsequence exactly when it is a mapped cluster point at infinity](goal). -/
lemma clusterValue_iff_mapClusterPt (x : ℕ → ℝ) (a : ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds a)) ↔
      MapClusterPt a atTop x :=
  Causalean.Mathlib.Topology.isSubsequentialLimit_iff_mapClusterPt x a

-- @node: subsequentialLimitSet_nonempty_compact
/-- If [a real sequence is eventually contained in a closed interval](hyp:hx),
then [its set of limits along strictly increasing subsequences is nonempty and
compact](goal). -/
lemma subsequentialLimitSet_nonempty_compact (x : ℕ → ℝ) (a b : ℝ)
    (hx : ∀ᶠ n in atTop, x n ∈ Set.Icc a b) :
    (∃ y : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (x ∘ φ) atTop (nhds y)) ∧
      IsCompact {y : ℝ | ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (x ∘ φ) atTop (nhds y)} :=
  Causalean.Mathlib.Topology.subsequentialLimitSet_nonempty_compact_of_eventually_mem_compact
    x isCompact_Icc hx

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
