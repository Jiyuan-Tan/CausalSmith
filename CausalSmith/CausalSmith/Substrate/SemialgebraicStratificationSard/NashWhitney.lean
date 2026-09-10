import CausalSmith.Substrate.SemialgebraicStratificationSard.DimensionBoundary

/-!
# Nash manifolds and finite Whitney stratifications

This file supplies extrinsic definitions for Nash submanifolds of a finite real coordinate space,
their tangent vectors, Whitney conditions (a) and (b), and finite compatible stratifications.
Local Nash charts are explicitly semialgebraic and smooth; no manifold existence is hidden in a
typeclass or in the meaning of “Nash”.
-/

open Set Filter Metric
open scoped Topology

namespace CausalSmith.SemialgebraicStratificationSard

/-- A vector is tangent to a subset at a point when it is the derivative at zero of a differentiable
curve that lies in the subset near zero and passes through the point. -/
def tangentVectors {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) (x : ι → ℝ) :
    Set (ι → ℝ) :=
  {v | ∃ γ : ℝ → (ι → ℝ), γ 0 = x ∧ (∀ᶠ t in 𝓝 0, γ t ∈ s) ∧ HasDerivAt γ v 0}

/-- A semialgebraic subset is a `k`-dimensional Nash submanifold when every point admits mutually
inverse local semialgebraic smooth coordinates from an open subset of `ℝ^k`, with injective chart
derivative. -/
def IsNashManifold {ι : Type*} [Fintype ι] (k : ℕ) (s : Set (ι → ℝ)) : Prop :=
  IsSemialgebraic s ∧ s.Nonempty ∧
    ∀ x ∈ s, ∃ (U : Set (Fin k → ℝ)) (V : Set (ι → ℝ))
      (φ : (Fin k → ℝ) → (ι → ℝ)) (ψ : (ι → ℝ) → (Fin k → ℝ)) (y : Fin k → ℝ),
      IsOpen U ∧ IsSemialgebraic U ∧ IsOpen V ∧ IsSemialgebraic V ∧ y ∈ U ∧ x ∈ V ∧
      φ y = x ∧ φ '' U = s ∩ V ∧ MapsTo ψ (s ∩ V) U ∧
      (∀ z ∈ U, ψ (φ z) = z) ∧ (∀ z ∈ s ∩ V, φ (ψ z) = z) ∧
      ContDiffOn ℝ ⊤ φ U ∧ ContDiffOn ℝ ⊤ ψ V ∧
      IsSemialgebraicMap U φ ∧ IsSemialgebraicMap V ψ ∧
      Function.Injective (fderiv ℝ φ y)

/-- A map is Nash on a semialgebraic domain when locally along that domain it agrees with a smooth
map whose restricted graph over a semialgebraic open neighborhood is semialgebraic. -/
def IsNashOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  ∀ x ∈ s, ∃ (U : Set (ι → ℝ)) (g : (ι → ℝ) → (κ → ℝ)),
    IsOpen U ∧ IsSemialgebraic U ∧ x ∈ U ∧ ContDiffOn ℝ ⊤ g U ∧
      IsSemialgebraicMap U g ∧ EqOn f g (s ∩ U)

/-- The whole finite real coordinate space is a Nash manifold of its ambient dimension. -/
theorem isNashManifold_univ {ι : Type*} [Fintype ι] :
    IsNashManifold (Fintype.card ι) (Set.univ : Set (ι → ℝ)) := by
  sorry

/-- A Nash manifold has semialgebraic dimension equal to its manifold dimension. -/
theorem IsNashManifold.semialgebraicDim_eq {ι : Type*} [Fintype ι]
    {k : ℕ} {s : Set (ι → ℝ)} (hs : IsNashManifold k s) :
    semialgebraicDim s = (k : ℤ) := by
  sorry

/-- Whitney condition (a), in sequential gap form: tangent vectors to the lower stratum at an
incident point become arbitrarily close to tangent spaces of the upper stratum. -/
def WhitneyA {ι : Type*} [Fintype ι] (upper lower : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ lower ∩ closure upper, ∀ y : ℕ → (ι → ℝ),
    (∀ n, y n ∈ upper) → Tendsto y atTop (𝓝 x) →
      ∀ v ∈ tangentVectors lower x,
        Tendsto (fun n => infDist v (tangentVectors upper (y n))) atTop (𝓝 0)

/-- Whitney condition (b), in sequential form: limiting secant directions between incident strata
become tangent to the upper stratum. -/
def WhitneyB {ι : Type*} [Fintype ι] (upper lower : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ lower ∩ closure upper, ∀ y z : ℕ → (ι → ℝ),
    (∀ n, y n ∈ upper) → (∀ n, z n ∈ lower) → (∀ n, y n ≠ z n) →
      Tendsto y atTop (𝓝 x) → Tendsto z atTop (𝓝 x) →
      Tendsto (fun n => infDist ((‖z n - y n‖)⁻¹ • (z n - y n))
        (tangentVectors upper (y n))) atTop (𝓝 0)

/-- A Whitney pair satisfies both Whitney conditions (a) and (b). -/
def IsWhitneyPair {ι : Type*} [Fintype ι]
    (upper lower : Set (ι → ℝ)) : Prop := WhitneyA upper lower ∧ WhitneyB upper lower

/-- A finite Nash Whitney stratification partitions its target into nonempty Nash manifolds,
satisfies the frontier condition with dimension drop, and satisfies Whitney (a) and (b) along every
incident pair. -/
structure NashWhitneyStratification {ι : Type*} [Fintype ι]
    (target : Set (ι → ℝ)) where
  /-- The finite number of strata. -/
  count : ℕ
  /-- The strata of the partition. -/
  stratum : Fin count → Set (ι → ℝ)
  /-- The manifold dimension of each stratum. -/
  dim : Fin count → ℕ
  covers : (⋃ i, stratum i) = target
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (stratum i) (stratum j)
  nash : ∀ i, IsNashManifold (dim i) (stratum i)
  frontier_condition : ∀ i j, i ≠ j → (stratum j ∩ closure (stratum i)).Nonempty →
    stratum j ⊆ frontier (stratum i) ∧ dim j < dim i
  whitney : ∀ i j, i ≠ j → (stratum j ∩ closure (stratum i)).Nonempty →
    IsWhitneyPair (stratum i) (stratum j)

/-- A stratification is compatible with a set when every stratum is either contained in that set or
disjoint from it. -/
def NashWhitneyStratification.Compatible {ι : Type*} [Fintype ι]
    {target : Set (ι → ℝ)} (W : NashWhitneyStratification target)
    (s : Set (ι → ℝ)) : Prop :=
  ∀ i, W.stratum i ⊆ s ∨ Disjoint (W.stratum i) s

/-- **Finite semialgebraic Whitney stratification.** Every finite family of semialgebraic sets has a
finite Nash Whitney stratification of its union compatible with every member of the family
(Bochnak--Coste--Roy, Theorem 9.7.11, with finite-family refinement). -/
theorem exists_compatible_nashWhitneyStratification {ι : Type*} [Fintype ι] {m : ℕ}
    (sets : Fin m → Set (ι → ℝ)) (hsets : ∀ i, IsSemialgebraic (sets i)) :
    ∃ W : NashWhitneyStratification (⋃ i, sets i), ∀ i, W.Compatible (sets i) := by
  -- The finite-family form should be proved during the inductive Whitney stratification
  -- construction, so compatibility is preserved at each refinement; merely intersecting strata
  -- afterwards does not automatically preserve the frontier and Whitney conditions.
  sorry

/-- Every semialgebraic set admits a finite Nash Whitney stratification. -/
theorem exists_nashWhitneyStratification {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    Nonempty (NashWhitneyStratification s) := by
  let sets : Fin 1 → Set (ι → ℝ) := fun _ => s
  obtain ⟨W, _⟩ := exists_compatible_nashWhitneyStratification sets (fun _ => hs)
  have h : (⋃ i, sets i) = s := by
    simp only [sets, Set.iUnion_const]
  exact ⟨h ▸ W⟩

/-- A semialgebraic set and the boundary of another semialgebraic set admit a common finite Nash
Whitney refinement compatible with both. -/
theorem exists_common_refinement_set_frontier {ι : Type*} [Fintype ι]
    {c e : Set (ι → ℝ)} (hc : IsSemialgebraic c) (he : IsSemialgebraic e) :
    ∃ W : NashWhitneyStratification (c ∪ frontier e), W.Compatible c ∧
      W.Compatible (frontier e) := by
  let sets : Fin 2 → Set (ι → ℝ) := ![c, frontier e]
  have hsets : ∀ i, IsSemialgebraic (sets i) := by
    intro i
    fin_cases i
    · exact hc
    · exact he.frontier
  obtain ⟨W, hW⟩ := exists_compatible_nashWhitneyStratification sets hsets
  have htarget : (⋃ i, sets i) = c ∪ frontier e := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Set.mem_iUnion_of_mem 0 hx
      · exact Set.mem_iUnion_of_mem 1 hx
  let W' : NashWhitneyStratification (c ∪ frontier e) :=
    { count := W.count
      stratum := W.stratum
      dim := W.dim
      covers := W.covers.trans htarget
      pairwise_disjoint := W.pairwise_disjoint
      nash := W.nash
      frontier_condition := W.frontier_condition
      whitney := W.whitney }
  refine ⟨W', ?_, ?_⟩
  · simpa [W', sets, NashWhitneyStratification.Compatible] using hW 0
  · simpa [W', sets, NashWhitneyStratification.Compatible] using hW 1

end CausalSmith.SemialgebraicStratificationSard
