import Causalean.Graph.FiniteDensity.Coordinate
import Causalean.Graph.FiniteDensity.Elimination

/-!
# Nonancestor marginal invariance for finite DAG product densities

This module turns reverse-topological density elimination into equality of measures.  Replacing
one normalized conditional density by a normalized parent-independent density preserves the
marginal on every parent-closed set omitting the target, hence on the ancestral closure of every
distinct node of which the target is not an ancestor.  Measurable functions determined by that
closure consequently have identical pushforward laws.
-/

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

/-- A [DAG factorization](hyp:B) determines [its observational product measure](goal). -/
def Factorization.observationalMeasure (B : Factorization G X μ) : Measure (∀ i, X i) :=
  (Measure.pi μ).withDensity B.observationalDensity

/-- A [DAG factorization](hyp:B), an [intervention target](hyp:j), and a [normalized replacement
density](hyp:q) determine [the corresponding single-target interventional product measure](goal). -/
def Factorization.interventionMeasure (B : Factorization G X μ) (j : V)
    (q : InterventionDensity j X μ) : Measure (∀ i, X i) :=
  (Measure.pi μ).withDensity (B.interventionDensity j q)

/-- A [finite DAG](hyp:G) and a [node](hyp:i) determine [the node's ancestral closure, including
the node and all strict ancestors](goal). -/
def nodeAncestralClosure (G : Causalean.DAG V) (i : V) : Finset V :=
  insert i (G.ancestors i)

/-- A [queried node](hyp:i) and a [candidate node](hyp:j) [satisfy ancestral-closure membership
exactly when the candidate is the queried node or an ancestor of it](goal). -/
theorem mem_nodeAncestralClosure_iff {i j : V} :
    j ∈ nodeAncestralClosure G i ↔ j = i ∨ G.isAncestor j i := by
  -- Unfold the closure and the graph's `ancestors` membership characterization.
  simp only [nodeAncestralClosure, Finset.mem_insert, G.mem_ancestors]

/-- A [node](hyp:i) [has an ancestral closure that contains every parent of each of its nodes](goal). -/
theorem parentClosed_nodeAncestralClosure (i : V) :
    ParentClosed G (nodeAncestralClosure G i) := by
  -- A parent of `i` is an ancestor; a parent of an ancestor reaches `i` by transitivity.
  intro k hk l hl
  rw [mem_nodeAncestralClosure_iff] at hk ⊢
  rcases hk with rfl | hki
  · exact Or.inr (G.mem_ancestors.mp (G.parents_subset_ancestors k hl))
  · exact Or.inr (G.isAncestor_trans
      (G.mem_ancestors.mp (G.parents_subset_ancestors k hl)) hki)

/-- A [node](hyp:i) [and all of its parents belong to that node's ancestral closure](goal). -/
theorem selfParents_subset_nodeAncestralClosure (i : V) :
    insert i (G.parents i) ⊆ nodeAncestralClosure G i := by
  -- Combine self-membership with `G.parents_subset_ancestors i`.
  intro j hj
  rw [mem_nodeAncestralClosure_iff]
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact Or.inl rfl
  · exact Or.inr (G.mem_ancestors.mp (G.parents_subset_ancestors i hj))

/-- A [DAG factorization](hyp:B), a [parent-closed retained set](hyp:hA), an [intervention target
outside that set](hyp:hj), and a [normalized replacement density](hyp:q) [give identical
observational and interventional marginals on the retained set](goal). -/
theorem Factorization.parentClosed_marginal_eq
    (B : Factorization G X μ) {A : Finset V} (hA : ParentClosed G A)
    {j : V} (hj : j ∉ A) (q : InterventionDensity j X μ) :
    Measure.map (coordinateProjection (X := X) A) B.observationalMeasure =
      Measure.map (coordinateProjection (X := X) A) (B.interventionMeasure j q) := by
  -- Apply the coordinate-density bridge to the two complement-marginal elimination identities.
  apply map_coordinateProjection_withDensity_eq_of_lmarginal_eq A
    B.measurable_observationalDensity (B.measurable_interventionDensity j q)
  rw [B.lmarginal_compl_observationalDensity_eq hA,
    B.lmarginal_compl_interventionDensity_eq hA hj q]

/-- A [DAG factorization](hyp:B), [distinct intervention and queried nodes](hyp:hji), evidence
that [the intervention target is not an ancestor of the queried node](hyp:hnotAncestor), and a
[normalized replacement density](hyp:q) [give identical observational and interventional laws on
the queried node's ancestral closure](goal). -/
theorem Factorization.ancestralMarginal_eq
    (B : Factorization G X μ) {i j : V} (hji : j ≠ i)
    (hnotAncestor : ¬ G.isAncestor j i) (q : InterventionDensity j X μ) :
    Measure.map (coordinateProjection (X := X) (nodeAncestralClosure G i))
        B.observationalMeasure =
      Measure.map (coordinateProjection (X := X) (nodeAncestralClosure G i))
        (B.interventionMeasure j q) := by
  -- Instantiate parent-closed marginal equality and discharge target omission by the
  -- membership iff.
  apply B.parentClosed_marginal_eq (parentClosed_nodeAncestralClosure i) ?_ q
  rw [mem_nodeAncestralClosure_iff]
  exact fun h ↦ h.elim hji hnotAncestor

/-- A [DAG factorization](hyp:B), [distinct intervention and queried nodes](hyp:hji), evidence
that [the intervention target is not an ancestor of the queried node](hyp:hnotAncestor), a
[normalized replacement density](hyp:q), a [measurable outcome map](hyp:f,hf), its [dependence
only on the queried node's ancestral closure](hyp:hdepends), and an [anchor assignment](hyp:x₀)
[give the same observational and interventional outcome law](goal). -/
theorem Factorization.map_eq_of_dependsOn_nodeAncestralClosure
    (B : Factorization G X μ) {i j : V} (hji : j ≠ i)
    (hnotAncestor : ¬ G.isAncestor j i) (q : InterventionDensity j X μ)
    {Y : Type*} [MeasurableSpace Y] (f : (∀ k, X k) → Y)
    (hf : Measurable f) (hdepends : DependsOn (nodeAncestralClosure G i) f)
    (x₀ : ∀ k, X k) :
    Measure.map f B.observationalMeasure = Measure.map f (B.interventionMeasure j q) := by
  -- Transport ancestral projection equality through the coordinate extension representation
  -- of `f`.
  exact map_eq_of_map_coordinateProjection_eq x₀ hf hdepends
    (B.ancestralMarginal_eq hji hnotAncestor q)

/-- A [DAG factorization](hyp:B), [distinct intervention and ratio nodes](hyp:hji), evidence that
[the intervention target is not an ancestor of the ratio node](hyp:hnotAncestor), a [normalized
replacement density](hyp:q), a [node-coordinate numerator](hyp:numerator), [measurability of the
resulting ratio](hyp:hratio), and an [anchor assignment](hyp:x₀) [give the same observational and
interventional law for the canonical density ratio](goal). -/
theorem Factorization.targetRatio_map_eq
    (B : Factorization G X μ) {i j : V} (hji : j ≠ i)
    (hnotAncestor : ¬ G.isAncestor j i) (q : InterventionDensity j X μ)
    (numerator : X i → ℝ≥0∞)
    (hratio : Measurable (fun v : ∀ k, X k ↦ numerator (v i) / B.factor i v))
    (x₀ : ∀ k, X k) :
    Measure.map (fun v : ∀ k, X k ↦ numerator (v i) / B.factor i v)
        B.observationalMeasure =
      Measure.map (fun v : ∀ k, X k ↦ numerator (v i) / B.factor i v)
        (B.interventionMeasure j q) := by
  -- Enlarge `targetRatio_dependsOn` to the ancestral closure, then use the dependent-map theorem.
  apply B.map_eq_of_dependsOn_nodeAncestralClosure hji hnotAncestor q
    (fun v : ∀ k, X k ↦ numerator (v i) / B.factor i v) hratio _ x₀
  exact (B.targetRatio_dependsOn i numerator).mono
    (selfParents_subset_nodeAncestralClosure i)

/-- A [DAG factorization](hyp:B), [distinct intervention and queried nodes](hyp:hji), evidence
that [the intervention target is not an ancestor of the queried node](hyp:hnotAncestor), a
[normalized replacement density](hyp:q), and a [measurable map of the ancestral subproduct](hyp:mix,hmix)
[give the same observational and interventional law after that map](goal). -/
theorem Factorization.map_ancestralProjection_eq
    (B : Factorization G X μ) {i j : V} (hji : j ≠ i)
    (hnotAncestor : ¬ G.isAncestor j i) (q : InterventionDensity j X μ)
    {Y : Type*} [MeasurableSpace Y]
    (mix : (∀ k : nodeAncestralClosure G i, X k) → Y) (hmix : Measurable mix) :
    Measure.map (mix ∘ coordinateProjection (X := X) (nodeAncestralClosure G i))
        B.observationalMeasure =
      Measure.map (mix ∘ coordinateProjection (X := X) (nodeAncestralClosure G i))
        (B.interventionMeasure j q) := by
  -- Use `Measure.map_map` on both sides of `ancestralMarginal_eq`.
  exact map_comp_eq_of_map_eq
    (measurable_coordinateProjection (X := X) (nodeAncestralClosure G i)) hmix
    (B.ancestralMarginal_eq hji hnotAncestor q)

end Causalean.Graph.FiniteDensity

/-!
# Finiteness of a normalized finite-DAG density law

This section records the measure-theoretic finiteness consequence of pointwise normalization of
all local factors. It supplies the `IsFiniteMeasure` instance required by Mathlib's
`CondIndepFun` API without making conditional independence part of the factorization interface.
-/

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

/-- The [observational density of a normalized finite DAG factorization](hyp:B) [has finite
integral against the product reference measure](goal). -/
theorem Factorization.lintegral_observationalDensity_lt_top
    (B : Factorization G X μ) :
    ∫⁻ x, B.observationalDensity x ∂Measure.pi μ < ∞ := by
  /-
  Evaluate `B.lmarginal_compl_observationalDensity_eq` at the empty retained set after splitting
  on whether the full dependent product `∀ i, X i` is empty.  In the inhabited case, evaluate
  the all-coordinate marginal at an anchor assignment and rewrite it as the full lintegral.  In
  the empty case the product measure, hence the integral, is zero.  Do not assume coordinate
  nonemptiness.
  -/
  classical
  by_cases h : Nonempty (∀ i, X i)
  · let x : ∀ i, X i := Classical.choice h
    have hmarg := B.lmarginal_compl_observationalDensity_eq (A := ∅) (by
      intro i hi
      simp at hi)
    have hlin : ∫⁻ v, B.observationalDensity v ∂Measure.pi μ = 1 := by
      rw [MeasureTheory.lintegral_eq_lmarginal_univ x]
      simpa [Factorization.partialDensity] using congrFun hmarg x
    rw [hlin]
    exact ENNReal.one_lt_top
  · let _ : IsEmpty (∀ i, X i) := not_nonempty_iff.mp h
    rw [MeasureTheory.lintegral_of_isEmpty]
    exact ENNReal.zero_lt_top

/-- The [observational measure induced by a normalized finite DAG factorization](hyp:B) [is a
finite measure](goal). -/
noncomputable instance Factorization.instIsFiniteMeasureObservationalMeasure
    (B : Factorization G X μ) : IsFiniteMeasure B.observationalMeasure := by
  rw [Factorization.observationalMeasure]
  exact isFiniteMeasure_withDensity
    (ne_of_lt B.lintegral_observationalDensity_lt_top)

end Causalean.Graph.FiniteDensity
