import Causalean.Graph.FiniteDensity.OrderedLocalMarkov.Local
import Causalean.Graph.FiniteDensity.Cube

/-!
# Ordered local Markov property for finite DAG density factorizations

This module derives the arbitrary-conditioning-superset form of the local Markov property and
specializes it to predecessor sets from arbitrary and canonical topological rankings.  It also
exports the unit-cube version using the existing unit-cube reference measure.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [mX : ∀ i, MeasurableSpace (X i)]
  [∀ i, StandardBorelSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

omit [Fintype V] [∀ i, StandardBorelSpace (X i)] in
private theorem comap_coordinateProjection_union_eq_sup (A B : Finset V) :
    MeasurableSpace.comap (coordinateProjection (X := X) (A ∪ B)) inferInstance =
      MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance ⊔
        MeasurableSpace.comap (coordinateProjection (X := X) B) inferInstance := by
  apply le_antisymm
  · apply Measurable.comap_le
    refine (@measurable_pi_iff (∀ j, X j) {j // j ∈ A ∪ B}
      (fun j : {j // j ∈ A ∪ B} ↦ X j.val)
      (MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance ⊔
        MeasurableSpace.comap (coordinateProjection (X := X) B) inferInstance)
      (fun j ↦ mX j.val) (coordinateProjection (X := X) (A ∪ B))).2 ?_
    intro ⟨j, hj⟩
    rcases Finset.mem_union.mp hj with hjA | hjB
    · have hprojA :
          @Measurable (∀ j, X j) (∀ j : A, X j)
            (MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance ⊔
              MeasurableSpace.comap (coordinateProjection (X := X) B) inferInstance)
            inferInstance (coordinateProjection (X := X) A) :=
        Measurable.of_comap_le le_sup_left
      simpa only [coordinateProjection, Function.comp_def] using
        (measurable_pi_apply (⟨j, hjA⟩ : A)).comp hprojA
    · have hprojB :
          @Measurable (∀ j, X j) (∀ j : B, X j)
            (MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance ⊔
              MeasurableSpace.comap (coordinateProjection (X := X) B) inferInstance)
            inferInstance (coordinateProjection (X := X) B) :=
        Measurable.of_comap_le le_sup_right
      simpa only [coordinateProjection, Function.comp_def] using
        (measurable_pi_apply (⟨j, hjB⟩ : B)).comp hprojB
  · apply sup_le <;> apply Measurable.comap_le
    · refine (@measurable_pi_iff (∀ j, X j) A (fun j : A ↦ X j.val)
        (MeasurableSpace.comap
          (coordinateProjection (X := X) (A ∪ B)) inferInstance)
        (fun j ↦ mX j.val) (coordinateProjection (X := X) A)).2 ?_
      intro ⟨j, hjA⟩
      have hprojAB :
          @Measurable (∀ j, X j) (∀ j : ↑(A ∪ B), X j)
            (MeasurableSpace.comap
              (coordinateProjection (X := X) (A ∪ B)) inferInstance)
            inferInstance (coordinateProjection (X := X) (A ∪ B)) :=
        Measurable.of_comap_le le_rfl
      simpa only [coordinateProjection, Function.comp_def] using
        (measurable_pi_apply
          (⟨j, Finset.mem_union_left B hjA⟩ : ↑(A ∪ B))).comp hprojAB
    · refine (@measurable_pi_iff (∀ j, X j) B (fun j : B ↦ X j.val)
        (MeasurableSpace.comap
          (coordinateProjection (X := X) (A ∪ B)) inferInstance)
        (fun j ↦ mX j.val) (coordinateProjection (X := X) B)).2 ?_
      intro ⟨j, hjB⟩
      have hprojAB :
          @Measurable (∀ j, X j) (∀ j : ↑(A ∪ B), X j)
            (MeasurableSpace.comap
              (coordinateProjection (X := X) (A ∪ B)) inferInstance)
            inferInstance (coordinateProjection (X := X) (A ∪ B)) :=
        Measurable.of_comap_le le_rfl
      simpa only [coordinateProjection, Function.comp_def] using
        (measurable_pi_apply
          (⟨j, Finset.mem_union_right A hjB⟩ : ↑(A ∪ B))).comp hprojAB

/-- For a [finite DAG density factorization](hyp:B), a [parent-closed block omitting a
vertex](hyp:hP,hi), and a [conditioning subset of that block containing every parent](hyp:hAP,hpa),
[the vertex coordinate is conditionally independent of all remaining block coordinates given the
chosen conditioning coordinates](goal). -/
theorem Factorization.localMarkovSuperset_of_parentClosed
    (B : Factorization G X μ) {i : V} {P A : Finset V}
    (hP : ParentClosed G P) (hi : i ∉ P)
    (hAP : A ⊆ P) (hpa : G.parents i ⊆ A) :
    CondIndepFun
      (MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance)
      (coordinateConditioning_comap_le (X := X) A)
      (fun x : ∀ j, X j ↦ x i)
      (coordinateProjection (X := X) (P \ A))
      B.observationalMeasure := by
  /-
  Derive this from `B.localMarkovParents_of_parentClosed hP hi`: decompose its right coordinate
  block using `Y := P \ A`, `W := A \ G.parents i`, and `C := G.parents i`.  The hypotheses give
  `Y ∪ W = P \ C` and `C ∪ W = A`.  Compose the local result with the measurable pair of
  restrictions to `Y` and `W`, then apply `condIndepFun_weak_union_of_prodMk`.  Finally identify
  `comap (coordinateProjection C) ⊔ comap (coordinateProjection W)` with the comap of
  `coordinateProjection A`; the proof of `Causalean.condIndep_valuesProjection_weak_union` is the
  library template for this measurable projection/reassembly step.  No density argument belongs
  here.
  -/
  classical
  let C : Finset V := G.parents i
  let Y : Finset V := P \ A
  let W : Finset V := A \ C
  have hYW : Y ∪ W = P \ C := by
    exact Finset.sdiff_union_sdiff_cancel hAP hpa
  have hCW : C ∪ W = A := by
    exact Finset.union_sdiff_of_subset hpa
  have hYPC : Y ⊆ P \ C := by
    rw [← hYW]
    exact Finset.subset_union_left
  have hWPC : W ⊆ P \ C := by
    rw [← hYW]
    exact Finset.subset_union_right
  let restrictYW : (∀ j : ↑(P \ C), X j) → (∀ j : Y, X j) × (∀ j : W, X j) :=
    fun z ↦
      (fun j ↦ z ⟨j, hYPC j.property⟩,
       fun j ↦ z ⟨j, hWPC j.property⟩)
  have hrestrictYW : Measurable restrictYW := by
    unfold restrictYW
    exact (measurable_pi_iff.mpr fun j ↦ measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun j ↦ measurable_pi_apply _)
  have hpair :
      CondIndepFun
        (MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance)
        (coordinateConditioning_comap_le (X := X) C)
        (fun x : ∀ j, X j ↦ x i)
        (fun x ↦
          (coordinateProjection (X := X) Y x,
           coordinateProjection (X := X) W x))
        B.observationalMeasure := by
    have hbase := B.localMarkovParents_of_parentClosed hP hi
    have hcomp := hbase.comp measurable_id hrestrictYW
    have hrestrict_comp :
        restrictYW ∘ coordinateProjection (X := X) (P \ C) =
          fun x ↦
            (coordinateProjection (X := X) Y x,
             coordinateProjection (X := X) W x) := by
      funext x
      apply Prod.ext <;> funext j <;> rfl
    rw [hrestrict_comp] at hcomp
    simpa only [Function.id_comp] using hcomp
  have hweak :
      CondIndepFun
        (MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance ⊔
          MeasurableSpace.comap (coordinateProjection (X := X) W) inferInstance)
        (sup_le (coordinateConditioning_comap_le (X := X) C)
          (coordinateConditioning_comap_le (X := X) W))
        (fun x : ∀ j, X j ↦ x i)
        (coordinateProjection (X := X) Y)
        B.observationalMeasure :=
    condIndepFun_weak_union_of_prodMk
      (m := MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance)
      (mΩ := inferInstance)
      (coordinateConditioning_comap_le (X := X) C)
      (W := fun x : ∀ j, X j ↦ x i)
      (V := coordinateProjection (X := X) Y)
      (A := coordinateProjection (X := X) W)
      (measurable_pi_apply i)
      (measurable_coordinateProjection Y)
      (measurable_coordinateProjection W)
      hpair
  have hσ :
      MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance ⊔
          MeasurableSpace.comap (coordinateProjection (X := X) W) inferInstance =
        MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance := by
    rw [← comap_coordinateProjection_union_eq_sup (X := X) C W, hCW]
  simpa only [Y, hσ] using hweak

/-- For a [finite DAG density factorization](hyp:B), an [arbitrary topological ranking](hyp:τ),
a [vertex](hyp:i), a [conditioning predecessor set](hyp:A), and [proof that it lies among the
predecessors and contains every parent](hyp:hA,hpa), [the vertex coordinate is conditionally
independent of all other predecessors given that set](goal). -/
theorem Factorization.orderedLocalMarkov
    (B : Factorization G X μ) (τ : TopologicalRanking G) (i : V) (A : Finset V)
    (hA : A ⊆ predecessors τ i) (hpa : G.parents i ⊆ A) :
    CondIndepFun
      (MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance)
      (coordinateConditioning_comap_le (X := X) A)
      (fun x : ∀ j, X j ↦ x i)
      (coordinateProjection (X := X) (predecessors τ i \ A))
      B.observationalMeasure := by
  exact B.localMarkovSuperset_of_parentClosed
    (parentClosed_predecessors τ i) (not_mem_predecessors τ i) hA hpa

/-- For a [finite DAG density factorization](hyp:B), a [vertex](hyp:i), a [conditioning set in
the canonical predecessor block](hyp:A), and [proof that it is a predecessor subset containing
every parent](hyp:hA,hpa), [the vertex coordinate is conditionally independent of all other
canonical predecessors given that set](goal). -/
theorem Factorization.orderedLocalMarkov_canonical
    (B : Factorization G X μ) (i : V) (A : Finset V)
    (hA : A ⊆ predecessors (canonicalTopologicalRanking G) i)
    (hpa : G.parents i ⊆ A) :
    CondIndepFun
      (MeasurableSpace.comap (coordinateProjection (X := X) A) inferInstance)
      (coordinateConditioning_comap_le (X := X) A)
      (fun x : ∀ j, X j ↦ x i)
      (coordinateProjection (X := X)
        (predecessors (canonicalTopologicalRanking G) i \ A))
      B.observationalMeasure := by
  exact B.orderedLocalMarkov (canonicalTopologicalRanking G) i A hA hpa

/-- The [unit-cube observational density associated with a unit-cube factorization](hyp:B)
[induces a finite measure when combined with the unit-cube reference measure](goal). -/
noncomputable instance UnitCubeFactorization.instIsFiniteMeasureUnitCubeObservational
    (B : UnitCubeFactorization V G) :
    IsFiniteMeasure ((unitCubeReference V).withDensity B.observationalDensity) := by
  have hσ : ∀ _ : V, SigmaFinite unitIntervalReference := fun _ ↦ by
    unfold unitIntervalReference
    infer_instance
  change IsFiniteMeasure B.observationalMeasure
  infer_instance

/-- For a [unit-cube DAG density factorization](hyp:B), an [arbitrary topological ranking](hyp:τ),
a [vertex](hyp:i), a [conditioning predecessor set](hyp:A), and [proof that it lies among the
predecessors and contains every parent](hyp:hA,hpa), [the vertex is conditionally independent of
all remaining predecessors given that set under the unit-cube reference measure](goal). -/
theorem UnitCubeFactorization.orderedLocalMarkov_unitCubeReference
    (B : UnitCubeFactorization V G) (τ : TopologicalRanking G) (i : V) (A : Finset V)
    (hA : A ⊆ predecessors τ i) (hpa : G.parents i ⊆ A) :
    CondIndepFun
      (MeasurableSpace.comap
        (coordinateProjection (X := fun _ : V ↦ ℝ) A) inferInstance)
      (coordinateConditioning_comap_le (X := fun _ : V ↦ ℝ) A)
      (fun x : V → ℝ ↦ x i)
      (coordinateProjection (X := fun _ : V ↦ ℝ) (predecessors τ i \ A))
      ((unitCubeReference V).withDensity B.observationalDensity) := by
  have hσ : ∀ _ : V, SigmaFinite unitIntervalReference := fun _ ↦ by
    unfold unitIntervalReference
    infer_instance
  change CondIndepFun
    (MeasurableSpace.comap
      (coordinateProjection (X := fun _ : V ↦ ℝ) A) inferInstance)
    (coordinateConditioning_comap_le (X := fun _ : V ↦ ℝ) A)
    (fun x : V → ℝ ↦ x i)
    (coordinateProjection (X := fun _ : V ↦ ℝ) (predecessors τ i \ A))
    B.observationalMeasure
  exact @Factorization.orderedLocalMarkov V _ _ (fun _ : V ↦ ℝ) _ _
    (fun _ : V ↦ unitIntervalReference) hσ G B τ i A hA hpa

end Causalean.Graph.FiniteDensity
