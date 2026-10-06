module
public import Causalean.Graph.DSep.OrderedLocalSG
public import Causalean.Graph.Density.FiniteDAG.LocalMarkov.Main
public import Causalean.Stat.FinitePositiveTable.DAG.KernelCI

/-!
# Multiplicative conditional independence and DAG global Markov kernels

This module interprets the DAG ordered-local closure for truncated products and combines that
interpretation with d-separation after arrowhead removal.  The graph-independent finite-kernel
conditional-independence definitions and bridges live in `KernelCI`.
-/

public section

open Finset
open scoped ENNReal

noncomputable section

namespace Causalean.Stat.FinitePositiveTable.DAG

open Causalean.Graph
open Causalean.Graph.FiniteDensity
open Causalean.Mathlib.MeasureTheory.FiniteCoordinate
open Causalean.Mathlib.Probability.Independence.Conditional
open Causalean.Stat.FinitePositiveTable
open MeasureTheory ProbabilityTheory

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

variable {G : DAG V} {p : PositiveTable r}

private theorem comap_coordinateProjection_union_eq_sup
    {X : V → Type*} [mX : ∀ i, MeasurableSpace (X i)] (A B : Finset V) :
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
      intro ⟨j, hj⟩
      have hprojAB :
          @Measurable (∀ j, X j) (∀ j : ↑(A ∪ B), X j)
            (MeasurableSpace.comap
              (coordinateProjection (X := X) (A ∪ B)) inferInstance)
            inferInstance (coordinateProjection (X := X) (A ∪ B)) :=
        Measurable.of_comap_le le_rfl
      simpa only [coordinateProjection, Function.comp_def] using
        (measurable_pi_apply
          (⟨j, Finset.mem_union_left B hj⟩ : ↑(A ∪ B))).comp hprojAB
    · refine (@measurable_pi_iff (∀ j, X j) B (fun j : B ↦ X j.val)
        (MeasurableSpace.comap
          (coordinateProjection (X := X) (A ∪ B)) inferInstance)
        (fun j ↦ mX j.val) (coordinateProjection (X := X) B)).2 ?_
      intro ⟨j, hj⟩
      have hprojAB :
          @Measurable (∀ j, X j) (∀ j : ↑(A ∪ B), X j)
            (MeasurableSpace.comap
              (coordinateProjection (X := X) (A ∪ B)) inferInstance)
            inferInstance (coordinateProjection (X := X) (A ∪ B)) :=
        Measurable.of_comap_le le_rfl
      simpa only [coordinateProjection, Function.comp_def] using
        (measurable_pi_apply
          (⟨j, Finset.mem_union_right A hj⟩ : ↑(A ∪ B))).comp hprojAB

private theorem nonDescendants_parentClosed (H : DAG V) (v : V) :
    ParentClosed H (H.nonDescendants v) := by
  intro i hi j hj
  simp only [DAG.nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hji : H.edge j i := H.mem_parents.mp hj
  constructor
  · intro hvj
    exact hi.1 (H.isAncestor_trans hvj (DAG.isAncestor.edge hji))
  · intro hjv
    subst j
    exact hi.1 (DAG.isAncestor.edge hji)

private theorem observationalMeasure_cylinder_real
    {X : V → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] (H : DAG V)
    (M : PositiveFiniteDAGMechanism H X) (S : Finset V) (x : ∀ i, X i) :
    letI : ∀ i, MeasurableSpace (X i) := fun _ ↦ ⊤
    M.toCountingFactorization.observationalMeasure.real
        (coordinateProjection (X := X) S ⁻¹' {coordinateProjection (X := X) S x}) =
      M.marginalMass S x := by
  letI : ∀ i, MeasurableSpace (X i) := fun _ ↦ ⊤
  have h := M.ofReal_marginalMass_eq_lintegral_indicator S x
  have hset : MeasurableSet
      (coordinateProjection (X := X) S ⁻¹' {coordinateProjection (X := X) S x}) :=
    (measurable_coordinateProjection S) (measurableSet_singleton _)
  rw [show (fun y : (∀ i, X i) ↦
      if coordinateProjection (X := X) S y = coordinateProjection (X := X) S x
      then (1 : ℝ≥0∞) else 0) =
      (coordinateProjection (X := X) S ⁻¹'
        {coordinateProjection (X := X) S x}).indicator (fun _ ↦ (1 : ℝ≥0∞)) by
        funext y
        simp [Set.indicator],
      ] at h
  have hmass : ENNReal.ofReal (M.marginalMass S x) =
      M.toCountingFactorization.observationalMeasure
        (coordinateProjection (X := X) S ⁻¹' {coordinateProjection (X := X) S x}) :=
    h.trans <| (lintegral_congr fun y ↦ by
      by_cases hy : y ∈ coordinateProjection (X := X) S ⁻¹'
          {coordinateProjection (X := X) S x} <;>
        simp [Set.indicator, hy]).trans (lintegral_indicator_one hset)
  unfold Measure.real
  rw [← hmass]
  exact ENNReal.toReal_ofReal (M.marginalMass_pos S x).le

private theorem mechanism_orderedLocalBasis_condIndep
    (H : DAG V) (M : PositiveFiniteDAGMechanism H (fun i ↦ Fin (r i)))
    (fixed R : Finset V) (hR : R = Finset.univ \ fixed)
    (hroot : ∀ f ∈ fixed, H.parents f = ∅)
    {v : V} (hv : v ∈ R) (P : Finset V)
    (hP : P ⊆ R) (hND : P ⊆ H.nonDescendants v)
    (hPa : H.parents v ∩ R ⊆ P) :
    CondIndepFun
      (MeasurableSpace.comap
        (coordinateProjection (X := fun i ↦ Fin (r i))
          (fixed ∪ (H.parents v ∩ R))) inferInstance)
      (coordinateConditioning_comap_le
        (X := fun i ↦ Fin (r i)) (fixed ∪ (H.parents v ∩ R)))
      (coordinateProjection (X := fun i ↦ Fin (r i)) {v})
      (coordinateProjection (X := fun i ↦ Fin (r i))
        (P \ (H.parents v ∩ R)))
      M.toCountingFactorization.observationalMeasure := by
  classical
  letI : ∀ i, MeasurableSpace (Fin (r i)) := fun _ ↦ ⊤
  let A := fixed ∪ (H.parents v ∩ R)
  have hvfixed : v ∉ fixed := by
    rw [hR] at hv
    exact (Finset.mem_sdiff.mp hv).2
  have hfixedND : fixed ⊆ H.nonDescendants v := by
    intro f hf
    simp only [DAG.nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hvf
      exact H.isAncestor_has_parent hvf (hroot f hf)
    · exact fun hfv ↦ hvfixed (hfv ▸ hf)
  have hparentsND : H.parents v ⊆ H.nonDescendants v := by
    intro j hj
    simp only [DAG.nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
    have hjv := H.mem_parents.mp hj
    constructor
    · intro hvj
      exact H.isAncestor_irrefl v
        (H.isAncestor_trans hvj (DAG.isAncestor.edge hjv))
    · intro hjv'
      subst j
      exact H.irrefl v hjv
  have hA : A ⊆ H.nonDescendants v := by
    exact Finset.union_subset hfixedND
      ((Finset.inter_subset_left).trans hparentsND)
  have hpaA : H.parents v ⊆ A := by
    intro j hj
    by_cases hjf : j ∈ fixed
    · exact Finset.mem_union_left _ hjf
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hj, by simpa [hR, hjf]⟩
  have hlocal := M.toCountingFactorization.localMarkovSuperset_of_parentClosed
    (nonDescendants_parentClosed H v)
    (by simp [DAG.nonDescendants]) hA hpaA
  have hright : P \ (H.parents v ∩ R) ⊆ H.nonDescendants v \ A := by
    intro j hj
    have hjP := (Finset.mem_sdiff.mp hj).1
    refine Finset.mem_sdiff.mpr ⟨hND hjP, ?_⟩
    intro hjA
    rcases Finset.mem_union.mp hjA with hjfixed | hjpa
    · have hjR := hP hjP
      rw [hR] at hjR
      exact (Finset.mem_sdiff.mp hjR).2 hjfixed
    · exact (Finset.mem_sdiff.mp hj).2 hjpa
  let restrictRight :
      (∀ j : ↑(H.nonDescendants v \ A), Fin (r j)) →
        (∀ j : ↑(P \ (H.parents v ∩ R)), Fin (r j)) :=
    fun z j ↦ z ⟨j, hright j.property⟩
  have hrestrictRight : Measurable restrictRight := by
    exact measurable_pi_iff.mpr fun j ↦
      measurable_pi_apply (⟨j, hright j.property⟩ : ↑(H.nonDescendants v \ A))
  let singletonOf : Fin (r v) → (∀ j : ({v} : Finset V), Fin (r j)) :=
    fun z j ↦ (Finset.mem_singleton.mp j.property).symm ▸ z
  have hsingletonOf : Measurable singletonOf := measurable_of_finite _
  have hcomp := hlocal.comp hsingletonOf hrestrictRight
  have hleft_eq : singletonOf ∘ (fun x : ∀ j, Fin (r j) ↦ x v) =
      coordinateProjection (X := fun i ↦ Fin (r i)) {v} := by
    funext x j
    rcases j with ⟨j, hj⟩
    simp only [Finset.mem_singleton] at hj
    subst j
    rfl
  have hright_eq : restrictRight ∘
      coordinateProjection (X := fun i ↦ Fin (r i)) (H.nonDescendants v \ A) =
      coordinateProjection (X := fun i ↦ Fin (r i))
        (P \ (H.parents v ∩ R)) := by
    funext x j
    rfl
  simpa only [hleft_eq, hright_eq, A] using hcomp

private theorem projectionCylinder_inter
    {X : V → Type*} (A B : Finset V) (x : ∀ i, X i) :
    (coordinateProjection (X := X) A ⁻¹' {coordinateProjection (X := X) A x}) ∩
        (coordinateProjection (X := X) B ⁻¹' {coordinateProjection (X := X) B x}) =
      coordinateProjection (X := X) (A ∪ B) ⁻¹'
        {coordinateProjection (X := X) (A ∪ B) x} := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hA, hB⟩
    funext j
    rcases Finset.mem_union.mp j.property with hjA | hjB
    · exact congrFun hA ⟨j, hjA⟩
    · exact congrFun hB ⟨j, hjB⟩
  · intro h
    constructor <;> funext j
    · exact congrFun h ⟨j, Finset.mem_union_left B j.property⟩
    · exact congrFun h ⟨j, Finset.mem_union_right A j.property⟩

private theorem fixedKernelCondIndep_of_mechanism
    (H : DAG V) (M : PositiveFiniteDAGMechanism H (fun i ↦ Fin (r i)))
    (hr : ∀ i, 0 < r i) (q : Kernel r) (c : ℝ) (hc : 0 < c)
    (hmarginal : ∀ S x, M.marginalMass S x = c * kernelMarginalMass q S x)
    (fixed X Y Z : Finset V)
    (hci :
      letI : ∀ i, MeasurableSpace (Fin (r i)) := fun _ ↦ ⊤
      CondIndepFun
        (MeasurableSpace.comap
          (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z)) inferInstance)
        (coordinateConditioning_comap_le
          (X := fun i ↦ Fin (r i)) (fixed ∪ Z))
        (coordinateProjection (X := fun i ↦ Fin (r i)) X)
        (coordinateProjection (X := fun i ↦ Fin (r i)) Y)
        M.toCountingFactorization.observationalMeasure) :
    FixedKernelCondIndep q fixed X Y Z := by
  classical
  letI : ∀ i, MeasurableSpace (Fin (r i)) := fun _ ↦ ⊤
  let (i : V) : Nonempty (Fin (r i)) := ⟨⟨0, hr i⟩⟩
  intro x
  have hcross := condIndepFun_finiteAtom_crossProduct
    M.toCountingFactorization.observationalMeasure
    (coordinateProjection (X := fun i ↦ Fin (r i)) X)
    (coordinateProjection (X := fun i ↦ Fin (r i)) Y)
    (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z))
    (measurable_coordinateProjection X)
    (measurable_coordinateProjection Y)
    (measurable_coordinateProjection (fixed ∪ Z)) hci
    (coordinateProjection (X := fun i ↦ Fin (r i)) X x)
    (coordinateProjection (X := fun i ↦ Fin (r i)) Y x)
    (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z) x)
  rw [projectionCylinder_inter X Y x,
    projectionCylinder_inter (X ∪ Y) (fixed ∪ Z) x,
    projectionCylinder_inter X (fixed ∪ Z) x,
    projectionCylinder_inter Y (fixed ∪ Z) x] at hcross
  rw [observationalMeasure_cylinder_real H M,
    observationalMeasure_cylinder_real H M,
    observationalMeasure_cylinder_real H M,
    observationalMeasure_cylinder_real H M] at hcross
  rw [hmarginal, hmarginal, hmarginal, hmarginal] at hcross
  unfold FixedKernelCondIndepAt fixedKernelMarginal
  have hscaled :
      c * c *
          (kernelMarginalMass q (fixed ∪ (X ∪ Y ∪ Z)) x *
            kernelMarginalMass q (fixed ∪ Z) x) =
        c * c *
          (kernelMarginalMass q (fixed ∪ (X ∪ Z)) x *
            kernelMarginalMass q (fixed ∪ (Y ∪ Z)) x) := by
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm,
      mul_assoc, mul_left_comm, mul_comm] using hcross
  exact mul_left_cancel₀ (mul_pos hc hc).ne' hscaled

namespace PositiveDAGTableFactorization

/-- A [factorized table](hyp:fac), [fixed vertex set](hyp:fixed), [remaining vertex](hyp:hv),
[candidate nondescendant set](hyp:P), [proof that it remains random](hyp:hP), [proof that it
contains only nondescendants](hyp:hND), and [proof that it contains the remaining parents](hyp:hPa)
give [the ordered-local fixed-row conditional-independence basis statement](goal). -/
theorem remainingFactorKernel_orderedLocalBasis
    (fac : PositiveDAGTableFactorization G p) (fixed : Finset V)
    {v : V} (hv : v ∈ Finset.univ \ fixed) (P : Finset V)
    (hP : P ⊆ Finset.univ \ fixed)
    (hND : P ⊆ (arrowheadRemovedDAG G fixed).nonDescendants v)
    (hPa : (arrowheadRemovedDAG G fixed).parents v ∩
      (Finset.univ \ fixed) ⊆ P) :
    FixedKernelCondIndep (fac.remainingFactorKernel fixed) fixed
      {v} (P \ ((arrowheadRemovedDAG G fixed).parents v ∩
        (Finset.univ \ fixed)))
      ((arrowheadRemovedDAG G fixed).parents v ∩
        (Finset.univ \ fixed)) := by
  classical
  let (i : V) : Nonempty (Fin (r i)) :=
    ⟨⟨0, fac.cardinalitiesPositive i⟩⟩
  let H := arrowheadRemovedDAG G fixed
  let M : PositiveFiniteDAGMechanism H (fun i ↦ Fin (r i)) :=
    { factor := fun i y ↦
        if i ∈ fixed then (r i : ℝ)⁻¹ else fac.mechanism.factor i y
      factor_pos := by
        intro i y
        split_ifs with hi
        · exact inv_pos.mpr (Nat.cast_pos.mpr (fac.cardinalitiesPositive i))
        · exact fac.mechanism.factor_pos i y
      factor_normalized := by
        intro i y
        by_cases hi : i ∈ fixed
        · simp only [hi, if_pos]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
            (Nat.ne_of_gt (fac.cardinalitiesPositive i)))
        · simp only [hi]
          exact fac.mechanism.factor_normalized i y
      factor_local := by
        intro i y y' hyy'
        by_cases hi : i ∈ fixed
        · simp [hi]
        · simp only [hi]
          apply fac.mechanism.factor_local i
          rw [← arrowheadRemovedDAG_random_parents G fixed hi]
          exact hyy' }
  let c : ℝ := ∏ i ∈ fixed, (r i : ℝ)⁻¹
  have hcpos : 0 < c := by
    exact Finset.prod_pos fun i _ ↦
      inv_pos.mpr (Nat.cast_pos.mpr (fac.cardinalitiesPositive i))
  have hjoint (y : ProfileSpace r) :
      M.jointMass y = c * fac.remainingFactorKernel fixed y := by
    unfold PositiveFiniteDAGMechanism.jointMass remainingFactorKernel c M
    rw [Finset.prod_ite]
    congr 1
    · congr 1
      ext i
      simp
    · congr 1
      ext i
      simp
  have hmarginal (S : Finset V) (a : ProfileSpace r) :
      M.marginalMass S a = c * kernelMarginalMass
        (fac.remainingFactorKernel fixed) S a := by
    unfold PositiveFiniteDAGMechanism.marginalMass kernelMarginalMass fiberSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hjoint]
    by_cases hya : AgreeOn S y a
    · have hp : coordinateProjection (X := fun i ↦ Fin (r i)) S y =
          coordinateProjection (X := fun i ↦ Fin (r i)) S a := by
        funext w
        exact hya w w.property
      simp [hya, hp]
    · have hp : coordinateProjection (X := fun i ↦ Fin (r i)) S y ≠
          coordinateProjection (X := fun i ↦ Fin (r i)) S a := by
        intro hp
        apply hya
        intro w hw
        exact congrFun hp ⟨w, hw⟩
      simp [hya, hp]
  have hci := mechanism_orderedLocalBasis_condIndep H M fixed
    (Finset.univ \ fixed) rfl
    (fun f hf ↦ arrowheadRemovedDAG_fixed_parents_empty G fixed hf)
    hv P hP hND hPa
  exact fixedKernelCondIndep_of_mechanism H M fac.cardinalitiesPositive
    (fac.remainingFactorKernel fixed) c hcpos hmarginal fixed {v}
      (P \ (H.parents v ∩ (Finset.univ \ fixed)))
      (H.parents v ∩ (Finset.univ \ fixed)) (by
        simpa only [H, Finset.union_assoc, Finset.union_left_comm,
          Finset.union_comm] using hci)

/-- A [factorized table](hyp:fac), [fixed and three coordinate sets](hyp:fixed,X,Y,Z), and [an
ordered-local semi-graphoid derivation in the arrowhead-removed DAG](hyp:hsg) give [the
corresponding multiplicative fixed-row conditional independence](goal). -/
theorem remainingFactorKernel_orderedLocalMarkov
    (fac : PositiveDAGTableFactorization G p) (fixed X Y Z : Finset V)
    (hsg : (arrowheadRemovedDAG G fixed).OrderedLocalSG
      (Finset.univ \ fixed) X Y Z) :
    FixedKernelCondIndep (fac.remainingFactorKernel fixed) fixed X Y Z := by
  classical
  let (i : V) : Nonempty (Fin (r i)) :=
    ⟨⟨0, fac.cardinalitiesPositive i⟩⟩
  letI : ∀ i, MeasurableSpace (Fin (r i)) := fun _ ↦ ⊤
  let H := arrowheadRemovedDAG G fixed
  let R := Finset.univ \ fixed
  let M : PositiveFiniteDAGMechanism H (fun i ↦ Fin (r i)) :=
    { factor := fun i y ↦
        if i ∈ fixed then (r i : ℝ)⁻¹ else fac.mechanism.factor i y
      factor_pos := by
        intro i y
        split_ifs with hi
        · exact inv_pos.mpr (Nat.cast_pos.mpr (fac.cardinalitiesPositive i))
        · exact fac.mechanism.factor_pos i y
      factor_normalized := by
        intro i y
        by_cases hi : i ∈ fixed
        · simp only [hi, if_pos]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
            (Nat.ne_of_gt (fac.cardinalitiesPositive i)))
        · simp only [hi]
          exact fac.mechanism.factor_normalized i y
      factor_local := by
        intro i y y' hyy'
        by_cases hi : i ∈ fixed
        · simp [hi]
        · simp only [hi]
          apply fac.mechanism.factor_local i
          rw [← arrowheadRemovedDAG_random_parents G fixed hi]
          exact hyy' }
  let c : ℝ := ∏ i ∈ fixed, (r i : ℝ)⁻¹
  have hcpos : 0 < c := by
    exact Finset.prod_pos fun i _ ↦
      inv_pos.mpr (Nat.cast_pos.mpr (fac.cardinalitiesPositive i))
  have hjoint (y : ProfileSpace r) :
      M.jointMass y = c * fac.remainingFactorKernel fixed y := by
    unfold PositiveFiniteDAGMechanism.jointMass remainingFactorKernel c M
    rw [Finset.prod_ite]
    congr 1
    · congr 1
      ext i
      simp
    · congr 1
      ext i
      simp
  have hmarginal (S : Finset V) (a : ProfileSpace r) :
      M.marginalMass S a = c * kernelMarginalMass
        (fac.remainingFactorKernel fixed) S a := by
    unfold PositiveFiniteDAGMechanism.marginalMass kernelMarginalMass fiberSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hjoint]
    by_cases hya : AgreeOn S y a
    · have hp : coordinateProjection (X := fun i ↦ Fin (r i)) S y =
          coordinateProjection (X := fun i ↦ Fin (r i)) S a := by
        funext w
        exact hya w w.property
      simp [hya, hp]
    · have hp : coordinateProjection (X := fun i ↦ Fin (r i)) S y ≠
          coordinateProjection (X := fun i ↦ Fin (r i)) S a := by
        intro hp
        apply hya
        intro w hw
        exact congrFun hp ⟨w, hw⟩
      simp [hya, hp]
  have hmeasure : ∀ {X Y Z : Finset V}, H.OrderedLocalSG R X Y Z →
      CondIndepFun
        (MeasurableSpace.comap
          (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z)) inferInstance)
        (coordinateConditioning_comap_le
          (X := fun i ↦ Fin (r i)) (fixed ∪ Z))
        (coordinateProjection (X := fun i ↦ Fin (r i)) X)
        (coordinateProjection (X := fun i ↦ Fin (r i)) Y)
        M.toCountingFactorization.observationalMeasure := by
    intro X' Y' Z' h
    induction h with
    | nil Y Z hY hZ =>
        let emptyValue : ∀ j : (∅ : Finset V), Fin (r j) :=
          fun j ↦ False.elim
            ((Finset.notMem_empty j.val : j.val ∉ (∅ : Finset V)) j.property)
        have hempty : coordinateProjection (X := fun i ↦ Fin (r i)) ∅ =
            fun _ ↦ emptyValue := by
          funext x j
          exact False.elim
            ((Finset.notMem_empty j.val : j.val ∉ (∅ : Finset V)) j.property)
        rw [hempty]
        exact condIndepFun_const_left emptyValue _
    | basis v hv P hP hND hPa =>
        exact mechanism_orderedLocalBasis_condIndep H M fixed R rfl
          (fun f hf ↦ arrowheadRemovedDAG_fixed_parents_empty G fixed hf)
          hv P hP hND hPa
    | symm h ih =>
        exact ih.symm
    | @decomp X Y W Z h ih =>
        let restrictY :
            (∀ j : ↑(Y ∪ W), Fin (r j)) → (∀ j : Y, Fin (r j)) :=
          fun z j ↦ z ⟨j, Finset.mem_union_left W j.property⟩
        have hrestrictY : Measurable restrictY := measurable_of_finite _
        have hcomp := ih.comp measurable_id hrestrictY
        have heq : restrictY ∘
            coordinateProjection (X := fun i ↦ Fin (r i)) (Y ∪ W) =
            coordinateProjection (X := fun i ↦ Fin (r i)) Y := by
          funext x j
          rfl
        simpa only [Function.id_comp, heq] using hcomp
    | @weakUnion X Y W Z h ih =>
        let split : (∀ j : ↑(Y ∪ W), Fin (r j)) →
            ((∀ j : Y, Fin (r j)) × (∀ j : W, Fin (r j))) :=
          fun z ↦
            (fun j ↦ z ⟨j, Finset.mem_union_left W j.property⟩,
             fun j ↦ z ⟨j, Finset.mem_union_right Y j.property⟩)
        have hsplit : Measurable split := measurable_of_finite _
        have hp := ih.comp measurable_id hsplit
        have hsplit_eq : split ∘
            coordinateProjection (X := fun i ↦ Fin (r i)) (Y ∪ W) =
            fun x ↦
              (coordinateProjection (X := fun i ↦ Fin (r i)) Y x,
               coordinateProjection (X := fun i ↦ Fin (r i)) W x) := by
          funext x
          rfl
        rw [hsplit_eq] at hp
        have hw := condIndepFun_weak_union_of_prodMk
          (coordinateConditioning_comap_le
            (X := fun i ↦ Fin (r i)) (fixed ∪ Z))
          (measurable_coordinateProjection X)
          (measurable_coordinateProjection Y)
          (measurable_coordinateProjection W) hp
        have hσ :
            MeasurableSpace.comap
                (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z)) inferInstance ⊔
              MeasurableSpace.comap
                (coordinateProjection (X := fun i ↦ Fin (r i)) W) inferInstance =
            MeasurableSpace.comap
              (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ (Z ∪ W)))
                inferInstance := by
          rw [← Finset.union_assoc]
          exact (comap_coordinateProjection_union_eq_sup
            (X := fun i ↦ Fin (r i)) (fixed ∪ Z) W).symm
        simpa only [hσ] using hw
    | @contract X Y W Z h1 h2 ih1 ih2 =>
        have hσ :
            MeasurableSpace.comap
                (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z)) inferInstance ⊔
              MeasurableSpace.comap
                (coordinateProjection (X := fun i ↦ Fin (r i)) W) inferInstance =
            MeasurableSpace.comap
              (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ (Z ∪ W)))
                inferInstance := by
          rw [← Finset.union_assoc]
          exact (comap_coordinateProjection_union_eq_sup
            (X := fun i ↦ Fin (r i)) (fixed ∪ Z) W).symm
        have ih1' : CondIndepFun
            (MeasurableSpace.comap
                (coordinateProjection (X := fun i ↦ Fin (r i)) (fixed ∪ Z)) inferInstance ⊔
              MeasurableSpace.comap
                (coordinateProjection (X := fun i ↦ Fin (r i)) W) inferInstance)
            (sup_le
              (coordinateConditioning_comap_le
                (X := fun i ↦ Fin (r i)) (fixed ∪ Z))
              (measurable_coordinateProjection W).comap_le)
            (coordinateProjection (X := fun i ↦ Fin (r i)) X)
            (coordinateProjection (X := fun i ↦ Fin (r i)) Y)
            M.toCountingFactorization.observationalMeasure := by
          simpa only [hσ] using ih1
        have hp := condIndepFun_contraction_of_prodMk
          (coordinateConditioning_comap_le
            (X := fun i ↦ Fin (r i)) (fixed ∪ Z))
          (measurable_coordinateProjection X)
          (measurable_coordinateProjection Y)
          (measurable_coordinateProjection W) ih1' ih2
        let merge : ((∀ j : Y, Fin (r j)) × (∀ j : W, Fin (r j))) →
            (∀ j : ↑(Y ∪ W), Fin (r j)) :=
          fun z j ↦ if hj : j.val ∈ Y then z.1 ⟨j, hj⟩
            else z.2 ⟨j, (Finset.mem_union.mp j.property).resolve_left hj⟩
        have hmerge : Measurable merge := measurable_of_finite _
        have hcomp := hp.comp measurable_id hmerge
        have hmerge_eq : merge ∘ (fun x ↦
              (coordinateProjection (X := fun i ↦ Fin (r i)) Y x,
               coordinateProjection (X := fun i ↦ Fin (r i)) W x)) =
            coordinateProjection (X := fun i ↦ Fin (r i)) (Y ∪ W) := by
          funext x j
          by_cases hj : j.val ∈ Y <;> simp [merge, hj, coordinateProjection]
        simpa only [Function.id_comp, hmerge_eq] using hcomp
  have hci := hmeasure hsg
  exact fixedKernelCondIndep_of_mechanism H M fac.cardinalitiesPositive
    (fac.remainingFactorKernel fixed) c hcpos hmarginal fixed X Y Z hci

/-- A [factorized table](hyp:fac), [fixed and three coordinate sets](hyp:fixed,X,Y,Z), [proofs
that each random set is remaining](hyp:hX,hY,hZ), and [d-separation after removing incoming arrows
to fixed vertices](hyp:hdSep) give [the atomwise multiplicative fixed-row conditional-independence
identity](goal). -/
theorem remainingFactorKernel_globalMarkov
    (fac : PositiveDAGTableFactorization G p) (fixed X Y Z : Finset V)
    (hX : X ⊆ Finset.univ \ fixed) (hY : Y ⊆ Finset.univ \ fixed)
    (hZ : Z ⊆ Finset.univ \ fixed)
    (hdSep : (arrowheadRemovedDAG G fixed).dSep X Y (Z ∪ fixed)) :
    FixedKernelCondIndep (fac.remainingFactorKernel fixed) fixed X Y Z := by
  apply fac.remainingFactorKernel_orderedLocalMarkov fixed X Y Z
  apply (arrowheadRemovedDAG G fixed).orderedLocalSG_of_dSep_with_fixed
    (Finset.univ \ fixed) X Y Z fixed
  · intro f hf
    exact arrowheadRemovedDAG_fixed_parents_empty G fixed hf
  · exact fixed_disjoint_remaining fixed
  · exact hX
  · exact hY
  · exact hZ
  · exact hdSep

/-- A [factorized table](hyp:fac), [fixed vertex set and two vertices](hyp:fixed,a,b), [random
conditioning set](hyp:Z), [proofs that both vertices remain](hyp:ha,hb), [proof that the
conditioning set remains random](hyp:hZ), and [the d-separation premise](hyp:hdSep) give
[singleton multiplicative fixed-row conditional independence](goal). -/
theorem remainingFactorKernel_singleton_globalMarkov
    (fac : PositiveDAGTableFactorization G p) (fixed : Finset V) (a b : V)
    (Z : Finset V) (ha : a ∉ fixed) (hb : b ∉ fixed)
    (hZ : Z ⊆ Finset.univ \ fixed)
    (hdSep : (arrowheadRemovedDAG G fixed).dSep {a} {b} (Z ∪ fixed)) :
    FixedKernelCondIndep (fac.remainingFactorKernel fixed) fixed {a} {b} Z := by
  exact fac.remainingFactorKernel_globalMarkov fixed {a} {b} Z
    (by simpa) (by simpa) hZ hdSep

end PositiveDAGTableFactorization

end Causalean.Stat.FinitePositiveTable.DAG
