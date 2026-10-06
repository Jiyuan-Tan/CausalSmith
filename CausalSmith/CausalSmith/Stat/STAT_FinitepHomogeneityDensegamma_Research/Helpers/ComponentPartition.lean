module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentBounds

/-! The full observation components form a partition of the record indices. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Sharing an undisclosed fine coefficient is a symmetric relation. [This is the stated conclusion](goal). -/
-- @node: componentEdge_symm
lemma componentEdge_symm (n K M : ℕ) (aug : Augmentation n K) {i j : Fin n}
    (h : componentEdge n K M aug i j) : componentEdge n K M aug j i := by
  rcases h with ⟨hc, hf | ⟨hf, hb⟩⟩
  · exact ⟨hc.symm, Or.inl hf.symm⟩
  · exact ⟨hc.symm, Or.inr ⟨hf.symm, by simpa only [max_comm] using hb⟩⟩

/-- Connectivity is symmetric because every generating edge can be reversed. [This is the stated conclusion](goal). -/
-- @node: component_connected_symm
lemma component_connected_symm (n K M : ℕ) (aug : Augmentation n K) {i j : Fin n}
    (h : Relation.ReflTransGen (componentEdge n K M aug) i j) :
    Relation.ReflTransGen (componentEdge n K M aug) j i := by
  induction h with
  | refl => exact .refl
  | tail h he ih => exact (Relation.ReflTransGen.single (componentEdge_symm n K M aug he)).trans ih

/-- Component membership is exactly connectivity, including its reflexive case. [This is the stated conclusion](goal). -/
-- @node: mem_componentOf_iff
lemma mem_componentOf_iff (n K M : ℕ) (aug : Augmentation n K) (i j : Fin n) :
    j ∈ componentOf n K M aug i ↔ Relation.ReflTransGen (componentEdge n K M aug) i j := by
  classical
  simp [componentOf]

/-- Every record belongs to its own component. [This is the stated conclusion](goal). -/
-- @node: self_mem_componentOf
lemma self_mem_componentOf (n K M : ℕ) (aug : Augmentation n K) (i : Fin n) :
    i ∈ componentOf n K M aug i :=
  (mem_componentOf_iff n K M aug i i).mpr .refl

/-- Connected records enumerate the same complete component. [This is the stated conclusion](goal). -/
-- @node: componentOf_eq_of_connected
lemma componentOf_eq_of_connected (n K M : ℕ) (aug : Augmentation n K) {i j : Fin n}
    (h : Relation.ReflTransGen (componentEdge n K M aug) i j) :
    componentOf n K M aug i = componentOf n K M aug j := by
  classical
  ext k
  simp only [mem_componentOf_iff]
  exact ⟨fun hik => (component_connected_symm n K M aug h).trans hik, fun hjk => h.trans hjk⟩

/-- Distinct enumerated components cannot share an observation. [This is the stated conclusion](goal). -/
-- @node: components_pairwise_disjoint
lemma components_pairwise_disjoint (n K M : ℕ) (aug : Augmentation n K) :
    (↑(components n K M aug) : Set (Finset (Fin n))).PairwiseDisjoint id := by
  classical
  intro C hC D hD hne
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
  apply Finset.disjoint_left.mpr
  intro k hik hjk
  have hi := (mem_componentOf_iff n K M aug i k).mp hik
  have hj := (mem_componentOf_iff n K M aug j k).mp hjk
  exact hne (componentOf_eq_of_connected n K M aug
    (hi.trans (component_connected_symm n K M aug hj)))

/-- The components cover all observations, without imposing an occupancy cutoff. [This is the stated conclusion](goal). -/
-- @node: components_biUnion_eq_univ
lemma components_biUnion_eq_univ (n K M : ℕ) (aug : Augmentation n K) :
    (components n K M aug).biUnion id = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro i
  exact Finset.mem_biUnion.mpr ⟨componentOf n K M aug i,
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, self_mem_componentOf n K M aug i⟩

/-- A product over all records factors exactly over their disjoint components. [This is the stated conclusion](goal). -/
-- @node: prod_records_eq_prod_components
lemma prod_records_eq_prod_components (n K M : ℕ) (aug : Augmentation n K)
    (f : Fin n → ℝ) :
    (∏ i, f i) = ∏ C ∈ components n K M aug, ∏ i ∈ C, f i := by
  classical
  simpa only [components_biUnion_eq_univ, id_eq] using
    (Finset.prod_biUnion (f := f) (components_pairwise_disjoint n K M aug))

/-- A record determines uniquely which enumerated component contains it. This statement assumes [the hC condition](hyp:hC), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: componentOf_eq_of_mem
lemma componentOf_eq_of_mem (n K M : ℕ) (aug : Augmentation n K)
    {C : Finset (Fin n)} (hC : C ∈ components n K M aug) {i : Fin n} (hi : i ∈ C) :
    componentOf n K M aug i = C := by
  classical
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
  exact (componentOf_eq_of_connected n K M aug ((mem_componentOf_iff n K M aug j i).mp hi)).symm

/-- Connectivity preserves the coarse cell because every generating edge stays in that cell. [This is the stated conclusion](goal). -/
-- @node: component_connected_coarseIndex
lemma component_connected_coarseIndex (n K M : ℕ) (aug : Augmentation n K)
    {i j : Fin n} (h : Relation.ReflTransGen (componentEdge n K M aug) i j) :
    fineIndex M (aug.1 i) = fineIndex M (aug.1 j) := by
  induction h with
  | refl => rfl
  | tail h he ih => exact ih.trans he.1

/-- All records in one actual component have the same coarse cell, including boundary components. This statement assumes [the hC condition](hyp:hC), [the hi condition](hyp:hi), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: component_coarseIndex_eq
lemma component_coarseIndex_eq (n K M : ℕ) (aug : Augmentation n K)
    {C : Finset (Fin n)} (hC : C ∈ components n K M aug)
    {i j : Fin n} (hi : i ∈ C) (hj : j ∈ C) :
    fineIndex M (aug.1 i) = fineIndex M (aug.1 j) := by
  have he := componentOf_eq_of_mem n K M aug hC hi
  rw [← he] at hj
  exact component_connected_coarseIndex n K M aug
    ((mem_componentOf_iff n K M aug i j).mp hj)

/-- The supremum used to name a component's coarse-sign pair equals the pair of every record it contains; no extra sign is disclosed or introduced by this ownership map. This statement assumes [the hC condition](hyp:hC), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: pairIndex_eq_of_mem_component
lemma pairIndex_eq_of_mem_component (n K M : ℕ) (aug : Augmentation n K)
    {C : Finset (Fin n)} (hC : C ∈ components n K M aug)
    {i : Fin n} (hi : i ∈ C) :
    pairIndex M aug C = fineIndex M (aug.1 i) / 2 := by
  unfold pairIndex
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (congrArg (fun k : ℕ => k / 2)
      (component_coarseIndex_eq n K M aug hC hj hi)).le
  · exact Finset.le_sup (f := fun j => fineIndex M (aug.1 j) / 2) hi

/-- Independent fair record labels normalize any record-wise product across the partition. This statement assumes [the r condition](hyp:r), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: component_partition_label_sum
lemma component_partition_label_sum (n K M : ℕ) (aug : Augmentation n K)
    (r : {C // C ∈ components n K M aug} → Fin n → Bool × Bool → ℝ)
    (hr : ∀ C i, ∑ label, r C i label = 4) :
    (∑ labels : Labels n, ∏ C : {C // C ∈ components n K M aug},
      ∏ i ∈ C.val, r C i (labels i)) = (4:ℝ)^n := by
  classical
  let owner (i : Fin n) : {C // C ∈ components n K M aug} :=
    ⟨componentOf n K M aug i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have ho (C : {C // C ∈ components n K M aug}) (i : Fin n) (hi : i ∈ C.val) :
      owner i = C := Subtype.ext (componentOf_eq_of_mem n K M aug C.property hi)
  have hp (labels : Labels n) :
      (∏ C : {C // C ∈ components n K M aug}, ∏ i ∈ C.val, r C i (labels i)) =
        ∏ i, r (owner i) i (labels i) := by
    calc
      _ = ∏ C : {C // C ∈ components n K M aug}, ∏ i ∈ C.val,
          r (owner i) i (labels i) := by
        apply Finset.prod_congr rfl
        intro C _
        apply Finset.prod_congr rfl
        intro i hi
        rw [ho C i hi]
      _ = _ := by
        exact (Finset.prod_coe_sort (components n K M aug)
          (fun C => ∏ i ∈ C, r (owner i) i (labels i))).trans
          (prod_records_eq_prod_components n K M aug (fun i => r (owner i) i (labels i))).symm
  simp_rw [hp]
  rw [← Fintype.prod_sum]
  simp_rw [hr]
  simp

/-- Arbitrary normalized finite coefficient mixtures can be chosen independently in each component without changing total mass on the fair full-label alphabet. This statement assumes [the w condition](hyp:w), [the r condition](hyp:r), [the hw condition](hyp:hw), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: component_partition_mixture_sum
lemma component_partition_mixture_sum (n K M : ℕ) (aug : Augmentation n K)
    {T : Type*} [Fintype T]
    (w : {C // C ∈ components n K M aug} → T → ℝ)
    (r : {C // C ∈ components n K M aug} → T → Fin n → Bool × Bool → ℝ)
    (hw : ∀ C, ∑ t, w C t = 1) (hr : ∀ C t i, ∑ label, r C t i label = 4) :
    (∑ labels : Labels n, ∏ C : {C // C ∈ components n K M aug},
      ∑ t, w C t * ∏ i ∈ C.val, r C t i (labels i)) = (4:ℝ)^n := by
  classical
  have hexp (labels : Labels n) := Fintype.prod_sum
    (fun (C : {C // C ∈ components n K M aug}) t =>
      w C t * ∏ i ∈ C.val, r C t i (labels i))
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [Finset.prod_mul_distrib, ← Finset.mul_sum]
  have hsum (ts : {C // C ∈ components n K M aug} → T) :=
    component_partition_label_sum n K M aug
      (fun C i label => r C (ts C) i label) (fun C i => hr C (ts C) i)
  simp_rw [hsum]
  rw [← Finset.sum_mul, ← Fintype.prod_sum]
  simp_rw [hw]
  simp

end CausalSmith.Stat.FinitepHomogeneityDensegamma
