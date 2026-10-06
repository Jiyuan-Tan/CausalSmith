module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentJointLaw
/-! Additive transport costs for the finite product of component couplings. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Pairing two assignments coordinatewise preserves all finite assignments. -/
-- @node: pairedAssignmentEquiv
def pairedAssignmentEquiv (ι α : Type*) :
    ((ι → α) × (ι → α)) ≃ (ι → α × α) where
  toFun zw i := (zw.1 i, zw.2 i)
  invFun v := (fun i => (v i).1, fun i => (v i).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Partition restriction factors array sums over any commutative semiring.  [the theorem's stated inputs and assumptions](hyp:s,hcover,hdisj,s,F), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α,R). -/
-- @node: sum_prod_partition_semiring
lemma sum_prod_partition_semiring {ι α R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [CommSemiring R]
    (s : Finset (Finset ι)) (hcover : ∀ i, ∃ C ∈ s, i ∈ C)
    (hdisj : Set.PairwiseDisjoint (s : Set (Finset ι)) id)
    (F : ∀ C : Finset ι, (C → α) → R) :
    (∑ z : ι → α, ∏ C ∈ s, F C (fun i => z i)) =
      ∏ C ∈ s, ∑ z : C → α, F C z := by
  classical
  let e := partitionRestrictionEquiv (α := α) s hcover hdisj
  calc
    _ = ∑ w : ∀ C : s, ↥(C : Finset ι) → α, ∏ C : s, F C (w C) := by
      apply Fintype.sum_equiv e
      intro z
      exact (Finset.prod_coe_sort s (fun C => F C (fun i => z i))).symm
    _ = _ := by
      rw [← Fintype.prod_sum]
      exact Finset.prod_coe_sort s (fun C => ∑ z : C → α, F C z)

/-- A normalized partition product preserves the expectation of any one block observable.  [the theorem's stated inputs and assumptions](hyp:s,hcover,hdisj,s,F,hF,D,hD,g), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α,R). -/
-- @node: sum_prod_partition_observable
lemma sum_prod_partition_observable {ι α R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [CommSemiring R]
    (s : Finset (Finset ι)) (hcover : ∀ i, ∃ C ∈ s, i ∈ C)
    (hdisj : Set.PairwiseDisjoint (s : Set (Finset ι)) id)
    (F : ∀ C : Finset ι, (C → α) → R)
    (hF : ∀ C ∈ s, ∑ z : C → α, F C z = 1)
    (D : Finset ι) (hD : D ∈ s) (g : (D → α) → R) :
    (∑ z : ι → α, (∏ C ∈ s, F C (fun i => z i)) * g (fun i => z i)) =
      ∑ z : D → α, F D z * g z := by
  classical
  let G (C : Finset ι) (z : C → α) : R :=
    if h : C = D then F D (fun i => z ⟨i, h.symm ▸ i.property⟩) *
      g (fun i => z ⟨i, h.symm ▸ i.property⟩) else F C z
  have hp (z : ι → α) :
      (∏ C ∈ s, G C (fun i => z i)) =
        (∏ C ∈ s, F C (fun i => z i)) * g (fun i => z i) := by
    rw [← Finset.prod_erase_mul _ _ hD, ← Finset.prod_erase_mul _ _ hD]
    have he : (∏ C ∈ s.erase D, G C (fun i => z i)) =
        ∏ C ∈ s.erase D, F C (fun i => z i) := by
      apply Finset.prod_congr rfl
      intro C hC
      simp [G, Finset.ne_of_mem_erase hC]
    rw [he]
    simp [G, mul_assoc]
  simp_rw [← hp]
  rw [sum_prod_partition_semiring s hcover hdisj G, ← Finset.prod_erase_mul _ _ hD]
  have he : (∏ C ∈ s.erase D, ∑ z : C → α, G C z) = 1 := by
    apply Finset.prod_eq_one
    intro C hC
    simpa [G, Finset.ne_of_mem_erase hC] using hF C (Finset.mem_of_mem_erase hC)
  rw [he, one_mul]
  simp [G]

/-- The shared-sign component list partitions any sum over dataset records.  [the theorem's stated inputs and assumptions](hyp:hL,n,x,f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:M). -/
-- @node: orderedComponents_sum_records
lemma orderedComponents_sum_records {M : Type*} [AddCommMonoid M]
    (hL : ℝ) (n : ℕ) (x : Fin n → Covariate) (f : Fin n → M) :
    (∑ i, f i) = ((orderedComponents hL n x).map
      (fun C => ∑ i ∈ C, f i)).sum := by
  classical
  let s := (orderedComponents hL n x).toFinset
  have hc : s.biUnion id = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    obtain ⟨C, hC, hi⟩ := orderedComponents_cover hL n x i
    exact ⟨C, List.mem_toFinset.mpr hC, hi⟩
  have hd : Set.PairwiseDisjoint (s : Set (Finset (Fin n))) id := by
    intro C hC D hD hne
    exact orderedComponents_disjoint hL n x C D
      (List.mem_toFinset.mp hC) (List.mem_toFinset.mp hD) hne
  rw [← hc, Finset.sum_biUnion hd]
  exact List.sum_toFinset _ (orderedComponents_nodup hL n x)

/-- Identical attached covariates make dataset replacements exactly mark replacements.  [the theorem's stated inputs and assumptions](hyp:z,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,x). -/
-- @node: attachMarks_hammingDist
lemma attachMarks_hammingDist (n : ℕ) (x : Fin n → Covariate)
    (z w : Fin n → Bool × Bool) :
    dHam n (attachMarks n x z) (attachMarks n x w) = hammingDist z w := by
  classical
  unfold dHam hammingDist
  congr 1
  ext i
  simp [attachMarks, Prod.ext_iff]

/-- Hamming cost decomposes over the disjoint ordered components.  [the theorem's stated inputs and assumptions](hyp:z,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: hammingDist_orderedComponents
lemma hammingDist_orderedComponents (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (z w : Fin n → Bool × Bool) :
    hammingDist z w = ((orderedComponents hL n x).map
      (fun (C : Finset (Fin n)) => hammingDist (fun i : C => z i) (fun i : C => w i))).sum := by
  classical
  have hc (C : Finset (Fin n)) :
      hammingDist (fun i : C => z i) (fun i : C => w i) =
        ∑ i ∈ C, if z i ≠ w i then 1 else 0 := by
    simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_coe_sort C (fun i => if z i ≠ w i then 1 else 0)
  simp_rw [hc]
  simpa only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter] using
    orderedComponents_sum_records hL n x (fun i => if z i ≠ w i then 1 else 0 : Fin n → ℕ)

/-- Summation over pairs of assignments equals summation over paired coordinates.  [the theorem's stated inputs and assumptions](hyp:f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α,M). -/
-- @node: sum_pairedAssignments
lemma sum_pairedAssignments {ι α M : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [AddCommMonoid M]
    (f : (ι → α) × (ι → α) → M) :
    (∑ zw, f zw) = ∑ v : ι → α × α, f (fun i => (v i).1, fun i => (v i).2) := by
  apply Fintype.sum_equiv (pairedAssignmentEquiv ι α)
  intro zw
  rfl

/-- Each component's paired-coordinate coupling array has total mass one.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentCouplingMass_paired_sum
lemma componentCouplingMass_paired_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∑ v : C → (Bool × Bool) × (Bool × Bool),
      ENNReal.ofReal (componentCouplingMass hL n x C
        (fun i => (v i).1) (fun i => (v i).2))) = 1 := by
  rw [← sum_pairedAssignments (fun zw : Marks C × Marks C =>
    ENNReal.ofReal (componentCouplingMass hL n x C zw.1 zw.2)), Fintype.sum_prod_type]
  have hr (z : Marks C) :
      (∑ w, ENNReal.ofReal (componentCouplingMass hL n x C z w)) =
        ENNReal.ofReal (alternativeMass hL n x C z) := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun w _ => componentCouplingMass_nonneg hL hhL n x C z w),
      componentCouplingMass_row_sum hL hhL]
  simp_rw [hr]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun z _ => alternativeMass_nonneg hL hhL n x C z), alternativeMass_sum]
  exact ENNReal.ofReal_one

/-- Converting the joint mass to an extended real preserves its component product.  [the theorem's stated inputs and assumptions](hyp:n,x,z,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: jointMarkMass_ofReal_prod
lemma jointMarkMass_ofReal_prod (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (z w : Fin n → Bool × Bool) :
    ENNReal.ofReal (jointMarkMass hL n x z w) =
      ∏ C ∈ (orderedComponents hL n x).toFinset,
        ENNReal.ofReal (componentCouplingMass hL n x C (fun i => z i) (fun i => w i)) := by
  unfold jointMarkMass
  rw [← List.prod_toFinset _ (orderedComponents_nodup hL n x)]
  exact ENNReal.ofReal_prod_of_nonneg (fun C _ => componentCouplingMass_nonneg hL hhL n x C _ _)

/-- Any component observable has its prescribed marginal under the full product coupling array.  [the theorem's stated inputs and assumptions](hyp:n,x,C,hC,g), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: jointMarkMass_component_observable
lemma jointMarkMass_component_observable (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n))
    (hC : C ∈ orderedComponents hL n x) (g : Marks C × Marks C → ℝ≥0∞) :
    (∑ zw : (Fin n → Bool × Bool) × (Fin n → Bool × Bool),
      ENNReal.ofReal (jointMarkMass hL n x zw.1 zw.2) *
        g (fun i => zw.1 i, fun i => zw.2 i)) =
      ∑ zw : Marks C × Marks C,
        ENNReal.ofReal (componentCouplingMass hL n x C zw.1 zw.2) * g zw := by
  classical
  conv_lhs => rw [sum_pairedAssignments]
  conv_rhs => rw [sum_pairedAssignments]
  simp_rw [jointMarkMass_ofReal_prod hL hhL]
  apply sum_prod_partition_observable (α := (Bool × Bool) × (Bool × Bool))
    (s := (orderedComponents hL n x).toFinset)
    (D := C)
    (F := fun D v => ENNReal.ofReal (componentCouplingMass hL n x D
      (fun i => (v i).1) (fun i => (v i).2)))
    (g := fun v => g (fun i => (v i).1, fun i => (v i).2))
  · intro i
    obtain ⟨D, hD, hi⟩ := orderedComponents_cover hL n x i
    exact ⟨D, List.mem_toFinset.mpr hD, hi⟩
  · intro D hD E hE hne
    exact orderedComponents_disjoint hL n x D E
      (List.mem_toFinset.mp hD) (List.mem_toFinset.mp hE) hne
  · intro D _
    exact componentCouplingMass_paired_sum hL hhL n x D
  · exact List.mem_toFinset.mpr hC

/-- The conditional dataset coupling's expected Hamming cost is the sum of component costs.  [the theorem's stated inputs and assumptions](hyp:hhL,n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalDatasetCoupling_hamming_cost_eq
lemma conditionalDatasetCoupling_hamming_cost_eq (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (x : Fin n → Covariate) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂conditionalDatasetCoupling hL n x) =
      ∑ C ∈ (orderedComponents hL n x).toFinset,
        ∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C := by
  classical
  have hd (z w : Fin n → Bool × Bool) :
      (dHam n (attachMarks n x z) (attachMarks n x w) : ℝ≥0∞) =
        ∑ C ∈ (orderedComponents hL n x).toFinset,
          (hammingDist (fun i : C => z i) (fun i : C => w i) : ℝ≥0∞) := by
    rw [attachMarks_hammingDist, hammingDist_orderedComponents hL n x]
    rw [← List.sum_toFinset _ (orderedComponents_nodup hL n x), Nat.cast_sum]
  simp only [conditionalDatasetCoupling, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp_rw [hd, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C hC
  rw [jointMarkMass_component_observable hL hhL n x C (List.mem_toFinset.mp hC)
    (fun zw => (hammingDist zw.1 zw.2 : ℝ≥0∞))]
  simp only [componentCoupling, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- The product coupling costs at most the sum of the nonsingleton cubic certificates.  [the theorem's stated inputs and assumptions](hyp:hhL,n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalDatasetCoupling_hamming_cost_le_cubic_sum
lemma conditionalDatasetCoupling_hamming_cost_le_cubic_sum (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (x : Fin n → Covariate) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂conditionalDatasetCoupling hL n x) ≤
      ∑ C ∈ (orderedComponents hL n x).toFinset,
        if C.card = 1 then 0 else ENNReal.ofReal (4*separation hL*(C.card : ℝ)^3) := by
  classical
  rw [conditionalDatasetCoupling_hamming_cost_eq hL hhL]
  apply Finset.sum_le_sum
  intro C _
  by_cases hc : C.card = 1
  · rw [if_pos hc, componentCoupling_hamming_cost_zero_of_card_one hL hhL n x C hc]
  · rw [if_neg hc]
    exact componentCoupling_hamming_cost_le_cubic hL hhL n x C

/-- Replacement Hamming cost is a Borel function of the two datasets. [The displayed conclusion](goal) follows. -/
-- @node: measurable_datasetHammingCost
@[fun_prop] lemma measurable_datasetHammingCost (n : ℕ) :
    Measurable (fun zw : Dataset n × Dataset n => (dHam n zw.1 zw.2 : ℝ≥0∞)) := by
  classical
  simp only [dHam, hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd)).compl
  · exact measurable_const
  · exact measurable_const

/-- Integrating the Borel conditional kernel preserves the exact additive transport cost.  [the theorem's stated inputs and assumptions](hyp:hhL,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: commonMassCoupling_hamming_cost_eq
lemma commonMassCoupling_hamming_cost_eq (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂commonMassCoupling hL n) =
      ∫⁻ x, ∑ C ∈ (orderedComponents hL n x).toFinset,
        ∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate))) := by
  rw [commonMassCoupling, Measure.lintegral_bind
    (measurable_conditionalDatasetCoupling hL n).aemeasurable
    (measurable_datasetHammingCost n).aemeasurable]
  apply lintegral_congr
  intro x
  exact conditionalDatasetCoupling_hamming_cost_eq hL hhL n x

/-- The integrated dataset cost is bounded by the expected nonsingleton cubic component sum.  [the theorem's stated inputs and assumptions](hyp:hhL,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: commonMassCoupling_hamming_cost_le_cubic_sum
lemma commonMassCoupling_hamming_cost_le_cubic_sum (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂commonMassCoupling hL n) ≤
      ∫⁻ x, ∑ C ∈ (orderedComponents hL n x).toFinset,
        if C.card = 1 then 0 else ENNReal.ofReal (4*separation hL*(C.card : ℝ)^3)
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate))) := by
  rw [commonMassCoupling, Measure.lintegral_bind
    (measurable_conditionalDatasetCoupling hL n).aemeasurable
    (measurable_datasetHammingCost n).aemeasurable]
  exact lintegral_mono (fun x =>
    conditionalDatasetCoupling_hamming_cost_le_cubic_sum hL hhL n x)

end CausalSmith.Stat.PrivateCateRoughdesign
