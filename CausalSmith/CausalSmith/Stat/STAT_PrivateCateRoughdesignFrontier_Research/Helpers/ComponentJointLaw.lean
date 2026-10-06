module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentFactorization
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentMeasurability
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentProduct
/-! Finite partition sums, conditional marginals of the product common-mass coupling,
and the quadratic component total-variation bound.
The certificates hold at every covariate vector, including support boundaries. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Restriction to the blocks of a finite partition is a bijection of assignment spaces. -/
-- @node: partitionRestrictionEquiv
def partitionRestrictionEquiv {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (Finset ι))
    (hcover : ∀ i, ∃ C ∈ s, i ∈ C)
    (hdisj : Set.PairwiseDisjoint (s : Set (Finset ι)) id) :
    (ι → α) ≃ (∀ C : s, ↥(C : Finset ι) → α) := by
  classical
  apply Equiv.ofBijective (fun (z : ι → α) (C : s) (i : ↥(C : Finset ι)) => z i)
  constructor
  · intro z w h
    funext i
    obtain ⟨C, hC, hi⟩ := hcover i
    exact congrFun (congrFun h ⟨C, hC⟩) ⟨i, hi⟩
  · intro w
    choose C hC hi using hcover
    refine ⟨fun i => w ⟨C i, hC i⟩ ⟨i, hi i⟩, ?_⟩
    funext D i
    have he : C i = D := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj (hC i) D.property hne) (hi i) i.property
    have hs : (⟨C i, hC i⟩ : s) = D := Subtype.ext he
    have key : ∀ (E D : s) (he : E = D) (a : ↥(E : Finset ι))
        (b : ↥(D : Finset ι)), (a : ι) = (b : ι) → w E a = w D b := by
      intro E D he a b hab
      subst D
      exact congrArg (w E) (Subtype.ext hab)
    exact key _ _ hs _ _ rfl

/-- Summing products of independent block arrays factors into their individual sums.  [the theorem's stated inputs and assumptions](hyp:s,hcover,hdisj,s,F), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: sum_prod_partition
lemma sum_prod_partition {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (s : Finset (Finset ι))
    (hcover : ∀ i, ∃ C ∈ s, i ∈ C)
    (hdisj : Set.PairwiseDisjoint (s : Set (Finset ι)) id)
    (F : ∀ C : Finset ι, (C → α) → ℝ) :
    (∑ z : ι → α, ∏ C ∈ s, F C (fun i => z i)) =
      ∏ C ∈ s, ∑ z : C → α, F C z := by
  classical
  let e := partitionRestrictionEquiv (α := α) s hcover hdisj
  calc
    _ = ∑ w : ∀ C : s, ↥(C : Finset ι) → α, ∏ C : s, F C (w C) := by
      apply Fintype.sum_equiv e
      intro z
      change (∏ C ∈ s, F C (fun i => z i)) = ∏ C : s, F C (fun i => z i)
      exact (Finset.prod_coe_sort s (fun C => F C (fun i => z i))).symm
    _ = _ := by
      rw [← Fintype.prod_sum]
      exact Finset.prod_coe_sort s (fun C => ∑ z : C → α, F C z)

/-- The ordered shared-sign components form a finite partition for any mark alphabet.  [the theorem's stated inputs and assumptions](hyp:hL,n,x,F), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: orderedComponents_sum_prod
lemma orderedComponents_sum_prod {α : Type*} [Fintype α]
    (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (F : ∀ C : Finset (Fin n), (C → α) → ℝ) :
    (∑ z : Fin n → α, ((orderedComponents hL n x).map
      (fun C => F C (fun i => z i))).prod) =
      ((orderedComponents hL n x).map (fun (C : Finset (Fin n)) => ∑ z : C → α, F C z)).prod := by
  classical
  have hc : ∀ i, ∃ C ∈ (orderedComponents hL n x).toFinset, i ∈ C := by
    intro i
    obtain ⟨C, hC, hi⟩ := orderedComponents_cover hL n x i
    exact ⟨C, List.mem_toFinset.mpr hC, hi⟩
  have hd : Set.PairwiseDisjoint
      ((orderedComponents hL n x).toFinset : Set (Finset (Fin n))) id := by
    intro C hC D hD hne
    exact orderedComponents_disjoint hL n x C D
      (List.mem_toFinset.mp hC) (List.mem_toFinset.mp hD) hne
  simp_rw [← List.prod_toFinset _ (orderedComponents_nodup hL n x)]
  exact sum_prod_partition _ hc hd F

/-- Every product joint mass is nonnegative.  [the theorem's stated inputs and assumptions](hyp:n,x,z,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: jointMarkMass_nonneg
lemma jointMarkMass_nonneg (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (z w : Fin n → Bool × Bool) :
    0 ≤ jointMarkMass hL n x z w := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp ha
  exact componentCouplingMass_nonneg hL hhL n x C _ _

/-- Summing a row of the joint product recovers the full conditional sign mixture.  [the theorem's stated inputs and assumptions](hyp:n,x,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: jointMarkMass_row_sum
lemma jointMarkMass_row_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (z : Fin n → Bool × Bool) :
    (∑ w, jointMarkMass hL n x z w) = fullAlternativeMass hL n x z := by
  unfold jointMarkMass
  rw [orderedComponents_sum_prod]
  simp_rw [componentCouplingMass_row_sum hL hhL]
  exact (fullAlternativeMass_component_factorization hL n x z).symm

/-- Summing a column of the joint product recovers the full fair mark array.  [the theorem's stated inputs and assumptions](hyp:n,x,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: jointMarkMass_column_sum
lemma jointMarkMass_column_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (w : Fin n → Bool × Bool) :
    (∑ z, jointMarkMass hL n x z w) = (4 : ℝ)^(-(n : ℤ)) := by
  unfold jointMarkMass
  rw [orderedComponents_sum_prod hL n x
    (fun C z => componentCouplingMass hL n x C z (fun i => w i))]
  simp_rw [componentCouplingMass_column_sum hL hhL]
  exact (nullMass_component_factorization hL n x w).symm

/-- The full conditional alternative array sums to one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: fullAlternativeMass_sum
lemma fullAlternativeMass_sum (hL : ℝ) (n : ℕ) (x : Fin n → Covariate) :
    (∑ z, fullAlternativeMass hL n x z) = 1 := by
  simp_rw [fullAlternativeMass_component_factorization, orderedComponents_sum_prod,
    alternativeMass_sum]
  simp

/-- The finite joint product array has unit total mass.  [the theorem's stated inputs and assumptions](hyp:n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: jointMarkMass_sum
lemma jointMarkMass_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) :
    (∑ zw : (Fin n → Bool × Bool) × (Fin n → Bool × Bool),
      jointMarkMass hL n x zw.1 zw.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [jointMarkMass_row_sum hL hhL]
  exact fullAlternativeMass_sum hL n x

/-- The conditional alternative dataset law attaches fixed covariates to the mixed marks. -/
-- @node: conditionalAlternativeDatasetLaw
def conditionalAlternativeDatasetLaw (hL : ℝ) (n : ℕ) (x : Fin n → Covariate) :
    Measure (Dataset n) :=
  ∑ z : Fin n → Bool × Bool,
    ENNReal.ofReal (fullAlternativeMass hL n x z) • Measure.dirac (attachMarks n x z)

/-- The conditional null dataset law attaches fixed covariates to independent fair marks. -/
-- @node: conditionalNullDatasetLaw
def conditionalNullDatasetLaw (n : ℕ) (x : Fin n → Covariate) : Measure (Dataset n) :=
  ∑ z : Fin n → Bool × Bool,
    ENNReal.ofReal ((4 : ℝ)^(-(n : ℤ))) • Measure.dirac (attachMarks n x z)

/-- The conditional product coupling has the exact mixed dataset law as first marginal.  [the theorem's stated inputs and assumptions](hyp:n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: conditionalDatasetCoupling_map_fst
lemma conditionalDatasetCoupling_map_fst (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) :
    (conditionalDatasetCoupling hL n x).map Prod.fst =
      conditionalAlternativeDatasetLaw hL n x := by
  classical
  have hr (z : Fin n → Bool × Bool) :
      (∑ w, ENNReal.ofReal (jointMarkMass hL n x z w)) =
        ENNReal.ofReal (fullAlternativeMass hL n x z) := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun w _ => jointMarkMass_nonneg hL hhL n x z w), jointMarkMass_row_sum hL hhL]
  ext S hS
  rw [Measure.map_apply measurable_fst hS]
  simp only [conditionalDatasetCoupling, conditionalAlternativeDatasetLaw,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ w, ENNReal.ofReal (jointMarkMass hL n x z w) *
      S.indicator 1 (attachMarks n x z)) = _
  rw [← Finset.sum_mul, hr]

/-- The conditional product coupling has the exact fair dataset law as second marginal.  [the theorem's stated inputs and assumptions](hyp:n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: conditionalDatasetCoupling_map_snd
lemma conditionalDatasetCoupling_map_snd (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) :
    (conditionalDatasetCoupling hL n x).map Prod.snd = conditionalNullDatasetLaw n x := by
  classical
  have hc (w : Fin n → Bool × Bool) :
      (∑ z, ENNReal.ofReal (jointMarkMass hL n x z w)) =
        ENNReal.ofReal ((4 : ℝ)^(-(n : ℤ))) := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun z _ => jointMarkMass_nonneg hL hhL n x z w), jointMarkMass_column_sum hL hhL]
  ext S hS
  rw [Measure.map_apply measurable_snd hS]
  simp only [conditionalDatasetCoupling, conditionalNullDatasetLaw,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ z, ENNReal.ofReal (jointMarkMass hL n x z w) *
      S.indicator 1 (attachMarks n x w)) = _
  rw [← Finset.sum_mul, hc]

/-- The conditional product coupling is a probability measure at every covariate vector.  [the theorem's stated inputs and assumptions](hyp:hhL,n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalDatasetCoupling_isProbabilityMeasure
lemma conditionalDatasetCoupling_isProbabilityMeasure (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (x : Fin n → Covariate) :
    IsProbabilityMeasure (conditionalDatasetCoupling hL n x) := by
  constructor
  simp only [conditionalDatasetCoupling, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun zw _ => jointMarkMass_nonneg hL hhL n x zw.1 zw.2), jointMarkMass_sum hL hhL]
  exact ENNReal.ofReal_one

/-- The explicit Borel conditional product couples the two full conditional dataset laws.  [the theorem's stated inputs and assumptions](hyp:n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: conditionalDatasetCoupling_isCoupling
lemma conditionalDatasetCoupling_isCoupling (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) :
    Causalean.Stat.IsCoupling (conditionalDatasetCoupling hL n x)
      (conditionalAlternativeDatasetLaw hL n x) (conditionalNullDatasetLaw n x) := by
  exact ⟨conditionalDatasetCoupling_isProbabilityMeasure hL hhL n x,
    conditionalDatasetCoupling_map_fst hL hhL n x,
    conditionalDatasetCoupling_map_snd hL hhL n x⟩

/-- Integrating the pointwise conditional coupling preserves unit total mass.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: commonMassCoupling_isProbabilityMeasure
lemma commonMassCoupling_isProbabilityMeasure (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) : IsProbabilityMeasure (commonMassCoupling hL n) := by
  constructor
  rw [commonMassCoupling, Measure.bind_apply MeasurableSet.univ
    (measurable_conditionalDatasetCoupling hL n).aemeasurable]
  have hp (x : Fin n → Covariate) : conditionalDatasetCoupling hL n x Set.univ = 1 := by
    let := conditionalDatasetCoupling_isProbabilityMeasure hL hhL n x
    exact measure_univ
  simp only [hp, lintegral_const, one_mul, measure_univ]

/-- The conditional alternative dataset law is Borel in the covariates. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_conditionalAlternativeDatasetLaw
@[fun_prop] lemma measurable_conditionalAlternativeDatasetLaw (hL : ℝ) (n : ℕ) :
    Measurable (conditionalAlternativeDatasetLaw hL n) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [conditionalAlternativeDatasetLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro z _
  apply Measurable.mul ((measurable_fullAlternativeMass hL n z).ennreal_ofReal)
  simp only [Measure.dirac_apply' _ hE]
  exact measurable_const.indicator (hE.preimage (measurable_attachMarks n z))

/-- The conditional null dataset law is Borel in the covariates. [The displayed conclusion](goal) follows. -/
-- @node: measurable_conditionalNullDatasetLaw
@[fun_prop] lemma measurable_conditionalNullDatasetLaw (n : ℕ) :
    Measurable (conditionalNullDatasetLaw n) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [conditionalNullDatasetLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro z _
  apply Measurable.mul measurable_const
  simp only [Measure.dirac_apply' _ hE]
  exact measurable_const.indicator (hE.preimage (measurable_attachMarks n z))

/-- Integrating the conditional coupling recovers the integrated alternative marginal.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: commonMassCoupling_map_fst_bind
lemma commonMassCoupling_map_fst_bind (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    (commonMassCoupling hL n).map Prod.fst =
      (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
        (conditionalAlternativeDatasetLaw hL n) := by
  ext E hE
  rw [Measure.map_apply measurable_fst hE, commonMassCoupling,
    Measure.bind_apply (hE.preimage measurable_fst)
      (measurable_conditionalDatasetCoupling hL n).aemeasurable,
    Measure.bind_apply hE (measurable_conditionalAlternativeDatasetLaw hL n).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← conditionalDatasetCoupling_map_fst hL hhL n x,
    Measure.map_apply measurable_fst hE]

/-- Integrating the conditional coupling recovers the integrated null marginal.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: commonMassCoupling_map_snd_bind
lemma commonMassCoupling_map_snd_bind (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    (commonMassCoupling hL n).map Prod.snd =
      (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
        (conditionalNullDatasetLaw n) := by
  ext E hE
  rw [Measure.map_apply measurable_snd hE, commonMassCoupling,
    Measure.bind_apply (hE.preimage measurable_snd)
      (measurable_conditionalDatasetCoupling hL n).aemeasurable,
    Measure.bind_apply hE (measurable_conditionalNullDatasetLaw n).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← conditionalDatasetCoupling_map_snd hL hhL n x,
    Measure.map_apply measurable_snd hE]

/-- The Borel product construction couples the integrated conditional dataset laws.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: commonMassCoupling_isCoupling_bind
lemma commonMassCoupling_isCoupling_bind (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    Causalean.Stat.IsCoupling (commonMassCoupling hL n)
      ((Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
        (conditionalAlternativeDatasetLaw hL n))
      ((Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
        (conditionalNullDatasetLaw n)) := by
  exact ⟨commonMassCoupling_isProbabilityMeasure hL hhL n,
    commonMassCoupling_map_fst_bind hL hhL n, commonMassCoupling_map_snd_bind hL hhL n⟩

open Classical in
/-- A nonnegative finite atomic array evaluates an event by summing its selected entries.  [the theorem's stated inputs and assumptions](hyp:a,ha,E,hE), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: finite_atomic_array_real
lemma finite_atomic_array_real {α : Type*} [Fintype α] [MeasurableSpace α]
    (a : α → ℝ) (ha : ∀ z, 0 ≤ a z) (E : Set α) (hE : MeasurableSet E) :
    (∑ z, ENNReal.ofReal (a z) • Measure.dirac z).real E =
      ∑ z, if z ∈ E then a z else 0 := by
  classical
  have hn (z : α) : 0 ≤ if z ∈ E then a z else 0 := by
    split_ifs <;> first | exact ha z | exact le_rfl
  have he (z : α) : ENNReal.ofReal (a z) * E.indicator 1 z =
      ENNReal.ofReal (if z ∈ E then a z else 0) := by
    by_cases hz : z ∈ E <;> simp [hz]
  simp only [measureReal_def, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul, he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hn z),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun z _ => hn z))]

open Classical in
/-- Event gaps of two probability arrays are bounded by their mass outside the common part.  [the theorem's stated inputs and assumptions](hyp:a,b,hsa,hsb,E), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: finite_array_event_gap_le_overlap_deficit
lemma finite_array_event_gap_le_overlap_deficit {α : Type*} [Fintype α]
    (a b : α → ℝ)
    (hsa : ∑ z, a z = 1) (hsb : ∑ z, b z = 1) (E : Set α) :
    |(∑ z, if z ∈ E then a z else 0) - (∑ z, if z ∈ E then b z else 0)| ≤
      1 - ∑ z, min (a z) (b z) := by
  classical
  let c (z : α) := min (a z) (b z)
  have bounds (f : α → ℝ) (hf : ∀ z, 0 ≤ f z) :
      0 ≤ (∑ z, if z ∈ E then f z else 0) ∧
      (∑ z, if z ∈ E then f z else 0) ≤ ∑ z, f z := by
    constructor
    · apply Finset.sum_nonneg; intro z _; split_ifs <;> first | exact hf z | exact le_rfl
    · apply Finset.sum_le_sum; intro z _; split_ifs <;> first | exact le_rfl | exact hf z
  have har := bounds (fun z => a z-c z) (fun z => sub_nonneg.mpr (min_le_left _ _))
  have hbr := bounds (fun z => b z-c z) (fun z => sub_nonneg.mpr (min_le_right _ _))
  rw [Finset.sum_sub_distrib, hsa] at har
  rw [Finset.sum_sub_distrib, hsb] at hbr
  have split_sum (f : α → ℝ) :
      (∑ z, if z ∈ E then f z else 0) =
        (∑ z, if z ∈ E then f z-c z else 0) + (∑ z, if z ∈ E then c z else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> ring
  rw [split_sum a, split_sum b, abs_le]
  change -(1 - ∑ z, c z) ≤ _ ∧ _ ≤ 1 - ∑ z, c z
  constructor <;> linarith [har.1, har.2, hbr.1, hbr.2]

/-- The TV of the finite component laws is bounded by the explicit coupling's failure mass.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: component_TV_le_overlap_deficit
lemma component_TV_le_overlap_deficit (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C) ≤
      1-overlapMass hL n x C := by
  classical
  unfold TV Causalean.Stat.tvDist
  apply ciSup_le
  intro E
  rw [alternativeComponentLaw, nullComponentLaw,
    finite_atomic_array_real _ (alternativeMass_nonneg hL hhL n x C) E.1 E.2,
    finite_atomic_array_real _ (fun z => (nullMass_pos n C z).le) E.1 E.2]
  exact finite_array_event_gap_le_overlap_deficit _ _
    (alternativeMass_sum hL n x C) (nullMass_sum n C) E.1

/-- The curvature certificate gives the uniform four-times-separation component TV bound.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: component_TV_le_quadratic
lemma component_TV_le_quadratic (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C) ≤
      4*separation hL*(componentSize n C : ℝ)^2 := by
  exact (component_TV_le_overlap_deficit hL hhL n x C).trans
    (overlapMass_deficit_le hL hhL n x C)

/-- Selecting entries where the first array is larger attains its overlap deficit.  [the theorem's stated inputs and assumptions](hyp:a,b,hsa), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: finite_array_positive_event_gap
lemma finite_array_positive_event_gap {α : Type*} [Fintype α]
    (a b : α → ℝ) (hsa : ∑ z, a z = 1) :
    (∑ z, if b z ≤ a z then a z else 0) -
      (∑ z, if b z ≤ a z then b z else 0) =
        1 - ∑ z, min (a z) (b z) := by
  classical
  rw [← Finset.sum_sub_distrib, ← hsa, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : b z ≤ a z
  · rw [if_pos h, if_pos h, min_eq_right h]
  · rw [if_neg h, if_neg h, min_eq_left (le_of_not_ge h)]
    ring

/-- Each nonnegative alternative component array defines a probability measure.  [the theorem's stated inputs and assumptions](hyp:hhL,n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: alternativeComponentLaw_isProbabilityMeasure
lemma alternativeComponentLaw_isProbabilityMeasure (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) : IsProbabilityMeasure (alternativeComponentLaw hL n x C) := by
  constructor
  simp only [alternativeComponentLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun z _ => alternativeMass_nonneg hL hhL n x C z), alternativeMass_sum]
  exact ENNReal.ofReal_one

/-- The explicit finite common part gives the exact total variation of component laws.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: component_TV_eq_overlap_deficit
lemma component_TV_eq_overlap_deficit (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C) =
      1-overlapMass hL n x C := by
  classical
  apply le_antisymm (component_TV_le_overlap_deficit hL hhL n x C)
  let E : Set (Marks C) := {z | nullMass n C z ≤ alternativeMass hL n x C z}
  have hE : MeasurableSet E := Set.to_countable E |>.measurableSet
  let := alternativeComponentLaw_isProbabilityMeasure hL hhL n x C
  let := nullComponentLaw_isProbabilityMeasure n C
  have h := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := alternativeComponentLaw hL n x C) (ν := nullComponentLaw n C) hE
  rw [alternativeComponentLaw, nullComponentLaw,
    finite_atomic_array_real _ (alternativeMass_nonneg hL hhL n x C) E hE,
    finite_atomic_array_real _ (fun z => (nullMass_pos n C z).le) E hE] at h
  change |(∑ z, if nullMass n C z ≤ alternativeMass hL n x C z then
      alternativeMass hL n x C z else 0) -
    (∑ z, if nullMass n C z ≤ alternativeMass hL n x C z then nullMass n C z else 0)| ≤ _ at h
  rw [finite_array_positive_event_gap _ _ (alternativeMass_sum hL n x C)] at h
  change |1-overlapMass hL n x C| ≤ TV (alternativeComponentLaw hL n x C)
    (nullComponentLaw n C) at h
  rw [abs_of_nonneg (sub_nonneg.mpr (overlapMass_range hL hhL n x C).2)] at h
  exact h

/-- The common-mass component coupling fails with probability exactly its marginal TV.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentCoupling_disagreement_eq_TV
lemma componentCoupling_disagreement_eq_TV (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    componentCoupling hL n x C {zw | zw.1 ≠ zw.2} =
      ENNReal.ofReal (TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C)) := by
  rw [component_TV_eq_overlap_deficit hL hhL,
    componentCoupling_disagreement_mass hL hhL]

/-- Component total variation is half the absolute difference of its finite arrays.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: component_TV_eq_half_abs_sum
lemma component_TV_eq_half_abs_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C) =
      1/2 * ∑ z : Marks C, |alternativeMass hL n x C z-nullMass n C z| := by
  rw [component_TV_eq_overlap_deficit hL hhL, componentMass_abs_sum]
  ring

/-- The explicit coupling changes at most the component size times its marginal TV.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentCoupling_hamming_cost_le_TV
lemma componentCoupling_hamming_cost_le_TV (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C) ≤
      (C.card : ℝ≥0∞) *
        ENNReal.ofReal (TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C)) := by
  rw [component_TV_eq_overlap_deficit hL hhL]
  exact componentCoupling_hamming_cost_le hL hhL n x C

end CausalSmith.Stat.PrivateCateRoughdesign
