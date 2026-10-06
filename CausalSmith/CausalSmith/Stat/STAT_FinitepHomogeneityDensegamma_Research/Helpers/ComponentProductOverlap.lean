module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentOverlap
public import Causalean.Stat.Minimax.ChiSquaredFinite
/-! Exact intermediate-versus-null joint chi-square factorization over the full label alphabet. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Independent uniform coordinates factor the mean of a product into the product of means. This statement assumes [the f condition](hyp:f). [This is the stated conclusion](goal). -/
-- @node: finite_pi_mean_prod
lemma finite_pi_mean_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (f : ∀ i, β i → ℝ) :
    (Fintype.card (∀ i, β i) : ℝ)⁻¹ * (∑ z : ∀ i, β i, ∏ i, f i (z i)) =
      ∏ i, (Fintype.card (β i) : ℝ)⁻¹ * ∑ x, f i x := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib,
    ← Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- A function of one coordinate has the same uniform mean on the full product as on that coordinate. [This is the stated conclusion](goal). -/
-- @node: finite_pi_mean_one
lemma finite_pi_mean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (j : ι) (f : β j → ℝ) :
    (Fintype.card (∀ i, β i) : ℝ)⁻¹ * (∑ z : ∀ i, β i, f (z j)) =
      (Fintype.card (β j) : ℝ)⁻¹ * ∑ x, f x := by
  classical
  let g (i : ι) (x : β i) : ℝ := if h : i = j then f (h ▸ x) else 1
  have hg (z : ∀ i, β i) : (∏ i, g i (z i)) = f (z j) := by
    simp [g]
  rw [show (∑ z : ∀ i, β i, f (z j)) = ∑ z : ∀ i, β i, ∏ i, g i (z i) from
    Finset.sum_congr rfl (fun z _ => (hg z).symm)]
  rw [finite_pi_mean_prod]
  have hh (i : ι) : (Fintype.card (β i) : ℝ)⁻¹ * ∑ x, g i x =
      if h : i = j then (Fintype.card (β j) : ℝ)⁻¹ * ∑ x, f x else 1 := by
    by_cases h : i = j
    · subst i; simp [g]
    · simp [g, h, Fintype.card_ne_zero]
  simp_rw [hh]
  simp

/-- Restricting labels to their disjoint observation components is a bijection. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the aug parameter](hyp:aug). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
-- @node: componentLabelEquiv
def componentLabelEquiv (n K M : ℕ) (aug : Augmentation n K) :
    Labels n ≃ (∀ C : {C // C ∈ components n K M aug}, C.val → Bool × Bool) := by
  classical
  let owner (i : Fin n) : {C // C ∈ components n K M aug} :=
    ⟨componentOf n K M aug i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  refine { toFun := fun labels C i => labels i.val
           invFun := fun z i => z (owner i) ⟨i, self_mem_componentOf n K M aug i⟩
           left_inv := ?_
           right_inv := ?_ }
  · intro labels; rfl
  · intro z
    funext C i
    have ho : owner i.val = C :=
      Subtype.ext (componentOf_eq_of_mem n K M aug C.property i.property)
    dsimp only
    have he : ∀ (D : {C // C ∈ components n K M aug}) (hD : D = C)
        (j : D.val), j.val = i.val → z D j = z C i := by
      intro D hD j hj
      subst D
      congr 1
      exact Subtype.ext hj
    exact he (owner i.val) ho _ rfl

/-- Component-local functions factor under the fair full-label average, including unused zero-mark signs. This statement assumes [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: component_partition_mean_prod
lemma component_partition_mean_prod (n K M : ℕ) (aug : Augmentation n K)
    (f : {C // C ∈ components n K M aug} → Labels n → ℝ)
    (hf : ∀ C l l', (∀ i ∈ C.val, l i = l' i) → f C l = f C l') :
    (4:ℝ)^(-(n:ℤ)) * (∑ l : Labels n, ∏ C, f C l) =
      ∏ C, (4:ℝ)^(-(n:ℤ)) * ∑ l : Labels n, f C l := by
  classical
  let e := componentLabelEquiv n K M aug
  let g (C : {C // C ∈ components n K M aug}) (x : C.val → Bool × Bool) : ℝ :=
    f C (fun i => if hi : i ∈ C.val then x ⟨i,hi⟩ else (false,false))
  have hg (z : ∀ C : {C // C ∈ components n K M aug}, C.val → Bool × Bool) (C) :
      f C (e.symm z) = g C (z C) := by
    apply hf
    intro i hi
    have h := congrFun (congrFun (e.apply_symm_apply z) C) ⟨i,hi⟩
    change e.symm z i = _ at h
    simpa only [g, dif_pos hi] using h
  have hw : (4:ℝ)^(-(n:ℤ)) = (Fintype.card (Labels n) : ℝ)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (fair_label_cardinality n)
  have hcard : Fintype.card (Labels n) =
      Fintype.card (∀ C : {C // C ∈ components n K M aug}, C.val → Bool × Bool) :=
    Fintype.card_congr e
  have hsum : (∑ l : Labels n, ∏ C, f C l) =
      ∑ z : ∀ C : {C // C ∈ components n K M aug}, C.val → Bool × Bool,
        ∏ C, g C (z C) := by
    apply Fintype.sum_equiv e
    intro l
    apply Finset.prod_congr rfl
    intro C _
    simpa only [e.symm_apply_apply] using hg (e l) C
  have hone (C : {C // C ∈ components n K M aug}) :
      (∑ l : Labels n, f C l) =
        ∑ z : ∀ C : {C // C ∈ components n K M aug}, C.val → Bool × Bool, g C (z C) := by
    apply Fintype.sum_equiv e
    intro l
    simpa only [e.symm_apply_apply] using hg (e l) C
  rw [hw, hcard, hsum, finite_pi_mean_prod]
  apply Finset.prod_congr rfl
  intro C _
  rw [hone, finite_pi_mean_one]

/-- The mass of a full-label atom is its density times the fair-label weight. [This is the stated conclusion](goal). -/
-- @node: fairLabelMeasure_singleton
lemma fairLabelMeasure_singleton (n : ℕ) (f : Labels n → ℝ) (l : Labels n) :
    fairLabelMeasure n f {l} = ENNReal.ofReal ((4:ℝ)^(-(n:ℤ))*f l) := by
  classical
  simp [fairLabelMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply', Set.indicator, Pi.single_apply]

/-- A nonnegative full-label density gives its exact real-valued atom mass. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: fairLabelMeasure_real_singleton
lemma fairLabelMeasure_real_singleton (n : ℕ) (f : Labels n → ℝ)
    (hf : ∀ l, 0 ≤ f l) (l : Labels n) :
    (fairLabelMeasure n f).real {l} = (4:ℝ)^(-(n:ℤ))*f l := by
  rw [measureReal_def, fairLabelMeasure_singleton, ENNReal.toReal_ofReal]
  exact mul_nonneg (by positivity) (hf l)

/-- A strictly positive full-label denominator dominates every fair-label density measure. This statement assumes [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: fairLabelMeasure_absolutelyContinuous
lemma fairLabelMeasure_absolutelyContinuous (n : ℕ) (f g : Labels n → ℝ)
    (hg : ∀ l, 0 < g l) : fairLabelMeasure n f ≪ fairLabelMeasure n g := by
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hz : fairLabelMeasure n g {l} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hl) hs
    rw [fairLabelMeasure_singleton] at hz
    have hp : 0 < (4:ℝ)^(-(n:ℤ))*g l := mul_pos (by positivity) (hg l)
    exact (ENNReal.ofReal_pos.mpr hp).ne' hz
  rw [hempty, measure_empty]

/-- Normalized full-label densities have shifted chi-square equal to their explicit squared-density quotient average. This statement assumes [the hf condition](hyp:hf), [the hg condition](hyp:hg), [the hf_sum condition](hyp:hf_sum), [the hg_sum condition](hyp:hg_sum). [This is the stated conclusion](goal). -/
-- @node: fairLabelMeasure_one_add_chiSqDiv
lemma fairLabelMeasure_one_add_chiSqDiv (n : ℕ) (f g : Labels n → ℝ)
    (hf : ∀ l, 0 ≤ f l) (hg : ∀ l, 0 < g l)
    (hf_sum : ∑ l, f l = (4:ℝ)^n) (hg_sum : ∑ l, g l = (4:ℝ)^n) :
    1 + Causalean.Stat.chiSqDiv (fairLabelMeasure n f) (fairLabelMeasure n g) =
      (4:ℝ)^(-(n:ℤ)) * ∑ l : Labels n, f l^2/g l := by
  letI := fairLabelMeasure_isProbabilityMeasure n f hf hf_sum
  letI := fairLabelMeasure_isProbabilityMeasure n g (fun l => (hg l).le) hg_sum
  rw [Causalean.Stat.finite_one_add_chiSqDiv _ _
    (fairLabelMeasure_absolutelyContinuous n f g hg), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [fairLabelMeasure_real_singleton n f hf,
    fairLabelMeasure_real_singleton n g (fun l => (hg l).le)]
  field_simp
  <;> ring

/-- A component likelihood depends only on the labels of observations in that component. This statement assumes [the hl condition](hyp:hl). [This is the stated conclusion](goal). -/
-- @node: componentDensity_labels_congr
lemma componentDensity_labels_congr (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (l l' : Labels n)
    (hl : ∀ i ∈ C, l i = l' i) :
    componentDensity ν s n K M a u aug C l = componentDensity ν s n K M a u aug C l' := by
  unfold componentDensity
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hl i hi]

/-- The joint intermediate-versus-null overlap factors into the exact local even overlaps. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: intermediate_null_overlap_product
lemma intermediate_null_overlap_product (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) :
    (4:ℝ)^(-(n:ℤ)) * ∑ l : Labels n,
      intermediateDensity n K M a u aug l^2 / nullConditionalDensity n K M a u aug l =
        ∏ C ∈ components n K M aug, (1 + componentEvenActivity n K M a u aug C) := by
  have hp (l : Labels n) :
      intermediateDensity n K M a u aug l^2 / nullConditionalDensity n K M a u aug l =
      ∏ C : {C // C ∈ components n K M aug},
        averageComponent n K M a u aug C.val l^2 / nullComponent n K M a u aug C.val l := by
    simp only [intermediateDensity, nullConditionalDensity, ← Finset.prod_pow,
      ← Finset.prod_div_distrib]
    exact (Finset.prod_coe_sort (components n K M aug)
      (fun C => averageComponent n K M a u aug C l^2 /
        nullComponent n K M a u aug C l)).symm
  simp_rw [hp]
  rw [component_partition_mean_prod]
  · simp_rw [component_even_overlap n K M a u hK ha hu aug]
    exact Finset.prod_coe_sort (components n K M aug)
      (fun C => 1 + componentEvenActivity n K M a u aug C)
  · intro C l l' hl
    have hh (ν s : Bool) := componentDensity_labels_congr ν s n K M a u aug C.val l l' hl
    simp only [averageComponent, nullComponent, hh]

/-- The intermediate-versus-null joint chi-square is exactly the product of unit mass plus each even activity. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: intermediate_null_chiSq_factorization
lemma intermediate_null_chiSq_factorization (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) :
    1 + Causalean.Stat.chiSqDiv (intermediateConditionalLaw n K M a u aug)
      (nullConditionalLaw n K M a u aug) =
        ∏ C ∈ components n K M aug, (1 + componentEvenActivity n K M a u aug C) := by
  rw [intermediateConditionalLaw, nullConditionalLaw, fairLabelMeasure_one_add_chiSqDiv]
  · exact intermediate_null_overlap_product n K M a u hK ha hu aug
  · intro l
    apply Finset.prod_nonneg
    intro C _
    exact le_trans (by positivity) (component_denominator_bounds n K M a u hK ha hu aug C l).2
  · intro l
    apply Finset.prod_pos
    intro C _
    exact lt_of_lt_of_le (by positivity) (component_denominator_bounds n K M a u hK ha hu aug C l).1
  · exact intermediateDensity_sum n K M a u aug
  · exact nullConditionalDensity_sum n K M a u aug

end CausalSmith.Stat.FinitepHomogeneityDensegamma
