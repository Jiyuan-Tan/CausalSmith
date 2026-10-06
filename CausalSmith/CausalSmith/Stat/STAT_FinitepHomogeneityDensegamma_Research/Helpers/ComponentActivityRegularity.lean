module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentChiSquare
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentMeasurability

/-! Measurability and finite integrability of the complete component activities. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The finite auxiliary experiment has finite total mass for every rarity parameter. [This is the stated conclusion](goal). -/
-- @node: commonAugmentation_isFiniteMeasure
lemma commonAugmentation_isFiniteMeasure (n K M : ℕ) (ε : ℝ) :
    IsFiniteMeasure (commonAugmentation n K M ε) := by
  letI : IsFiniteMeasure (markFlagLaw ε) := ⟨by
    simp [markFlagLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']⟩
  letI : IsFiniteMeasure (disclosureLaw K M) := ⟨by
    simp only [disclosureLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    finiteness⟩
  letI : IsFiniteMeasure design := by
    unfold design
    infer_instance
  unfold commonAugmentation
  infer_instance

/-- A component's coarse-pair index is a Borel function of the design. [This is the stated conclusion](goal). -/
-- @node: measurable_pairIndex
@[fun_prop] lemma measurable_pairIndex (n K M : ℕ) (C : Finset (Fin n)) :
    Measurable (fun aug : Augmentation n K => pairIndex M aug C) := by
  unfold pairIndex
  fun_prop

/-- Fixed-component even activity is Borel, including division by its actual density. [This is the stated conclusion](goal). -/
-- @node: measurable_componentEvenActivity
@[fun_prop] lemma measurable_componentEvenActivity (n K M : ℕ) (a u : ℝ)
    (C : Finset (Fin n)) :
    Measurable (fun aug => componentEvenActivity n K M a u aug C) := by
  unfold componentEvenActivity evenDiscrepancy averageComponent nullComponent
  fun_prop

/-- Fixed-component odd activity is Borel on the full augmented design. [This is the stated conclusion](goal). -/
-- @node: measurable_componentOddActivity
@[fun_prop] lemma measurable_componentOddActivity (n K M : ℕ) (a u : ℝ)
    (C : Finset (Fin n)) :
    Measurable (fun aug => componentOddActivity n K M a u aug C) := by
  unfold componentOddActivity oddDiscrepancy averageComponent
  fun_prop

/-- Component membership indicators turn the variable activity sum into a finite Borel sum. [This is the stated conclusion](goal). -/
-- @node: measurable_activityA
@[fun_prop] lemma measurable_activityA (n K M : ℕ) (a u : ℝ) :
    Measurable (activityA n K M a u) := by
  have he (aug : Augmentation n K) : activityA n K M a u aug =
      ∑ C : Finset (Fin n), if C ∈ components n K M aug then
        componentEvenActivity n K M a u aug C else 0 := by
    simp [activityA]
  change Measurable (fun aug : Augmentation n K => _ )
  simp_rw [he]
  apply Finset.measurable_sum
  intro C _
  exact (measurable_componentEvenActivity n K M a u C).ite
    (measurableSet_componentMembership n K M C) measurable_const

/-- The distinct-component shared-pair activity is Borel without discarding any pair terms. [This is the stated conclusion](goal). -/
-- @node: measurable_activityB
@[fun_prop] lemma measurable_activityB (n K M : ℕ) (a u : ℝ) :
    Measurable (activityB n K M a u) := by
  have he (aug : Augmentation n K) : activityB n K M a u aug =
      (∑ C : Finset (Fin n), if C ∈ components n K M aug then
        ∑ D : Finset (Fin n), if D ∈ components n K M aug then
          if C ≠ D ∧ pairIndex M aug C = pairIndex M aug D then
            componentOddActivity n K M a u aug C * componentOddActivity n K M a u aug D
          else 0 else 0 else 0) / 2 := by
    simp [activityB]
  change Measurable (fun aug : Augmentation n K => activityB n K M a u aug)
  simp_rw [he]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro C _
  apply Measurable.ite (measurableSet_componentMembership n K M C) _ measurable_const
  apply Finset.measurable_sum
  intro D _
  apply Measurable.ite (measurableSet_componentMembership n K M D) _ measurable_const
  apply Measurable.ite
  · exact (show MeasurableSet {aug : Augmentation n K | C ≠ D} from by
      by_cases h : C = D <;> simp [h]).inter
        (measurableSet_eq_fun (measurable_pairIndex n K M C) (measurable_pairIndex n K M D))
  · fun_prop
  · fun_prop

/-- The positive density envelope bounds the even discrepancy uniformly for a fixed occupancy. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_uniform_bound
lemma evenDiscrepancy_uniform_bound (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |evenDiscrepancy n K M a u aug C labels| ≤ (2:ℝ)^C.card := by
  have hp := componentDensity_bounds true true n K M a u hK ha hu aug C labels
  have hm := componentDensity_bounds true false n K M a u hK ha hu aug C labels
  have h0 := componentDensity_bounds false false n K M a u hK ha hu aug C labels
  have hlo : 0 ≤ (1/2:ℝ)^C.card := by positivity
  unfold evenDiscrepancy averageComponent nullComponent
  apply abs_le.mpr
  constructor <;> linarith

/-- Every even component activity is uniformly finite before using any derivative or rarity estimate. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: componentEvenActivity_uniform_bound
lemma componentEvenActivity_uniform_bound (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    componentEvenActivity n K M a u aug C ≤ (8:ℝ)^C.card := by
  have hh := finite_component_activity_bound n C.card
    (evenDiscrepancy n K M a u aug C) (nullComponent n K M a u aug C)
    ((2:ℝ)^C.card) (by positivity)
    (evenDiscrepancy_uniform_bound n K M a u hK ha hu aug C)
    (fun labels => (component_denominator_bounds n K M a u hK ha hu aug C labels).1)
  change componentEvenActivity n K M a u aug C ≤ _ at hh
  convert hh using 1
  rw [← pow_mul, Nat.mul_comm C.card 2, pow_mul, ← mul_pow]
  norm_num

/-- A finite sum over all observation subsets uniformly dominates the actual even activity. [This is the stated conclusion](goal). -/
-- @node: activityA_uniform_bound
lemma activityA_uniform_bound (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (aug : Augmentation n K) :
    activityA n K M a u aug ≤ ∑ C : Finset (Fin n), (8:ℝ)^C.card := by
  rcases h with ⟨hn, hk, hm, hKM, hM, ha, hu, hε, hL⟩
  have hK : 0 < K := by omega
  unfold activityA
  calc
    _ ≤ ∑ C ∈ components n K M aug, (8:ℝ)^C.card :=
      Finset.sum_le_sum (fun C _ => componentEvenActivity_uniform_bound n K M a u hK ha hu aug C)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)

/-- Odd activities bounded by one give a finite bound on all distinct shared-pair products. [This is the stated conclusion](goal). -/
-- @node: activityB_uniform_bound
lemma activityB_uniform_bound (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (aug : Augmentation n K) :
    activityB n K M a u aug ≤ (Fintype.card (Finset (Fin n)):ℝ)^2/2 := by
  have hnonneg := component_activities_nonneg n K M a u
    (by have := h.2.2.2.1; have := h.2.2.2.2.1; omega)
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  have hbound := componentOddActivity_le_one n K M a u
    (by have := h.2.2.2.1; have := h.2.2.2.2.1; omega)
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  have hterm (C D : Finset (Fin n)) :
      (if C ≠ D ∧ pairIndex M aug C = pairIndex M aug D then
        componentOddActivity n K M a u aug C*componentOddActivity n K M a u aug D else 0) ≤ 1 := by
    split
    · exact (mul_le_mul (hbound C) (hbound D) (hnonneg D).2 (by norm_num)).trans_eq (by ring)
    · norm_num
  unfold activityB
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ C ∈ components n K M aug, ∑ D ∈ components n K M aug, (1:ℝ) :=
      Finset.sum_le_sum (fun C _ => Finset.sum_le_sum (fun D _ => hterm C D))
    _ = ((components n K M aug).card:ℝ)^2 := by simp; ring
    _ ≤ _ := by
      have hc : (components n K M aug).card ≤ Fintype.card (Finset (Fin n)) := Finset.card_le_univ _
      have hc' : ((components n K M aug).card:ℝ) ≤ Fintype.card (Finset (Fin n)) := by exact_mod_cast hc
      exact pow_le_pow_left₀ (by positivity) hc' 2

/-- Both complete activities are integrable because they are Borel and bounded on the finite auxiliary measure. [This is the stated conclusion](goal). -/
-- @node: component_activities_integrable
lemma component_activities_integrable (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) :
    Integrable (activityA n K M a u) (commonAugmentation n K M ε) ∧
    Integrable (activityB n K M a u) (commonAugmentation n K M ε) := by
  letI := commonAugmentation_isFiniteMeasure n K M ε
  constructor
  · apply Integrable.of_mem_Icc 0 (∑ C : Finset (Fin n), (8:ℝ)^C.card)
      (measurable_activityA n K M a u).aemeasurable
    exact Filter.Eventually.of_forall (fun aug =>
      ⟨(conditional_activities_nonneg n K M a u ε L h aug).1,
        activityA_uniform_bound n K M a u ε L h aug⟩)
  · apply Integrable.of_mem_Icc 0 ((Fintype.card (Finset (Fin n)):ℝ)^2/2)
      (measurable_activityB n K M a u).aemeasurable
    exact Filter.Eventually.of_forall (fun aug =>
      ⟨(conditional_activities_nonneg n K M a u ε L h aug).2,
        activityB_uniform_bound n K M a u ε L h aug⟩)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
