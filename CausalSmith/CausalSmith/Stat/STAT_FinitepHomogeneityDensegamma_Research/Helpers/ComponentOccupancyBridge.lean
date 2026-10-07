module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentActivityRegularity
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCoefficientGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OccupancySeries
public import Causalean.Stat.RandomGraph.PathOccupancy.Bounds

/-! Concrete-model bridge from the copula augmentation to fixed-sample path occupancy bounds. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- [The occ Cell object](goal) is defined from [the K parameter](hyp:K), [the hK parameter](hyp:hK), [the x parameter](hyp:x). -/
def occCell (K : ℕ) (hK : 0 < K) (x : unitInterval) : Fin K :=
  ⟨fineIndex K x, by simp only [fineIndex]; omega⟩

/-- Under [the hK condition](hyp:hK), [the measurable occ Cell statement holds](goal). -/
lemma measurable_occCell (K : ℕ) (hK : 0 < K) : Measurable (occCell K hK) := by
  intro s _
  let t : Set ℕ := {i | ∃ hi : i < K, (⟨i, hi⟩ : Fin K) ∈ s}
  have ht : MeasurableSet t := MeasurableSet.of_discrete
  have hm := measurable_fineIndex K ht
  convert hm using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred, t, occCell]
  constructor
  · intro hx
    exact ⟨by simp only [fineIndex]; omega, by simpa only [Fin.ext_iff]⟩
  · rintro ⟨hi, hx⟩
    simpa only [Fin.ext_iff] using hx

/-- Under [the hK condition](hyp:hK), [the occ Cell fiber statement holds](goal). -/
lemma occCell_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    design {x | occCell K hK x = a} = (K : ℝ≥0∞)⁻¹ := by
  let lo : unitInterval := ⟨(a : ℝ) / K, by
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hK)).2 (by exact_mod_cast a.isLt.le)⟩
  let hi : unitInterval := ⟨((a : ℕ) + 1 : ℝ) / K, by
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hK)).2 (by exact_mod_cast a.isLt)⟩
  by_cases ha : (a : ℕ) + 1 = K
  · have he : {x : unitInterval | occCell K hK x = a} = Icc lo 1 := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Icc, lo, occCell, Fin.ext_iff]
      constructor
      · intro hx
        constructor
        · have hf : a.val ≤ Nat.floor ((K : ℝ) * (x : ℝ)) := by
            simp only [fineIndex] at hx
            omega
          have hf' : (a : ℝ) ≤ (K : ℝ) * (x : ℝ) :=
            (Nat.le_floor_iff (mul_nonneg (by positivity) x.property.1)).mp hf
          change (a : ℝ) / (K : ℝ) ≤ (x : ℝ)
          apply (div_le_iff₀ (by exact_mod_cast hK)).2
          simpa [mul_comm] using hf'
        · exact x.property.2
      · rintro ⟨hlo, _⟩
        have hfloor : a.val ≤ Nat.floor ((K : ℝ) * (x : ℝ)) := by
          apply (Nat.le_floor_iff (mul_nonneg (by positivity) x.property.1)).mpr
          change (a : ℝ) / (K : ℝ) ≤ (x : ℝ) at hlo
          have := (div_le_iff₀ (by exact_mod_cast hK)).mp hlo
          simpa [mul_comm] using this
        simp only [fineIndex]
        omega
    rw [he, design, unitInterval.volume_Icc]
    simp only [lo]
    rw [show (a : ℕ) = K - 1 by omega]
    simp only [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
    have hreal : (1 : ℝ) - ((K : ℝ) - 1) / K = 1 / K := by
      have hKR : (0 : ℝ) < K := by exact_mod_cast hK
      field_simp [hKR.ne']
      linarith
    change ENNReal.ofReal ((1 : ℝ) - ((K : ℝ) - 1) / K) = _
    rw [hreal, ENNReal.ofReal_div_of_pos (by exact_mod_cast hK)]
    simp
  · have halt : (a : ℕ) + 1 < K := by omega
    have he : {x : unitInterval | occCell K hK x = a} = Ico lo hi := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ico, lo, hi, occCell, Fin.ext_iff]
      constructor
      · intro hx
        have hx' : Nat.floor ((K : ℝ) * (x : ℝ)) = a.val := by
          simp only [fineIndex] at hx
          omega
        rw [Nat.floor_eq_iff (mul_nonneg (by positivity) x.property.1)] at hx'
        constructor
        · change (a : ℝ) / (K : ℝ) ≤ (x : ℝ)
          apply (div_le_iff₀ (by exact_mod_cast hK)).2
          simpa [mul_comm] using hx'.1
        · change (x : ℝ) < ((a : ℕ) + 1 : ℝ) / (K : ℝ)
          apply (lt_div_iff₀ (by exact_mod_cast hK)).2
          simpa [mul_comm] using hx'.2
      · rintro ⟨hlo, hhi⟩
        have hf : Nat.floor ((K : ℝ) * (x : ℝ)) = a.val := by
          rw [Nat.floor_eq_iff (mul_nonneg (by positivity) x.property.1)]
          constructor
          · change (a : ℝ) / (K : ℝ) ≤ (x : ℝ) at hlo
            have := (div_le_iff₀ (by exact_mod_cast hK)).mp hlo
            simpa [mul_comm] using this
          · change (x : ℝ) < ((a : ℕ) + 1 : ℝ) / (K : ℝ) at hhi
            have := (lt_div_iff₀ (by exact_mod_cast hK)).mp hhi
            simpa [mul_comm] using this
        simp [fineIndex, hf, show (a : ℕ) ≤ K - 1 by omega]
    rw [he, design, unitInterval.volume_Ico]
    simp only [lo, hi]
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have hreal : (((a : ℕ) + 1 : ℝ) / K - (a : ℝ) / K) = 1 / K := by
      push_cast
      field_simp [hKR.ne']
      ring
    rw [hreal, ENNReal.ofReal_div_of_pos hKR]
    simp

/-- Under [the h0 condition](hyp:h0), [the h1 condition](hyp:h1), [the mark Flag Law probability statement holds](goal). -/
lemma markFlagLaw_probability (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (markFlagLaw ε) := by
  refine ⟨?_⟩
  simp only [markFlagLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add h0 (sub_nonneg.mpr h1)]
  norm_num

/-- [the disclosure Law probability statement holds](goal). -/
lemma disclosureLaw_probability (K M : ℕ) : IsProbabilityMeasure (disclosureLaw K M) := by
  refine ⟨?_⟩
  simp only [disclosureLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (-(K + 1 : ℤ)) = -((K + 1 : ℕ) : ℤ) by rfl]
  rw [zpow_neg, zpow_natCast]
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [show ENNReal.ofReal ((4 : ℝ) ^ (K + 1)) = (4 : ℝ≥0∞) ^ (K + 1) by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]]
  rw [show Fintype.card (CoefficientPairs K) = 4 ^ (K + 1) by
    simp [CoefficientPairs, Fintype.card_fun, Fintype.card_prod]]
  push_cast
  exact ENNReal.mul_inv_cancel (a := (4 : ℝ≥0∞) ^ (K + 1)) (by positivity) (by simp)

/-- Under [the hf condition](hyp:hf), [the hm condition](hyp:hm), [the hg condition](hyp:hg), [the i Indep Fun comp measure Preserving statement holds](goal). -/
lemma iIndepFun_comp_measurePreserving {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    {f : ∀ i, Ω' → β i} {g : Ω → Ω'}
    (hf : iIndepFun f ν) (hm : ∀ i, Measurable (f i))
    (hg : MeasurePreserving g μ ν) :
    iIndepFun (fun i => f i ∘ g) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hinter : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) := by
    exact S.measurableSet_biInter fun i hi => (hm i) (hsets i hi)
  have hpre (s : Set Ω') (hs : MeasurableSet s) : μ (g ⁻¹' s) = ν s := by
    rw [← Measure.map_apply hg.measurable hs, hg.map_eq]
  calc
    μ (⋂ i ∈ S, (f i ∘ g) ⁻¹' sets i) = μ (g ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i)) := by
      congr 1
      ext ω
      simp [Function.comp_def]
    _ = ν (⋂ i ∈ S, f i ⁻¹' sets i) := hpre _ hinter
    _ = ∏ i ∈ S, ν (f i ⁻¹' sets i) :=
      hf.measure_inter_preimage_eq_mul S hsets
    _ = ∏ i ∈ S, μ ((f i ∘ g) ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [show (f i ∘ g) ⁻¹' sets i = g ⁻¹' (f i ⁻¹' sets i) by rfl]
      exact (hpre _ ((hm i) (hsets i hi))).symm

/-- Under [the hK condition](hyp:hK), [the hε0 condition](hyp:hε0), [the hε1 condition](hyp:hε1), [the common Augmentation uniform Marked Sample statement holds](goal). -/
lemma commonAugmentation_uniformMarkedSample (n K M : ℕ) (ε : ℝ)
    (hK : 0 < K) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Causalean.Stat.RandomGraph.PathOccupancy.UniformMarkedSample
      (commonAugmentation n K M ε)
      (fun i aug => occCell K hK (aug.1 i)) (fun i aug => aug.2.1 i) ε := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε0 hε1
  letI : IsProbabilityMeasure (disclosureLaw K M) := disclosureLaw_probability K M
  let μX := Measure.pi (fun _ : Fin n => design)
  let μB := Measure.pi (fun _ : Fin n => markFlagLaw ε)
  let μD := disclosureLaw K M
  letI : IsProbabilityMeasure μX := by dsimp [μX]; infer_instance
  letI : IsProbabilityMeasure μB := by dsimp [μB]; infer_instance
  letI : IsProbabilityMeasure μD := by dsimp [μD]; infer_instance
  letI : IsProbabilityMeasure (μB.prod μD) := by infer_instance
  have hcommon : commonAugmentation n K M ε = μX.prod (μB.prod μD) := rfl
  have hfst : MeasurePreserving (fun aug : Augmentation n K => aug.1)
      (commonAugmentation n K M ε) μX := by
    rw [hcommon]
    exact measurePreserving_fst
  have hsndfst : MeasurePreserving (fun aug : Augmentation n K => aug.2.1)
      (commonAugmentation n K M ε) μB := by
    rw [hcommon]
    exact (measurePreserving_fst (μ := μB) (ν := μD)).comp
      (measurePreserving_snd (μ := μX) (ν := μB.prod μD))
  refine {
    probability := by rw [hcommon]; infer_instance
    epsilon_nonneg := hε0
    epsilon_le_one := hε1
    cells_measurable := fun i => (measurable_occCell K hK).comp
      ((measurable_pi_apply i).comp measurable_fst)
    marks_measurable := fun i => (measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd)
    cells_uniform := ?_
    marks_bernoulli := ?_
    cells_independent := ?_
    marks_independent := ?_
    blocks_independent := ?_ }
  · intro i a
    have heval : MeasurePreserving (fun xs : Fin n → unitInterval => xs i) μX design := by
      dsimp [μX]
      exact measurePreserving_eval _ i
    have hp := (heval.comp hfst)
    have hs : MeasurableSet {x : unitInterval | occCell K hK x = a} :=
      (measurable_occCell K hK) (MeasurableSet.singleton a)
    change (commonAugmentation n K M ε)
      (((fun xs : Fin n → unitInterval => xs i) ∘ fun aug : Augmentation n K => aug.1) ⁻¹'
        {x | occCell K hK x = a}) = _
    rw [← Measure.map_apply hp.measurable hs, hp.map_eq]
    exact occCell_fiber K hK a
  · intro i b
    have heval : MeasurePreserving (fun bs : Fin n → Bool => bs i) μB (markFlagLaw ε) := by
      dsimp [μB]
      exact measurePreserving_eval _ i
    have hp := heval.comp hsndfst
    change (commonAugmentation n K M ε)
      (((fun bs : Fin n → Bool => bs i) ∘ fun aug : Augmentation n K => aug.2.1) ⁻¹' {b}) = _
    rw [← Measure.map_apply hp.measurable (MeasurableSet.singleton b), hp.map_eq]
    cases b <;> simp [markFlagLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  · have hi : iIndepFun (fun i (xs : Fin n → unitInterval) => occCell K hK (xs i)) μX := by
      dsimp [μX]
      exact iIndepFun_pi (fun _ => (measurable_occCell K hK).aemeasurable)
    exact iIndepFun_comp_measurePreserving hi
      (fun i => (measurable_occCell K hK).comp (measurable_pi_apply i)) hfst
  · have hi : iIndepFun (fun i (bs : Fin n → Bool) => bs i) μB := by
      dsimp [μB]
      exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    exact iIndepFun_comp_measurePreserving hi (fun i => measurable_pi_apply i) hsndfst
  · rw [hcommon]
    exact indepFun_prod
      (measurable_pi_lambda _ (fun i => (measurable_occCell K hK).comp (measurable_pi_apply i)))
      measurable_fst

/-- [the measurable Set component Edge statement holds](goal). -/
lemma measurableSet_componentEdge (n K M : ℕ) (i j : Fin n) :
    MeasurableSet {aug : Augmentation n K | componentEdge n K M aug i j} := by
  let f (aug : Augmentation n K) : ℕ × ℕ × ℕ × ℕ :=
    (fineIndex M (aug.1 i), fineIndex M (aug.1 j),
      fineIndex K (aug.1 i), fineIndex K (aug.1 j))
  let s : Set (ℕ × ℕ × ℕ × ℕ) := {z |
    z.1 = z.2.1 ∧ (z.2.2.1 = z.2.2.2 ∨
      ((z.2.2.1 + 1 = z.2.2.2 ∨ z.2.2.2 + 1 = z.2.2.1) ∧
        max z.2.2.1 z.2.2.2 * M % K ≠ 0))}
  have hf : Measurable f := by fun_prop
  have hs : MeasurableSet s := MeasurableSet.of_discrete
  exact hs.preimage hf

/-- [the component Edge eqv Gen iff statement holds](goal). -/
lemma componentEdge_eqvGen_iff (n K M : ℕ) (aug : Augmentation n K) (i j : Fin n) :
    Relation.EqvGen (componentEdge n K M aug) i j ↔
      Relation.ReflTransGen (componentEdge n K M aug) i j := by
  constructor
  · intro hij
    induction hij with
    | rel i j hij => exact .single hij
    | refl i => exact .refl
    | symm i j hij ih => exact component_connected_symm n K M aug ih
    | trans i j k hij hjk ihij ihjk => exact ihij.trans ihjk
  · intro hij
    induction hij with
    | refl => exact .refl _
    | tail h hij ih => exact .trans _ _ _ ih (.rel _ _ hij)

/-- [the path components eq statement holds](goal). -/
lemma path_components_eq (n K M : ℕ) (aug : Augmentation n K) :
    Causalean.Stat.RandomGraph.PathOccupancy.components (componentEdge n K M aug) =
      components n K M aug := by
  classical
  unfold Causalean.Stat.RandomGraph.PathOccupancy.components components
  apply Finset.image_congr
  intro i _
  ext j
  simp only [Causalean.Stat.RandomGraph.PathOccupancy.component, componentOf,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact componentEdge_eqvGen_iff n K M aug i j

/-- Under [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the component Edge admissible statement holds](goal). -/
lemma componentEdge_admissible (n K M : ℕ) (hK : 0 < K) (hM : 0 < M)
    (hdiv : M ∣ K) (aug : Augmentation n K) :
    Causalean.Stat.RandomGraph.PathOccupancy.Admissible M
      (fun i => occCell K hK (aug.1 i)) (componentEdge n K M aug) := by
  intro i j hij
  constructor
  · unfold Causalean.Stat.RandomGraph.PathOccupancy.Adjacent occCell
    change fineIndex K (aug.1 i) ≤ fineIndex K (aug.1 j) + 1 ∧
      fineIndex K (aug.1 j) ≤ fineIndex K (aug.1 i) + 1
    rcases hij.2 with hsame | ⟨hadj, _⟩
    · omega
    · omega
  · unfold occCell
    change fineIndex K (aug.1 i) / (K / M) = fineIndex K (aug.1 j) / (K / M)
    rw [fineIndex_refinement K M hK hM hdiv, fineIndex_refinement K M hK hM hdiv]
    exact hij.1

/-- Under [the henv condition](hyp:henv), [the activity A le single Score statement holds](goal). -/
lemma activityA_le_singleScore (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (henv : ∀ C ∈ components n K M aug,
      componentEvenActivity n K M a u aug C ≤
        if 2 ≤ C.card ∧ 2 ≤ (C.filter (fun i => aug.2.1 i)).card then
          2 ^ 14 * a ^ 4 * u ^ 4 * (C.card : ℝ) ^ 8 * 8 ^ C.card else 0) :
    activityA n K M a u aug ≤
      2 ^ 14 * a ^ 4 * u ^ 4 *
        Causalean.Stat.RandomGraph.PathOccupancy.singleScore
          (componentEdge n K M aug) (fun i => aug.2.1 i) := by
  unfold activityA Causalean.Stat.RandomGraph.PathOccupancy.singleScore
  rw [path_components_eq]
  calc
    _ ≤ ∑ C ∈ components n K M aug,
        if 2 ≤ C.card ∧ 2 ≤ (C.filter (fun i => aug.2.1 i)).card then
          2 ^ 14 * a ^ 4 * u ^ 4 * (C.card : ℝ) ^ 8 * 8 ^ C.card else 0 :=
      Finset.sum_le_sum fun C hC => henv C hC
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C hC
      unfold Causalean.Stat.RandomGraph.PathOccupancy.singleWeight
      unfold Causalean.Stat.RandomGraph.PathOccupancy.markCount
      by_cases hm : 2 ≤ (C.filter (fun i => aug.2.1 i = true)).card
      · have hs : 2 ≤ C.card := hm.trans (Finset.card_filter_le _ _)
        simp [hm, hs]
        ring
      · simp [hm]

/-- Under [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hdiv condition](hyp:hdiv), [the hC condition](hyp:hC), [the hD condition](hyp:hD), [the hpair condition](hyp:hpair), [the same Coarse Pair of pair Index eq statement holds](goal). -/
lemma sameCoarsePair_of_pairIndex_eq (n K M : ℕ) (hK : 0 < K) (hM : 0 < M)
    (heven : 2 ∣ M) (hdiv : M ∣ K) (aug : Augmentation n K)
    (C D : Finset (Fin n)) (hC : C ∈ components n K M aug)
    (hD : D ∈ components n K M aug) (hpair : pairIndex M aug C = pairIndex M aug D) :
    Causalean.Stat.RandomGraph.PathOccupancy.SameCoarsePair M C D
      (fun i => occCell K hK (aug.1 i)) := by
  have hCne : C.Nonempty := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨i, self_mem_componentOf n K M aug i⟩
  obtain ⟨i, hi⟩ := hCne
  let p := pairIndex M aug C
  have hp : p < M / 2 := by
    dsimp [p]
    rw [pairIndex_eq_of_mem_component n K M aug hC hi]
    obtain ⟨r, hr⟩ := heven
    subst M
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2
    have hf : fineIndex (2 * r) (aug.1 i) < 2 * r := by
      simp only [fineIndex]
      omega
    omega
  refine ⟨p, hp, ?_, ?_⟩
  · intro j hj
    unfold Causalean.Stat.RandomGraph.PathOccupancy.pairClass occCell
    rw [Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
      fineIndex_refinement K M hK hM hdiv]
    exact (pairIndex_eq_of_mem_component n K M aug hC hj).symm
  · intro j hj
    unfold Causalean.Stat.RandomGraph.PathOccupancy.pairClass occCell
    rw [Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
      fineIndex_refinement K M hK hM hdiv]
    dsimp [p]
    rw [hpair]
    exact (pairIndex_eq_of_mem_component n K M aug hD hj).symm

/-- Under [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hdiv condition](hyp:hdiv), [the hC condition](hyp:hC), [the hD condition](hyp:hD), [the hnonneg condition](hyp:hnonneg), [the henv condition](hyp:henv), [the hpair condition](hyp:hpair), [the odd product le pair Weight statement holds](goal). -/
lemma odd_product_le_pairWeight (n K M : ℕ) (a u : ℝ) (hK : 0 < K) (hM : 0 < M)
    (heven : 2 ∣ M) (hdiv : M ∣ K) (aug : Augmentation n K)
    (C D : Finset (Fin n)) (hC : C ∈ components n K M aug)
    (hD : D ∈ components n K M aug)
    (hnonneg : ∀ E, 0 ≤ componentOddActivity n K M a u aug E)
    (henv : ∀ E ∈ components n K M aug,
      componentOddActivity n K M a u aug E ≤
        if 2 ≤ E.card ∧ 1 ≤ (E.filter (fun i => aug.2.1 i)).card then
          2 ^ 8 * a ^ 2 * u ^ 2 * (E.card : ℝ) ^ 4 * 8 ^ E.card else 0)
    (hpair : pairIndex M aug C = pairIndex M aug D) :
    componentOddActivity n K M a u aug C * componentOddActivity n K M a u aug D ≤
      2 ^ 16 * a ^ 4 * u ^ 4 *
        Causalean.Stat.RandomGraph.PathOccupancy.pairWeight M C D
          (fun i => occCell K hK (aug.1 i)) (fun i => aug.2.1 i) := by
  let cut (E : Finset (Fin n)) :=
    2 ≤ E.card ∧ 1 ≤ (E.filter (fun i => aug.2.1 i = true)).card
  by_cases hcutC : cut C
  · by_cases hcutD : cut D
    · have hsame := sameCoarsePair_of_pairIndex_eq n K M hK hM heven hdiv aug
        C D hC hD hpair
      unfold cut at hcutC hcutD
      have henvC := henv C hC
      have henvD := henv D hD
      rw [if_pos hcutC] at henvC
      rw [if_pos hcutD] at henvD
      have hmul := mul_le_mul henvC henvD
        (hnonneg D) (by positivity : 0 ≤ 2 ^ 8 * a ^ 2 * u ^ 2 * (C.card : ℝ) ^ 4 * 8 ^ C.card)
      calc
        _ ≤ (2 ^ 8 * a ^ 2 * u ^ 2 * (C.card : ℝ) ^ 4 * 8 ^ C.card) *
            (2 ^ 8 * a ^ 2 * u ^ 2 * (D.card : ℝ) ^ 4 * 8 ^ D.card) := hmul
        _ = _ := by
          unfold Causalean.Stat.RandomGraph.PathOccupancy.pairWeight
          unfold Causalean.Stat.RandomGraph.PathOccupancy.markCount
          simp [hcutC, hcutD, hsame]
          ring
    · have hz : componentOddActivity n K M a u aug D = 0 := by
        apply le_antisymm
        · have hd := henv D hD
          rw [if_neg hcutD] at hd
          exact hd
        · exact hnonneg D
      rw [hz, mul_zero]
      unfold Causalean.Stat.RandomGraph.PathOccupancy.pairWeight
      split <;> positivity
  · have hz : componentOddActivity n K M a u aug C = 0 := by
      apply le_antisymm
      · have hc := henv C hC
        rw [if_neg hcutC] at hc
        exact hc
      · exact hnonneg C
    rw [hz, zero_mul]
    unfold Causalean.Stat.RandomGraph.PathOccupancy.pairWeight
    split <;> positivity

/-- Under [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hdiv condition](hyp:hdiv), [the hnonneg condition](hyp:hnonneg), [the henv condition](hyp:henv), [the activity B le paired Score statement holds](goal). -/
lemma activityB_le_pairedScore (n K M : ℕ) (a u : ℝ) (hK : 0 < K) (hM : 0 < M)
    (heven : 2 ∣ M) (hdiv : M ∣ K) (aug : Augmentation n K)
    (hnonneg : ∀ E, 0 ≤ componentOddActivity n K M a u aug E)
    (henv : ∀ E ∈ components n K M aug,
      componentOddActivity n K M a u aug E ≤
        if 2 ≤ E.card ∧ 1 ≤ (E.filter (fun i => aug.2.1 i)).card then
          2 ^ 8 * a ^ 2 * u ^ 2 * (E.card : ℝ) ^ 4 * 8 ^ E.card else 0) :
    activityB n K M a u aug ≤
      2 ^ 16 * a ^ 4 * u ^ 4 *
        Causalean.Stat.RandomGraph.PathOccupancy.pairedScore M
          (componentEdge n K M aug) (fun i => occCell K hK (aug.1 i))
          (fun i => aug.2.1 i) := by
  have hinner (C : Finset (Fin n)) (hC : C ∈ components n K M aug) :
      (∑ D ∈ components n K M aug,
        if C ≠ D ∧ pairIndex M aug C = pairIndex M aug D then
          componentOddActivity n K M a u aug C * componentOddActivity n K M a u aug D else 0) =
      ∑ D ∈ (components n K M aug).erase C,
        if pairIndex M aug C = pairIndex M aug D then
          componentOddActivity n K M a u aug C * componentOddActivity n K M a u aug D else 0 := by
    rw [← Finset.sum_erase_add _ _ hC]
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, add_zero]
    apply Finset.sum_congr rfl
    intro D hD
    have hne : C ≠ D := fun heq => (Finset.mem_erase.mp hD).1 heq.symm
    simp [hne]
  unfold activityB
  rw [Finset.sum_congr rfl (fun C hC => hinner C hC)]
  unfold Causalean.Stat.RandomGraph.PathOccupancy.pairedScore
  rw [path_components_eq]
  rw [show 2 ^ 16 * a ^ 4 * u ^ 4 *
      ((1 / 2 : ℝ) * ∑ C ∈ components n K M aug,
        ∑ D ∈ (components n K M aug).erase C,
          Causalean.Stat.RandomGraph.PathOccupancy.pairWeight M C D
            (fun i => occCell K hK (aug.1 i)) (fun i => aug.2.1 i)) =
      (2 ^ 16 * a ^ 4 * u ^ 4 *
        (∑ C ∈ components n K M aug,
          ∑ D ∈ (components n K M aug).erase C,
            Causalean.Stat.RandomGraph.PathOccupancy.pairWeight M C D
              (fun i => occCell K hK (aug.1 i)) (fun i => aug.2.1 i))) / 2 by ring]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C hC
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D hD
  by_cases hp : pairIndex M aug C = pairIndex M aug D
  · simp only [hp, ↓reduceIte]
    exact odd_product_le_pairWeight n K M a u hK hM heven hdiv aug C D hC
      (Finset.mem_of_mem_erase hD) hnonneg henv hp
  · simp only [hp, ↓reduceIte]
    unfold Causalean.Stat.RandomGraph.PathOccupancy.pairWeight
    split <;> positivity

/-- Under [the hscale condition](hyp:hscale), [the component occupancy series bounds statement holds](goal). -/
lemma component_occupancy_series_bounds (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (hscale : 2 ^ 40 * n ≤ K) :
    let z : ℝ := 8 * Real.exp 1 * (n : ℝ) / K
    (∫ aug, activityA n K M a u aug ∂commonAugmentation n K M ε) ≤
        2 ^ 14 * a ^ 4 * u ^ 4 * ε ^ 2 * K *
          (∑' j : ℕ, (j + 2 : ℝ) ^ 11 * z ^ (j + 2)) ∧
    (∫ aug, activityB n K M a u aug ∂commonAugmentation n K M ε) ≤
        2 ^ 17 * a ^ 4 * u ^ 4 * ε ^ 2 * (K : ℝ) ^ 2 / M *
          (∑' j : ℕ, (j + 2 : ℝ) ^ 6 * z ^ (j + 2)) ^ 2 := by
  dsimp only
  have hn : 2 ≤ n := h.1
  have hM : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) h.2.2.2.2.1
  have hK : 0 < K := lt_of_lt_of_le (by omega : 0 < 16 * M) h.2.2.2.1
  obtain ⟨k, hk⟩ := h.2.1
  obtain ⟨m, hm⟩ := h.2.2.1
  have hKM := h.2.2.2.1
  have hM2 := h.2.2.2.2.1
  have hMK : M ≤ K := by omega
  have hmk : m ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hm, ← hk]
    exact hMK
  have hdiv : M ∣ K := by
    rw [hm, hk]
    exact Nat.pow_dvd_pow 2 hmk
  have heven : 2 ∣ M := by
    have hmpos : 0 < m := by
      by_contra hm0
      have : m = 0 := by omega
      have hMone : M = 1 := by simp [hm, this]
      omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hm, pow_succ]
    simpa only [mul_comm] using dvd_mul_right 2 (2 ^ r)
  have hdensity : (n : ℝ) / K ≤ (2 : ℝ) ^ (-40 : ℤ) := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have hsR : (2 : ℝ) ^ 40 * n ≤ K := by exact_mod_cast hscale
    rw [zpow_neg, inv_eq_one_div]
    exact (div_le_div_iff₀ hKR (by positivity : (0 : ℝ) < 2 ^ 40)).2 (by
      simpa [mul_comm] using hsR)
  have hsample := commonAugmentation_uniformMarkedSample n K M ε hK
    h.2.2.2.2.2.2.2.1.1.le h.2.2.2.2.2.2.2.1.2.le
  have hsingle := Causalean.Stat.RandomGraph.PathOccupancy.single_component_occupancy
    hsample hn h.2.2.2.2.1 heven h.2.2.2.1
    (fun aug => componentEdge n K M aug)
    (measurableSet_componentEdge n K M)
    (componentEdge_admissible n K M hK hM hdiv)
  have hpaired := Causalean.Stat.RandomGraph.PathOccupancy.paired_component_occupancy
    hsample hn h.2.2.2.2.1 heven hdiv h.2.2.2.1
    (fun aug => componentEdge n K M aug)
    (measurableSet_componentEdge n K M)
    (componentEdge_admissible n K M hK hM hdiv)
  obtain ⟨hsum11, hsum6, _, _⟩ := occupancy_collision_series_bounds n K hK hscale
  have hfinite11 : Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries 11 n K ≤
      ∑' j : ℕ, (j + 2 : ℝ) ^ 11 *
        (8 * Real.exp 1 * (n : ℝ) / K) ^ (j + 2) := by
    unfold Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries
    unfold Causalean.Stat.RandomGraph.PathOccupancy.occupancyZ
    exact hsum11.sum_le_tsum (Finset.range (n - 1)) (fun j _ => by positivity)
  have hfinite6 : Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries 6 n K ≤
      ∑' j : ℕ, (j + 2 : ℝ) ^ 6 *
        (8 * Real.exp 1 * (n : ℝ) / K) ^ (j + 2) := by
    unfold Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries
    unfold Causalean.Stat.RandomGraph.PathOccupancy.occupancyZ
    exact hsum6.sum_le_tsum (Finset.range (n - 1)) (fun j _ => by positivity)
  letI := commonAugmentation_isFiniteMeasure n K M ε
  have hi := component_activities_integrable n K M a u ε L h
  have henv := component_activity_envelopes n K M a u ε L h
  have hnonneg (aug : Augmentation n K) := component_activities_nonneg n K M a u hK
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  have hR := measurableSet_componentEdge n K M
  have hX (i : Fin n) : Measurable (fun aug : Augmentation n K => occCell K hK (aug.1 i)) :=
    (measurable_occCell K hK).comp ((measurable_pi_apply i).comp measurable_fst)
  have hB (i : Fin n) : Measurable (fun aug : Augmentation n K => aug.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hisingle := Causalean.Stat.RandomGraph.PathOccupancy.integrable_singleScore
    (commonAugmentation n K M ε) (fun aug => componentEdge n K M aug)
    (fun i aug => aug.2.1 i) hR hB
  have hipaired := Causalean.Stat.RandomGraph.PathOccupancy.integrable_pairedScore
    (commonAugmentation n K M ε) M (fun aug => componentEdge n K M aug)
    (fun i aug => occCell K hK (aug.1 i)) (fun i aug => aug.2.1 i) hR hX hB
  constructor
  · have hpoint : activityA n K M a u ≤ᵐ[commonAugmentation n K M ε]
        fun aug => 2 ^ 14 * a ^ 4 * u ^ 4 *
          Causalean.Stat.RandomGraph.PathOccupancy.singleScore
            (componentEdge n K M aug) (fun i => aug.2.1 i) := by
      filter_upwards [henv] with aug haug
      exact activityA_le_singleScore n K M a u aug (fun C hC => (haug C hC).1)
    calc
      _ ≤ ∫ aug, 2 ^ 14 * a ^ 4 * u ^ 4 *
          Causalean.Stat.RandomGraph.PathOccupancy.singleScore
            (componentEdge n K M aug) (fun i => aug.2.1 i) ∂commonAugmentation n K M ε :=
        MeasureTheory.integral_mono_ae hi.1 (hisingle.const_mul _) hpoint
      _ = 2 ^ 14 * a ^ 4 * u ^ 4 *
          (∫ aug, Causalean.Stat.RandomGraph.PathOccupancy.singleScore
            (componentEdge n K M aug) (fun i => aug.2.1 i) ∂commonAugmentation n K M ε) := by
        rw [integral_const_mul]
      _ ≤ 2 ^ 14 * a ^ 4 * u ^ 4 *
          (ε ^ 2 * K * Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries 11 n K) :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)
      _ ≤ _ := by
        calc
          _ = (2 ^ 14 * a ^ 4 * u ^ 4 * ε ^ 2 * K) *
              Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries 11 n K := by ring
          _ ≤ (2 ^ 14 * a ^ 4 * u ^ 4 * ε ^ 2 * K) *
              (∑' j : ℕ, (j + 2 : ℝ) ^ 11 *
                (8 * Real.exp 1 * (n : ℝ) / K) ^ (j + 2)) :=
            mul_le_mul_of_nonneg_left hfinite11 (by positivity)
          _ = _ := by ring
  · have hpoint : activityB n K M a u ≤ᵐ[commonAugmentation n K M ε]
        fun aug => 2 ^ 16 * a ^ 4 * u ^ 4 *
          Causalean.Stat.RandomGraph.PathOccupancy.pairedScore M
            (componentEdge n K M aug) (fun i => occCell K hK (aug.1 i))
            (fun i => aug.2.1 i) := by
      filter_upwards [henv] with aug haug
      exact activityB_le_pairedScore n K M a u hK hM heven hdiv aug
        (fun E => (hnonneg aug E).2) (fun E hE => (haug E hE).2)
    calc
      _ ≤ ∫ aug, 2 ^ 16 * a ^ 4 * u ^ 4 *
          Causalean.Stat.RandomGraph.PathOccupancy.pairedScore M
            (componentEdge n K M aug) (fun i => occCell K hK (aug.1 i))
            (fun i => aug.2.1 i) ∂commonAugmentation n K M ε :=
        MeasureTheory.integral_mono_ae hi.2 (hipaired.const_mul _) hpoint
      _ = 2 ^ 16 * a ^ 4 * u ^ 4 *
          (∫ aug, Causalean.Stat.RandomGraph.PathOccupancy.pairedScore M
            (componentEdge n K M aug) (fun i => occCell K hK (aug.1 i))
            (fun i => aug.2.1 i) ∂commonAugmentation n K M ε) := by
        rw [integral_const_mul]
      _ ≤ 2 ^ 16 * a ^ 4 * u ^ 4 *
          (2 * ε ^ 2 * (K : ℝ) ^ 2 / M *
            Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries 6 n K ^ 2) :=
        mul_le_mul_of_nonneg_left hpaired (by positivity)
      _ ≤ _ := by
        have hseries_nonneg : 0 ≤ Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries 6 n K := by
          unfold Causalean.Stat.RandomGraph.PathOccupancy.occupancySeries
          unfold Causalean.Stat.RandomGraph.PathOccupancy.occupancyZ
          exact Finset.sum_nonneg fun _ _ => by
            have : (0 : ℝ) < K := by exact_mod_cast hK
            positivity
        have hpow := pow_le_pow_left₀ hseries_nonneg hfinite6 2
        calc
          _ ≤ 2 ^ 16 * a ^ 4 * u ^ 4 *
              (2 * ε ^ 2 * (K : ℝ) ^ 2 / M *
                (∑' j : ℕ, (j + 2 : ℝ) ^ 6 *
                  (8 * Real.exp 1 * (n : ℝ) / K) ^ (j + 2)) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left hpow
            positivity
          _ = _ := by ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
