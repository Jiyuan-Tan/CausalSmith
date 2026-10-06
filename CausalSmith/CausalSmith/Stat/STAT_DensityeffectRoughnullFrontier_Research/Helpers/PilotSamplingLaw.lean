module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotDensityTail
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalConstruction

/-!
The retained covariate/treatment design law and its conditional outcome kernel
recover the actual observed law. This transports conditional histogram tails to
the independent training block of the randomized sampling law.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The supported covariate and treatment marginal used by histogram Bernstein. -/
-- @node: pilotDesignLaw
def pilotDesignLaw (P : ObsLaw) : Measure PilotDesign :=
  causalCovariateLaw ⊗ₘ causalTreatmentKernel P

-- @node: pilotDesignLaw_isProbabilityMeasure
instance pilotDesignLaw_isProbabilityMeasure (P : ObsLaw) :
    IsProbabilityMeasure (pilotDesignLaw P) := by
  unfold pilotDesignLaw
  infer_instance

/-- Assemble the ambient observation from supported design and outcome. -/
-- @node: pilotRecordMap
def pilotRecordMap (z : PilotDesign × ℝ) : Omega := (z.1.1.val, z.1.2, z.2)

-- @node: measurable_pilotRecordMap
@[fun_prop] lemma measurable_pilotRecordMap : Measurable pilotRecordMap := by
  unfold pilotRecordMap
  fun_prop

/-- The treatment/outcome experiment has the same arm rectangles as the
independent potential-outcome construction after selecting the observed arm. -/
-- @node: pilot_selected_rectangle_eq
lemma pilot_selected_rectangle_eq (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1)
    (a : Bool) (D : Set ℝ) (hD : MeasurableSet D) :
    (causalTreatmentKernel P ⊗ₖ pilotOutcomeKernel P) x ({a} ×ˢ D) =
      causalExperimentKernel P x
        {z | z.1 = a ∧ (if z.1 then z.2.2 else z.2.1) ∈ D} := by
  rw [Kernel.compProd_apply_prod (measurableSet_singleton a) hD]
  simp only [lintegral_singleton, pilotOutcomeKernel_apply,
    causalTreatmentKernel_apply_singleton]
  cases a
  · have he : {z : Bool × (ℝ × ℝ) | z.1 = false ∧
        (if z.1 then z.2.2 else z.2.1) ∈ D} = {false} ×ˢ (D ×ˢ Set.univ) := by
      ext z
      rcases z with ⟨b, v⟩
      cases b <;> simp
    rw [he, causalExperimentKernel_apply_rectangle]
    simp [mul_comm]
  · have he : {z : Bool × (ℝ × ℝ) | z.1 = true ∧
        (if z.1 then z.2.2 else z.2.1) ∈ D} = {true} ×ˢ (Set.univ ×ˢ D) := by
      ext z
      rcases z with ⟨b, v⟩
      cases b <;> simp
    rw [he, causalExperimentKernel_apply_rectangle]
    simp [mul_comm]

/-- Arm rectangles of the retained-design law agree with the observed marginal
of the already verified causal construction. -/
-- @node: pilot_jointLaw_map_rectangle
lemma pilot_jointLaw_map_rectangle (P : ObsLaw) (B D : Set ℝ)
    (hB : MeasurableSet B) (hD : MeasurableSet D) (a : Bool) :
    ((pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P).map pilotRecordMap)
      (B ×ˢ ({a} ×ˢ D)) =
    ((constructedCausalLaw P).map Prod.fst) (B ×ˢ ({a} ×ˢ D)) := by
  rw [pilotDesignLaw, ← Measure.compProd_assoc,
    Measure.map_map measurable_pilotRecordMap (by fun_prop)]
  rw [constructedCausalLaw,
    Measure.map_map measurable_fst measurable_causalConsistencyMap]
  rw [Measure.map_apply (measurable_pilotRecordMap.comp (by fun_prop))
    (hB.prod ((measurableSet_singleton a).prod hD)),
    Measure.map_apply (measurable_fst.comp measurable_causalConsistencyMap)
      (hB.prod ((measurableSet_singleton a).prod hD))]
  have hl : (pilotRecordMap ∘ MeasurableEquiv.prodAssoc.symm) ⁻¹'
      (B ×ˢ ({a} ×ˢ D)) = (Subtype.val ⁻¹' B) ×ˢ ({a} ×ˢ D) := by
    ext z
    rfl
  have hr : (Prod.fst ∘ causalConsistencyMap) ⁻¹' (B ×ˢ ({a} ×ˢ D)) =
      (Subtype.val ⁻¹' B) ×ˢ
        {z | z.1 = a ∧ (if z.1 then z.2.2 else z.2.1) ∈ D} := by
    ext z
    simp [causalConsistencyMap]
  rw [hl, hr, Measure.compProd_apply_prod (hB.preimage measurable_subtype_coe)
      ((measurableSet_singleton a).prod hD),
    Measure.compProd_apply_prod (hB.preimage measurable_subtype_coe)
      (show MeasurableSet {z : Bool × (ℝ × ℝ) | z.1 = a ∧
          (if z.1 then z.2.2 else z.2.1) ∈ D} from
        (measurableSet_eq_fun measurable_fst measurable_const).inter
        (hD.preimage ((measurable_snd.comp measurable_snd).ite
          (measurableSet_eq_fun measurable_fst measurable_const)
          (measurable_fst.comp measurable_snd))))]
  apply lintegral_congr
  intro x
  exact pilot_selected_rectangle_eq P x a D hD

/-- The retained-design conditional law is exactly the specified observed law. -/
-- @node: pilot_jointLaw_map_record
lemma pilot_jointLaw_map_record (P : ObsLaw) :
    (pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P).map pilotRecordMap = P.law := by
  rw [← constructedCausalLaw_map_observed P]
  apply Measure.ext_prod₃
  intro B C D hB hC hD
  by_cases hf : false ∈ C <;> by_cases ht : true ∈ C
  · have hC : C = Set.univ := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    let S0 : Set Omega := B ×ˢ ({false} ×ˢ D)
    let S1 : Set Omega := B ×ˢ ({true} ×ˢ D)
    have hu : B ×ˢ (Set.univ ×ˢ D) = S0 ∪ S1 := by
      ext o
      cases o.2.1 <;> simp [S0, S1] <;> aesop
    rw [hu, measure_union (by simp [S0])
      (hB.prod ((measurableSet_singleton true).prod hD)),
      measure_union (by simp [S0])
        (hB.prod ((measurableSet_singleton true).prod hD))]
    exact congrArg₂ (· + ·) (pilot_jointLaw_map_rectangle P B D hB hD false)
      (pilot_jointLaw_map_rectangle P B D hB hD true)
  · have hC : C = {false} := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    exact pilot_jointLaw_map_rectangle P B D hB hD false
  · have hC : C = {true} := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    exact pilot_jointLaw_map_rectangle P B D hB hD true
  · have hC : C = ∅ := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    simp

/-- Coordinatewise reassembly preserves the entire IID observation law. -/
-- @node: pilot_iid_jointLaw_map_record
lemma pilot_iid_jointLaw_map_record (P : ObsLaw) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P)).map
      (fun z i => pilotRecordMap (z i)) = dataLaw P m := by
  rw [Measure.pi_map_pi (fun _ => measurable_pilotRecordMap.aemeasurable)]
  simp only [pilot_jointLaw_map_record, dataLaw]

/-- Reassembly is a measurable embedding, so arbitrary pilot-error events
can be transported without assuming measurability of a supremum over points. -/
-- @node: measurableEmbedding_pilot_record_vector
lemma measurableEmbedding_pilot_record_vector (m : ℕ) :
    MeasurableEmbedding (fun z : Fin m → PilotDesign × ℝ =>
      fun i => pilotRecordMap (z i)) := by
  have hm : Measurable (fun z : Fin m → PilotDesign × ℝ =>
      fun i => pilotRecordMap (z i)) := by fun_prop
  apply hm.measurableEmbedding
  intro z w h
  funext i
  have hi := congrFun h i
  simp only [pilotRecordMap, Prod.mk.injEq] at hi
  exact Prod.ext (Prod.ext (Subtype.ext hi.1) hi.2.1) hi.2.2

/-- Actual-law normalized density tail on the arm-count-good event. This is
precisely the outcome part of the roadmap after integrating retained designs. -/
-- @node: pilot_density_actual_iid_tail_le
lemma pilot_density_actual_iid_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my) :
    (dataLaw P m).real
      {train | (∀ a x, x ∈ Set.Icc 0 1 →
        (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x) ∧
        ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
          hAllow (2 ^ 16) m mx my < |densityPilot train mx my a x y - P.eta a x y|} ≤
      4 * (mx : ℝ) * my * Real.exp (-(30 * Real.log m)) := by
  rw [← pilot_iid_jointLaw_map_record P m, measureReal_def,
    (measurableEmbedding_pilot_record_vector m).map_apply]
  apply le_trans (b := (Measure.pi (fun _ : Fin m =>
    pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P)).real
      {z | (∀ e : PilotDesign, (m : ℝ) / (8 * mx) ≤
        Causalean.Stat.Concentration.ConditionalBernstein.cellCount
          (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) (fun i => (z i).1)) ∧
        ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
          hAllow (2 ^ 16) m mx my <
            |densityPilot (pilotTrainingRecords (fun i => (z i).1) (fun i => (z i).2))
              mx my a x y - P.eta a x y|})
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro z ⟨hc, he⟩
    refine ⟨?_, he⟩
    intro e
    rw [pilot_bernstein_cellCount_eq mx hmx]
    exact hc e.2 e.1.val e.1.property
  · exact pilot_density_public_iid_tail_le P hModel (pilotDesignLaw P) mx my hm hmx hmy

/-- The randomized sampling law budgets arbitrary training-block events by
their IID observation measure, even before proving event measurability. -/
-- @node: samplingLaw_foldData_real_le
lemma samplingLaw_foldData_real_le (P : ObsLaw) (n : ℕ)
    (ν : Measure (SampleSpace n)) (hSampling : SamplingLaw P n ν)
    (b : Fin 13) (E : Set (Data (roleSize n))) :
    ν.real {ω | foldData n ω.1 b ∈ E} ≤ (dataLaw P (roleSize n)).real E := by
  change ν = sampleLaw P n at hSampling
  subst ν
  have hm : Measurable (fun ω : SampleSpace n => foldData n ω.1 b) := by
    unfold foldData
    fun_prop
  let : IsProbabilityMeasure (dataLaw P (roleSize n)) := by
    unfold dataLaw
    infer_instance
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  have h := Measure.le_map_apply (μ := sampleLaw P n) hm.aemeasurable E
  rwa [sampleLaw_foldData_map] at h

/-- The density tail now applies to the actual training fold and includes
integration over all other roles and the independent public randomization. -/
-- @node: pilot_density_sampling_tail_le
lemma pilot_density_sampling_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (ν : Measure (SampleSpace (13 * m))) (hSampling : SamplingLaw P (13 * m) ν) :
    ν.real {ω | (∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x) ∧
      ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
        hAllow (2 ^ 16) m mx my <
          |densityPilot (foldData (13 * m) ω.1 0) mx my a x y - P.eta a x y|} ≤
      4 * (mx : ℝ) * my * Real.exp (-(30 * Real.log m)) := by
  let E : Set (Data (roleSize (13 * m))) := {train |
    (∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x) ∧
    ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
      hAllow (2 ^ 16) m mx my < |densityPilot train mx my a x y - P.eta a x y|}
  exact (samplingLaw_foldData_real_le P (13 * m) ν hSampling 0 E).trans (by
    have hmrole : roleSize (13 * m) = m := by simp [roleSize]
    dsimp only [E]
    generalize roleSize (13 * m) = r at *
    subst r
    exact pilot_density_actual_iid_tail_le P hModel m mx my hm hmx hmy)

/-- Separate the two remaining design/propensity probabilities from the
now verified actual-law outcome budget. -/
-- @node: pilot_good_sampling_tail_le
lemma pilot_good_sampling_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (ν : Measure (SampleSpace (13 * m))) (hSampling : SamplingLaw P (13 * m) ν) :
    ν.real {ω | ¬GoodPilot P (foldData (13 * m) ω.1 0) (2 ^ 16) mx my} ≤
      ν.real {ω | ¬(∀ a x, x ∈ Set.Icc 0 1 →
        (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x)} +
      ν.real {ω | (∀ a x, x ∈ Set.Icc 0 1 →
        (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x) ∧
        ∃ a x, x ∈ Set.Icc 0 1 ∧ hAllow (2 ^ 16) m mx my <
        |pilotPi (foldData (13 * m) ω.1 0) mx a x - pi P a x|} +
      4 * (mx : ℝ) * my * Real.exp (-(30 * Real.log m)) := by
  let : IsProbabilityMeasure ν := by
    let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
    change ν = sampleLaw P (13 * m) at hSampling
    rw [hSampling]
    unfold sampleLaw dataLaw
    infer_instance
  let C : Set (SampleSpace (13 * m)) := {ω | ¬(∀ a x, x ∈ Set.Icc 0 1 →
    (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x)}
  let E : Set (SampleSpace (13 * m)) := {ω |
    (∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x) ∧
    ∃ a x, x ∈ Set.Icc 0 1 ∧
    hAllow (2 ^ 16) m mx my < |pilotPi (foldData (13 * m) ω.1 0) mx a x - pi P a x|}
  let D : Set (SampleSpace (13 * m)) := {ω | (∀ a x, x ∈ Set.Icc 0 1 →
    (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x) ∧
    ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ hAllow (2 ^ 16) m mx my <
      |densityPilot (foldData (13 * m) ω.1 0) mx my a x y - P.eta a x y|}
  have hsub : {ω | ¬GoodPilot P (foldData (13 * m) ω.1 0) (2 ^ 16) mx my} ⊆
      (C ∪ E) ∪ D := by
    intro ω hbad
    by_cases hc : ω ∈ C
    · exact Or.inl (Or.inl hc)
    by_cases he : ω ∈ E
    · exact Or.inl (Or.inr he)
    apply Or.inr
    refine ⟨Classical.not_not.mp hc, ?_⟩
    by_contra hd
    apply hbad
    have hmrole : roleSize (13 * m) = m := by simp [roleSize]
    unfold GoodPilot
    conv_rhs => rw [hmrole]
    apply pilotError_le_of_pointwise
    · intro a x hx
      exact le_of_not_gt (fun h => he ⟨Classical.not_not.mp hc, a, x, hx, h⟩)
    · intro a x y hx hy
      exact le_of_not_gt (fun h => hd ⟨a, x, y, hx, hy, h⟩)
  calc
    _ ≤ ν.real ((C ∪ E) ∪ D) := measureReal_mono hsub
    _ ≤ ν.real (C ∪ E) + ν.real D := measureReal_union_le _ _
    _ ≤ (ν.real C + ν.real E) + ν.real D :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add le_rfl
      (pilot_density_sampling_tail_le P hModel m mx my hm hmx hmy ν hSampling)

end CausalSmith.Stat.DensityEffectRoughNull
