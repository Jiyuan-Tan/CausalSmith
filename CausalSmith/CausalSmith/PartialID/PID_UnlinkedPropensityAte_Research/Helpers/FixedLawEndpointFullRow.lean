module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawEndpointAssembly

/-! Full-row realization of the fixed-law endpoint constructions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), [this definition](goal) introduces the corresponding object. -/
def endpointFullLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    Measure (FullRow ε J) :=
  ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity false)).map (reconstructedFullRow g false) +
    ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity true)).map (reconstructedFullRow g true)

private lemma endpointAssignmentDensity_measurable {ε : ℝ}
    (a : ArmSpace) : Measurable
      (reconstructedAssignmentDensity (ε := ε) a) := by
  cases a
  · change Measurable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      ENNReal.ofReal (1 - (p.1 : ℝ)))
    fun_prop
  · change Measurable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      ENNReal.ofReal (p.1 : ℝ))
    fun_prop

private lemma endpointAssignmentDensity_sum {ε : ℝ}
    (hOverlap : Overlap ε)
    (p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :
    reconstructedAssignmentDensity false p +
      reconstructedAssignmentDensity true p = 1 := by
  have he0 : 0 ≤ (p.1 : ℝ) :=
    le_trans hOverlap.1.le p.1.property.1
  have he1 : (p.1 : ℝ) ≤ 1 := by
    linarith [p.1.property.2, hOverlap.1]
  unfold reconstructedAssignmentDensity armProb
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr he1) he0]
  norm_num
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointAssignmentMeasures_sum {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        (reconstructedAssignmentDensity false) +
      (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        (reconstructedAssignmentDensity true) =
      endpointLatentLaw H g Prel hMass hOverlap upper0 upper1 := by
  rw [← withDensity_add_left (endpointAssignmentDensity_measurable false)]
  have hfun : reconstructedAssignmentDensity false +
      reconstructedAssignmentDensity true =
      (1 : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) → ENNReal) := by
    funext p
    exact endpointAssignmentDensity_sum hOverlap p
  rw [hfun, withDensity_one]

private lemma endpoint_map_withDensity_of_comp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (m : α → β) (hm : Measurable m)
    (f : β → ENNReal) (hf : Measurable f) :
    (μ.withDensity (f ∘ m)).map m = (μ.map m).withDensity f := by
  ext B hB
  rw [Measure.map_apply hm hB,
    withDensity_apply _ (hB.preimage hm), withDensity_apply _ hB,
    setLIntegral_map hB hf hm]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointAssignedPotentialLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) (a : ArmSpace) :
    ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        (reconstructedAssignmentDensity a)).map
        (fun p => (p.1, if a then p.2.2 else p.2.1)) =
      endpointAssignedArmLaw H g Prel hMass hOverlap a
        (if a then upper1 else upper0) := by
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    change ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        ((fun q : ScoreSpace ε × OutcomeSpace =>
          ENNReal.ofReal (1 - (q.1 : ℝ))) ∘
          (fun p => (p.1, p.2.1)))).map (fun p => (p.1, p.2.1)) = _
    rw [endpoint_map_withDensity_of_comp _ _ (by fun_prop) _ (by fun_prop),
      endpointLatentLaw_map_control H g Prel hMass hOverlap upper0 upper1]
    simpa [armProb] using
      endpointArmPotentialLaw_retilt H g Prel hMass hOverlap false upper0
  · simp only [↓reduceIte]
    change ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        ((fun q : ScoreSpace ε × OutcomeSpace =>
          ENNReal.ofReal (q.1 : ℝ)) ∘
          (fun p => (p.1, p.2.2)))).map (fun p => (p.1, p.2.2)) = _
    rw [endpoint_map_withDensity_of_comp _ _ (by fun_prop) _ (by fun_prop),
      endpointLatentLaw_map_treated H g Prel hMass hOverlap upper0 upper1]
    simpa [armProb] using
      endpointArmPotentialLaw_retilt H g Prel hMass hOverlap true upper1
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    IsProbabilityMeasure
      (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) := by
  rw [isProbabilityMeasure_iff]
  unfold endpointFullLaw
  rw [Measure.add_apply,
    Measure.map_apply (reconstructedFullRow_measurable g hMass.2.2.1 false)
      MeasurableSet.univ,
    Measure.map_apply (reconstructedFullRow_measurable g hMass.2.2.1 true)
      MeasurableSet.univ]
  simp only [preimage_univ]
  rw [← Measure.add_apply,
    endpointAssignmentMeasures_sum H g Prel hMass hOverlap upper0 upper1]
  exact isProbabilityMeasure_iff.mp inferInstance
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_scoreMarginal {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    ScoreMarginal (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) H := by
  unfold ScoreMarginal endpointFullLaw
  rw [Measure.map_add _ _ (by unfold score; fun_prop),
    Measure.map_map (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hMass.2.2.1 false),
    Measure.map_map (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hMass.2.2.1 true)]
  change Measure.map Prod.fst
      ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        (reconstructedAssignmentDensity false)) +
      Measure.map Prod.fst
      ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        (reconstructedAssignmentDensity true)) = H
  rw [← Measure.map_add _ _ measurable_fst,
    endpointAssignmentMeasures_sum H g Prel hMass hOverlap upper0 upper1]
  exact endpointLatentLaw_fst H g Prel hMass hOverlap upper0 upper1
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_consistency {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    Consistency (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) := by
  unfold Consistency endpointFullLaw
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff
      (reconstructedFullRow_measurable g hMass.2.2.1 false).aemeasurable (by
        exact measurableSet_eq_fun (by unfold observed; fun_prop)
          (by
            have hcond : MeasurableSet {ω : FullRow ε J | arm ω = true} :=
              measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
            exact Measurable.ite hcond (by unfold outcome1; fun_prop)
              (by unfold outcome0; fun_prop)))]
    filter_upwards [] with p
    rfl
  · rw [ae_map_iff
      (reconstructedFullRow_measurable g hMass.2.2.1 true).aemeasurable (by
        exact measurableSet_eq_fun (by unfold observed; fun_prop)
          (by
            have hcond : MeasurableSet {ω : FullRow ε J | arm ω = true} :=
              measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
            exact Measurable.ite hcond (by unfold outcome1; fun_prop)
              (by unfold outcome0; fun_prop)))]
    filter_upwards [] with p
    rfl
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_deterministicRelease {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    DeterministicRelease g
      (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) := by
  unfold DeterministicRelease endpointFullLaw
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff
      (reconstructedFullRow_measurable g hMass.2.2.1 false).aemeasurable (by
        exact measurableSet_eq_fun (by unfold label; fun_prop)
          (hMass.2.2.1.comp (by unfold score; fun_prop)))]
    filter_upwards [] with p
    rfl
  · rw [ae_map_iff
      (reconstructedFullRow_measurable g hMass.2.2.1 true).aemeasurable (by
        exact measurableSet_eq_fun (by unfold label; fun_prop)
          (hMass.2.2.1.comp (by unfold score; fun_prop)))]
    filter_upwards [] with p
    rfl

private lemma endpointLatentScore_integrable {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    Integrable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      (p.1 : ℝ)) (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1) := by
  apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  rcases p.1.property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma endpointAssignmentTrue_real {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool)
    (D : Set (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)))
    (hD : MeasurableSet D) :
    ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity true)).real D =
      ∫ p in D, (p.1 : ℝ) ∂endpointLatentLaw H g Prel hMass hOverlap upper0 upper1 := by
  have hint : IntegrableOn
      (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) => (p.1 : ℝ)) D
      (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1) :=
    (endpointLatentScore_integrable H g Prel hMass hOverlap upper0 upper1).integrableOn
  unfold Measure.real reconstructedAssignmentDensity armProb
  rw [withDensity_apply _ hD]
  simp only [ite_true]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun p => by
      exact le_trans hOverlap.1.le p.1.property.1)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun p =>
    le_trans hOverlap.1.le p.1.property.1)]

private lemma endpointComponent_finite {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) (a : ArmSpace) :
    IsFiniteMeasure
      ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
        (reconstructedAssignmentDensity a)) := by
  let f : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) → ℝ :=
    fun p => armProb a p.1
  have hf : Integrable f
      (endpointLatentLaw H g Prel hMass hOverlap upper0 upper1) := by
    apply Integrable.of_bound (by
      dsimp [f]
      cases a <;> simp [armProb] <;> fun_prop) 1
    filter_upwards [] with p
    have he0 : 0 ≤ (p.1 : ℝ) := le_trans hOverlap.1.le p.1.property.1
    have he1 : (p.1 : ℝ) ≤ 1 := by linarith [p.1.property.2, hOverlap.1]
    cases a
    · change |1 - (p.1 : ℝ)| ≤ 1
      rw [abs_of_nonneg (by linarith)]
      linarith
    · change |(p.1 : ℝ)| ≤ 1
      rw [abs_of_nonneg he0]
      exact he1
  change IsFiniteMeasure
    ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (fun p => ENNReal.ofReal (f p)))
  exact isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral

private lemma endpointFullScore_integrable_finite {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsFiniteMeasure P] :
    Integrable (fun ω => (score ω : ℝ)) P := by
  apply Integrable.of_bound (by unfold score; fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  rcases (score ω).property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma endpointLatentScore_integrable_finite {ε : ℝ}
    (μ : Measure (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)))
    [IsFiniteMeasure μ] :
    Integrable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      (p.1 : ℝ)) μ := by
  apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  rcases p.1.property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_randomizedAssignment {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    RandomizedAssignment (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) := by
  intro B hB
  let L := endpointLatentLaw H g Prel hMass hOverlap upper0 upper1
  let M₀ := L.withDensity (reconstructedAssignmentDensity false)
  let M₁ := L.withDensity (reconstructedAssignmentDensity true)
  let D : Set (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :=
    {p | (p.1, p.2.1, p.2.2) ∈ B}
  have hD : MeasurableSet D := hB.preimage (by fun_prop)
  let S : Set (FullRow ε J) :=
    {ω | arm ω = true ∧ (score ω, outcome0 ω, outcome1 ω) ∈ B}
  let T : Set (FullRow ε J) :=
    {ω | (score ω, outcome0 ω, outcome1 ω) ∈ B}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const).inter
      (hB.preimage (by unfold score outcome0 outcome1; fun_prop))
  have hT : MeasurableSet T :=
    hB.preimage (by unfold score outcome0 outcome1; fun_prop)
  have hpre0S : reconstructedFullRow g false ⁻¹' S = ∅ := by
    ext p
    simp [S, reconstructedFullRow, arm]
  have hpre1S : reconstructedFullRow g true ⁻¹' S = D := by
    ext p
    simp [S, D, reconstructedFullRow, arm, score, outcome0, outcome1]
  have hpre0T : reconstructedFullRow g false ⁻¹' T = D := by
    ext p
    simp [T, D, reconstructedFullRow, score, outcome0, outcome1]
  have hpre1T : reconstructedFullRow g true ⁻¹' T = D := by
    ext p
    simp [T, D, reconstructedFullRow, score, outcome0, outcome1]
  letI : IsFiniteMeasure M₀ :=
    endpointComponent_finite H g Prel hMass hOverlap upper0 upper1 false
  letI : IsFiniteMeasure M₁ :=
    endpointComponent_finite H g Prel hMass hOverlap upper0 upper1 true
  have hmap0 : IsFiniteMeasure (M₀.map (reconstructedFullRow g false)) := ⟨by
    rw [Measure.map_apply (reconstructedFullRow_measurable g hMass.2.2.1 false)
      MeasurableSet.univ]
    simpa using measure_lt_top M₀ Set.univ
  ⟩
  have hmap1 : IsFiniteMeasure (M₁.map (reconstructedFullRow g true)) := ⟨by
    rw [Measure.map_apply (reconstructedFullRow_measurable g hMass.2.2.1 true)
      MeasurableSet.univ]
    simpa using measure_lt_top M₁ Set.univ
  ⟩
  change (endpointFullLaw H g Prel hMass hOverlap upper0 upper1).real S =
    ∫ ω in T, (score ω : ℝ) ∂endpointFullLaw H g Prel hMass hOverlap upper0 upper1
  have hleft : (endpointFullLaw H g Prel hMass hOverlap upper0 upper1).real S =
      ∫ p in D, (p.1 : ℝ) ∂L := by
    unfold endpointFullLaw
    rw [Measure.real_def, Measure.add_apply,
      Measure.map_apply (reconstructedFullRow_measurable g hMass.2.2.1 false) hS,
      Measure.map_apply (reconstructedFullRow_measurable g hMass.2.2.1 true) hS,
      hpre0S, hpre1S, measure_empty, zero_add]
    change M₁.real D = _
    exact endpointAssignmentTrue_real H g Prel hMass hOverlap upper0 upper1 D hD
  rw [hleft]
  unfold endpointFullLaw
  letI : IsFiniteMeasure (M₀.map (reconstructedFullRow g false)) := hmap0
  letI : IsFiniteMeasure (M₁.map (reconstructedFullRow g true)) := hmap1
  rw [Measure.restrict_add,
    integral_add_measure (endpointFullScore_integrable_finite _).integrableOn
      (endpointFullScore_integrable_finite _).integrableOn,
    setIntegral_map hT (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hMass.2.2.1 false).aemeasurable,
    setIntegral_map hT (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hMass.2.2.1 true).aemeasurable,
    hpre0T, hpre1T]
  change (∫ p in D, (p.1 : ℝ) ∂L) =
    (∫ p in D, (p.1 : ℝ) ∂M₀) + (∫ p in D, (p.1 : ℝ) ∂M₁)
  rw [← integral_add_measure
    (endpointLatentScore_integrable_finite M₀).integrableOn
    (endpointLatentScore_integrable_finite M₁).integrableOn]
  rw [← Measure.restrict_add,
    endpointAssignmentMeasures_sum H g Prel hMass hOverlap upper0 upper1]
/-- For [the specified mathematical inputs](hyp:J,z), [this definition](goal) introduces the corresponding object. -/
def endpointObservationReal {J : ℕ} (z : Observation J) :
    LabelSpace J × (ArmSpace × ℝ) :=
  (z.1, z.2.1, (z.2.2 : ℝ))

private lemma endpointObservationReal_measurable {J : ℕ} :
    Measurable (endpointObservationReal (J := J)) := by
  unfold endpointObservationReal
  fun_prop

private lemma endpointAssignedCell_releaseReal {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool)
    (r : LabelSpace J) :
    (if hq : 0 < armCellMass H g a r then
      ENNReal.ofReal (armCellMass H g a r) •
        boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
     else 0).map (fun p => (g p.1, a, (p.2 : ℝ))) =
      (Prel.restrict {z | z.1 = r ∧ z.2.1 = a}).map endpointObservationReal := by
  let μ := if hq : 0 < armCellMass H g a r then
      ENNReal.ofReal (armCellMass H g a r) •
        boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
    else 0
  let C : Set (Observation J) := {z | z.1 = r ∧ z.2.1 = a}
  have hμscore : ∀ᵐ p ∂μ, g p.1 = r := by
    dsimp only [μ]
    split
    · rename_i hq
      rw [ae_iff]
      have hbad : MeasurableSet
          {p : ScoreSpace ε × OutcomeSpace | ¬g p.1 = r} :=
        (measurableSet_eq_fun (hMass.2.2.1.comp measurable_fst)
          measurable_const).compl
      rw [Measure.smul_apply]
      apply mul_eq_zero.mpr
      right
      change (boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper)
        (Prod.fst ⁻¹' ({e : ScoreSpace ε | g e = r}ᶜ)) = 0
      rw [← Measure.map_apply measurable_fst
        (measurableSet_eq_fun hMass.2.2.1 measurable_const).compl]
      change (boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper).fst
        ({e : ScoreSpace ε | g e = r}ᶜ) = 0
      rw [boundedEndpointCellLaw_fst H g Prel hMass hOverlap a r hq upper]
      unfold armCellScoreLaw
      rw [Measure.smul_apply]
      apply mul_eq_zero.mpr
      right
      rw [Measure.restrict_apply
        (measurableSet_eq_fun hMass.2.2.1 measurable_const).compl]
      simp [cell]
    · simp
  have hPrel : ∀ᵐ z ∂Prel.restrict C, z.1 = r ∧ z.2.1 = a := by
    exact self_mem_ae_restrict (by
      exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
        (measurableSet_eq_fun (by fun_prop) measurable_const))
  have hleft : μ.map (fun p => (g p.1, a, (p.2 : ℝ))) =
      (μ.map (fun p => (p.2 : ℝ))).map (fun y => (r, a, y)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [hμscore] with p hp
    simp only [Function.comp_apply, hp]
  have hright : (Prel.restrict C).map endpointObservationReal =
      ((Prel.restrict C).map (fun z => (z.2.2 : ℝ))).map
        (fun y => (r, a, y)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [hPrel] with z hz
    simp only [Function.comp_apply, endpointObservationReal, hz.1, hz.2]
  change μ.map (fun p => (g p.1, a, (p.2 : ℝ))) =
    (Prel.restrict C).map endpointObservationReal
  rw [hleft, hright,
    endpointAssignedCell_realOutcome H g Prel hMass hOverlap a upper r]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointAssignedArmLaw_releaseReal {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    (endpointAssignedArmLaw H g Prel hMass hOverlap a upper).map
        (fun p => (g p.1, a, (p.2 : ℝ))) =
      (Prel.restrict {z | z.2.1 = a}).map endpointObservationReal := by
  let C : LabelSpace J → Set (Observation J) :=
    fun r => {z | z.1 = r ∧ z.2.1 = a}
  let A : Set (Observation J) := {z | z.2.1 = a}
  have hC : ∀ r, MeasurableSet (C r) := by
    intro r
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  have hdisj : Pairwise (fun r s => Disjoint (C r) (C s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro z hzr hzs
    exact hrs (hzr.1.symm.trans hzs.1)
  have hunion : (⋃ r, C r) = A := by
    ext z
    simp [C, A]
  have hpartition : Measure.sum (fun r => Prel.restrict (C r)) =
      Prel.restrict A := by
    rw [← Measure.restrict_iUnion hdisj hC, hunion]
  let f : ScoreSpace ε × OutcomeSpace → LabelSpace J × (ArmSpace × ℝ) :=
    fun p => (g p.1, a, (p.2 : ℝ))
  have hf : Measurable f := by
    have hg : Measurable g := hMass.2.2.1
    dsimp only [f]
    fun_prop
  unfold endpointAssignedArmLaw
  change (Measure.sum fun r : LabelSpace J =>
    if hq : 0 < armCellMass H g a r then
      ENNReal.ofReal (armCellMass H g a r) •
        boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
    else 0).map f = _
  rw [Measure.map_sum hf.aemeasurable]
  have hterms : (fun r : LabelSpace J =>
      (if hq : 0 < armCellMass H g a r then
        ENNReal.ofReal (armCellMass H g a r) •
          boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
       else 0).map f) =
      (fun r => (Prel.restrict (C r)).map endpointObservationReal) := by
    funext r
    exact endpointAssignedCell_releaseReal
      H g Prel hMass hOverlap a upper r
  rw [hterms]
  change Measure.sum (fun r => (Prel.restrict (C r)).map endpointObservationReal) =
    (Prel.restrict A).map endpointObservationReal
  rw [← hpartition,
    Measure.map_sum endpointObservationReal_measurable.aemeasurable]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_releaseReal {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    (endpointFullLaw H g Prel hMass hOverlap upper0 upper1).map
        (fun ω => endpointObservationReal (releasedRecord ω)) =
      Prel.map endpointObservationReal := by
  have hrel : Measurable
      (fun ω : FullRow ε J => endpointObservationReal (releasedRecord ω)) := by
    exact endpointObservationReal_measurable.comp (by
      unfold releasedRecord label arm observed
      fun_prop)
  unfold endpointFullLaw
  rw [Measure.map_add _ _ hrel,
    Measure.map_map hrel
      (reconstructedFullRow_measurable g hMass.2.2.1 false),
    Measure.map_map hrel
      (reconstructedFullRow_measurable g hMass.2.2.1 true)]
  change ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity false)).map
        (fun p => (g p.1, false, (p.2.1 : ℝ))) +
    ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity true)).map
        (fun p => (g p.1, true, (p.2.2 : ℝ))) = _
  have h0 := congrArg
    (Measure.map (fun q : ScoreSpace ε × OutcomeSpace =>
      (g q.1, false, (q.2 : ℝ))))
    (endpointAssignedPotentialLaw H g Prel hMass hOverlap upper0 upper1 false)
  have hg : Measurable g := hMass.2.2.1
  rw [Measure.map_map (by fun_prop)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; fun_prop)] at h0
  simp only [Bool.false_eq_true, ↓reduceIte] at h0
  change ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity false)).map
        (fun p => (g p.1, false, (p.2.1 : ℝ))) =
    (endpointAssignedArmLaw H g Prel hMass hOverlap false upper0).map
      (fun q => (g q.1, false, (q.2 : ℝ))) at h0
  have h1 := congrArg
    (Measure.map (fun q : ScoreSpace ε × OutcomeSpace =>
      (g q.1, true, (q.2 : ℝ))))
    (endpointAssignedPotentialLaw H g Prel hMass hOverlap upper0 upper1 true)
  rw [Measure.map_map (by fun_prop)
    (by simp only [↓reduceIte]; fun_prop)] at h1
  simp only [↓reduceIte] at h1
  change ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity true)).map
        (fun p => (g p.1, true, (p.2.2 : ℝ))) =
    (endpointAssignedArmLaw H g Prel hMass hOverlap true upper1).map
      (fun q => (g q.1, true, (q.2 : ℝ))) at h1
  rw [h0, h1,
    endpointAssignedArmLaw_releaseReal H g Prel hMass hOverlap false upper0,
    endpointAssignedArmLaw_releaseReal H g Prel hMass hOverlap true upper1,
    ← Measure.map_add _ _ endpointObservationReal_measurable]
  congr 1
  let S : Set (Observation J) := {z | z.2.1 = true}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hfalse : {z : Observation J | z.2.1 = false} = Sᶜ := by
    ext z
    simp [S]
  rw [hfalse, Measure.restrict_compl_add_restrict hS]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_releasedLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    ReleasedLaw (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) Prel := by
  have hcoe : MeasurableEmbedding
      (fun y : OutcomeSpace => (y : ℝ)) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hinner : MeasurableEmbedding
      (fun p : ArmSpace × OutcomeSpace => (p.1, (p.2 : ℝ))) := by
    change MeasurableEmbedding
      (Prod.map id (fun y : OutcomeSpace => (y : ℝ)))
    exact MeasurableEmbedding.id.prodMap hcoe
  have hemb : MeasurableEmbedding
      (endpointObservationReal (J := J)) := by
    change MeasurableEmbedding
      (Prod.map id (fun p : ArmSpace × OutcomeSpace => (p.1, (p.2 : ℝ))))
    exact MeasurableEmbedding.id.prodMap hinner
  unfold ReleasedLaw releasedLaw
  apply hemb.map_injective
  rw [Measure.map_map hemb.measurable (by
    unfold releasedRecord label arm observed
    fun_prop)]
  exact endpointFullLaw_releaseReal H g Prel hMass hOverlap upper0 upper1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_compatibleCausalLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    CompatibleCausalLaw H g Prel
      (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) := by
  exact
    { probability := endpointFullLaw_isProbabilityMeasure
        H g Prel hMass hOverlap upper0 upper1
      measurableRelease := hMass.2.2.1
      scoreMarginal := endpointFullLaw_scoreMarginal
        H g Prel hMass hOverlap upper0 upper1
      randomizedAssignment := endpointFullLaw_randomizedAssignment
        H g Prel hMass hOverlap upper0 upper1
      consistency := endpointFullLaw_consistency
        H g Prel hMass hOverlap upper0 upper1
      deterministicRelease := endpointFullLaw_deterministicRelease
        H g Prel hMass hOverlap upper0 upper1
      releasedLaw := endpointFullLaw_releasedLaw
        H g Prel hMass hOverlap upper0 upper1 }

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_potentialLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) (a : ArmSpace) :
    (endpointFullLaw H g Prel hMass hOverlap upper0 upper1).map
        (fun ω => (score ω, if a then outcome1 ω else outcome0 ω)) =
      endpointArmPotentialLaw H g Prel hMass hOverlap a
        (if a then upper1 else upper0) := by
  have hp : Measurable
      (fun ω : FullRow ε J =>
        (score ω, if a then outcome1 ω else outcome0 ω)) := by
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hs : Measurable (score (ε := ε) (J := J)) := by
        unfold score
        fun_prop
      have ho : Measurable (outcome0 (ε := ε) (J := J)) := by
        unfold outcome0
        fun_prop
      exact hs.prodMk ho
    · simp only [↓reduceIte]
      have hs : Measurable (score (ε := ε) (J := J)) := by
        unfold score
        fun_prop
      have ho : Measurable (outcome1 (ε := ε) (J := J)) := by
        unfold outcome1
        fun_prop
      exact hs.prodMk ho
  unfold endpointFullLaw
  rw [Measure.map_add _ _ hp,
    Measure.map_map hp
      (reconstructedFullRow_measurable g hMass.2.2.1 false),
    Measure.map_map hp
      (reconstructedFullRow_measurable g hMass.2.2.1 true)]
  change ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity false)).map
        (fun p => (p.1, if a then p.2.2 else p.2.1)) +
    ((endpointLatentLaw H g Prel hMass hOverlap upper0 upper1).withDensity
      (reconstructedAssignmentDensity true)).map
        (fun p => (p.1, if a then p.2.2 else p.2.1)) = _
  rw [← Measure.map_add _ _ (by
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop),
    endpointAssignmentMeasures_sum H g Prel hMass hOverlap upper0 upper1]
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact endpointLatentLaw_map_control
      H g Prel hMass hOverlap upper0 upper1
  · simp only [↓reduceIte]
    exact endpointLatentLaw_map_treated
      H g Prel hMass hOverlap upper0 upper1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma boundedEndpointCell_productIntegral {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (upper : Bool) :
    (∫ p, (p.2 : ℝ) * (armProb a p.1)⁻¹
        ∂boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper) =
      ∫ q, q.1 * q.2 ∂(if upper then
        Causalean.Stat.comonotoneCoupling
          (armCellOutcomeLaw Prel hMass.2.1 a r
            (by rw [hMass.2.2.2 a r]; exact hq))
          (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq)
       else
        Causalean.Stat.countermonotoneCoupling
          (armCellOutcomeLaw Prel hMass.2.1 a r
            (by rw [hMass.2.2.2 a r]; exact hq))
          (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq)) := by
  let M := endpointCellScoreOutcomeLaw H g Prel hMass hOverlap a r hq upper
  let b : ScoreSpace ε × ℝ → ScoreSpace ε × OutcomeSpace :=
    fun p => (p.1, clampOutcome p.2)
  let t : ScoreSpace ε × ℝ → ℝ × ℝ :=
    fun p => (p.2, (armProb a p.1)⁻¹)
  have hb : Measurable b := by
    dsimp only [b]
    exact measurable_fst.prodMk (clampOutcome_measurable.comp measurable_snd)
  have ht : Measurable t := by
    dsimp only [t]
    cases a <;> simp [armProb] <;> fun_prop
  have hboundedProduct : Measurable
      (fun p : ScoreSpace ε × OutcomeSpace =>
        (p.2 : ℝ) * (armProb a p.1)⁻¹) := by
    have hy : Measurable
        (fun p : ScoreSpace ε × OutcomeSpace => (p.2 : ℝ)) := by
      fun_prop
    have hw : Measurable (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
      cases a <;> simp [armProb] <;> fun_prop
    exact hy.mul (hw.comp measurable_fst)
  have hsupport : ∀ᵐ p ∂M, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact endpointCellScoreOutcomeLaw_outcome_support
      H g Prel hMass hOverlap a r hq upper
  unfold boundedEndpointCellLaw
  rw [integral_map hb.aemeasurable hboundedProduct.aestronglyMeasurable]
  calc
    (∫ p, ((clampOutcome p.2 : OutcomeSpace) : ℝ) *
        (armProb a p.1)⁻¹ ∂M) =
        ∫ p, p.2 * (armProb a p.1)⁻¹ ∂M := by
      apply integral_congr_ae
      filter_upwards [hsupport] with p hp
      rw [clampOutcome_coe_of_mem hp]
    _ = ∫ q, q.1 * q.2 ∂M.map t := by
      rw [integral_map ht.aemeasurable (by fun_prop)]
    _ = _ := by
      rw [endpointCellScoreOutcomeLaw_map_outcome_weight
        H g Prel hMass hOverlap a r hq upper]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointArmPotentialMean_eq_sum_cellProducts {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    (∫ p, (p.2 : ℝ) ∂endpointArmPotentialLaw
        H g Prel hMass hOverlap a upper) =
      ∑ r : LabelSpace J,
        if hq : 0 < armCellMass H g a r then
          armCellMass H g a r *
            ∫ q, q.1 * q.2 ∂(if upper then
              Causalean.Stat.comonotoneCoupling
                (armCellOutcomeLaw Prel hMass.2.1 a r
                  (by rw [hMass.2.2.2 a r]; exact hq))
                (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq)
             else
              Causalean.Stat.countermonotoneCoupling
                (armCellOutcomeLaw Prel hMass.2.1 a r
                  (by rw [hMass.2.2.2 a r]; exact hq))
                (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq))
        else 0 := by
  let F : ScoreSpace ε × OutcomeSpace → ℝ :=
    fun p => (p.2 : ℝ) * (armProb a p.1)⁻¹
  have hF : Measurable F := by
    dsimp only [F]
    have hy : Measurable
        (fun p : ScoreSpace ε × OutcomeSpace => (p.2 : ℝ)) := by fun_prop
    have hw : Measurable (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
      cases a <;> simp [armProb] <;> fun_prop
    exact hy.mul (hw.comp measurable_fst)
  have hcellInt : ∀ r : LabelSpace J, Integrable F
      (if hq : 0 < armCellMass H g a r then
        ENNReal.ofReal (armCellMass H g a r) •
          boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper
       else 0) := by
    intro r
    split
    · rename_i hq
      letI : IsFiniteMeasure
          (ENNReal.ofReal (armCellMass H g a r) •
            boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper) :=
        ⟨by
          rw [Measure.smul_apply]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (measure_lt_top _ _)⟩
      apply Integrable.of_bound hF.aestronglyMeasurable (|ε⁻¹| + 1)
      filter_upwards [] with p
      have hp : ε ≤ armProb a p.1 := by
        rcases p.1.property with ⟨hp0, hp1⟩
        cases a <;> simp [armProb] <;> linarith
      have hpa : 0 < armProb a p.1 := lt_of_lt_of_le hOverlap.1 hp
      have hw0 : 0 ≤ (armProb a p.1)⁻¹ := (inv_nonneg.mpr hpa.le)
      have hw1 : (armProb a p.1)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpa hOverlap.1).mpr hp
      have hy := p.2.property
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy.1 hw0)]
      calc
        (p.2 : ℝ) * (armProb a p.1)⁻¹ ≤
            1 * (armProb a p.1)⁻¹ :=
          mul_le_mul_of_nonneg_right hy.2 hw0
        _ = (armProb a p.1)⁻¹ := one_mul _
        _ ≤ ε⁻¹ := hw1
        _ ≤ |ε⁻¹| := le_abs_self _
        _ ≤ |ε⁻¹| + 1 := by linarith
    · simp [F]
  unfold endpointArmPotentialLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by cases a <;> simp [armProb] <;> fun_prop)
    (Filter.Eventually.of_forall fun p => by
      rw [ENNReal.inv_lt_top]
      apply ENNReal.ofReal_pos.mpr
      rcases p.1.property with ⟨hp0, hp1⟩
      cases a <;> simp [armProb] <;> linarith [hOverlap.1]) ]
  have hconvert : (∫ p,
      ((ENNReal.ofReal (armProb a p.1))⁻¹).toReal • (p.2 : ℝ)
        ∂endpointAssignedArmLaw H g Prel hMass hOverlap a upper) =
      ∫ p, F p ∂endpointAssignedArmLaw H g Prel hMass hOverlap a upper := by
    apply integral_congr_ae
    filter_upwards [] with p
    have hp : 0 < armProb a p.1 := by
      rcases p.1.property with ⟨hp0, hp1⟩
      cases a <;> simp [armProb] <;> linarith [hOverlap.1]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
    simp [F, mul_comm]
  rw [hconvert]
  unfold endpointAssignedArmLaw
  rw [Measure.sum_fintype,
    integral_finset_sum_measure (fun r _ => hcellInt r)]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : 0 < armCellMass H g a r
  · simp only [hq, dif_pos]
    rw [integral_smul_measure]
    rw [ENNReal.toReal_ofReal hq.le]
    change armCellMass H g a r *
      (∫ p, (p.2 : ℝ) * (armProb a p.1)⁻¹
        ∂boundedEndpointCellLaw H g Prel hMass hOverlap a r hq upper) = _
    rw [boundedEndpointCell_productIntegral
      H g Prel hMass hOverlap a r hq upper]
  · simp [hq]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointArmPotentialMean_lower {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) :
    (∫ p, (p.2 : ℝ) ∂endpointArmPotentialLaw
        H g Prel hMass hOverlap a false) =
      muLower H g Prel hMass a := by
  rw [endpointArmPotentialMean_eq_sum_cellProducts
    H g Prel hMass hOverlap a false]
  unfold muLower
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : 0 < armCellMass H g a r
  · simp only [hq, dif_pos, Bool.false_eq_true, ↓reduceIte]
    let Y := armCellOutcomeLaw Prel hMass.2.1 a r
      (by rw [hMass.2.2.2 a r]; exact hq)
    let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
    letI : IsProbabilityMeasure H := hMass.1
    letI : IsProbabilityMeasure Prel := hMass.2.1
    letI : IsProbabilityMeasure Y :=
      armCellOutcomeLaw_isProbabilityMeasure Prel a r
        (by rw [hMass.2.2.2 a r]; exact hq)
    letI : IsProbabilityMeasure
        (armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq) :=
      armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
    letI : IsProbabilityMeasure W := by
      dsimp [W, armCellWeightLaw]
      exact Measure.isProbabilityMeasure_map (by
        cases a <;> simp [armProb] <;> fun_prop)
    congr 1
    exact product_expectation_countermonotoneCoupling_interval Y W
  · simp [hq]

private lemma endpoint_memLp_id_of_support_Icc
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (b : ℝ) (h : μ (Icc 0 b)ᶜ = 0) : MemLp (fun x : ℝ => x) 2 μ := by
  apply memLp_of_bounded
  · rw [ae_iff]
    exact h
  · fun_prop

private lemma endpointArmCell_moments {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    MemLp (fun x : ℝ => x) 2
      (armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq)) ∧
    MemLp (fun x : ℝ => x) 2
      (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) := by
  let Y := armCellOutcomeLaw Prel hMass.2.1 a r
    (by rw [hMass.2.2.2 a r]; exact hq)
  let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : IsProbabilityMeasure Y :=
    armCellOutcomeLaw_isProbabilityMeasure Prel a r
      (by rw [hMass.2.2.2 a r]; exact hq)
  letI : IsProbabilityMeasure
      (armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq) :=
    armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
  letI : IsProbabilityMeasure W := by
    dsimp [W, armCellWeightLaw]
    exact Measure.isProbabilityMeasure_map (by
      cases a <;> simp [armProb] <;> fun_prop)
  have hYsup : Y (Icc 0 1)ᶜ = 0 := by
    dsimp [Y, armCellOutcomeLaw]
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    have hpre : (fun z : Observation J => (z.2.2 : ℝ)) ⁻¹' (Icc 0 1)ᶜ = ∅ := by
      ext z
      exact iff_false_intro (fun hz => hz z.2.2.property)
    rw [hpre]
    simp
  have hWsup : W (Icc 0 ε⁻¹)ᶜ = 0 := by
    dsimp [W, armCellWeightLaw]
    rw [Measure.map_apply (by
      cases a <;> simp [armProb] <;> fun_prop) measurableSet_Icc.compl]
    have hpre : (fun e : ScoreSpace ε => (armProb a e)⁻¹) ⁻¹'
        (Icc 0 ε⁻¹)ᶜ = ∅ := by
      ext e
      apply iff_false_intro
      intro he
      apply he
      have hp : ε ≤ armProb a e := by
        rcases e.property with ⟨he0, he1⟩
        cases a <;> simp [armProb] <;> linarith
      have hpa : 0 < armProb a e := lt_of_lt_of_le hOverlap.1 hp
      exact ⟨inv_nonneg.mpr hpa.le, (inv_le_inv₀ hpa hOverlap.1).mpr hp⟩
    rw [hpre]
    simp
  exact ⟨endpoint_memLp_id_of_support_Icc Y 1 hYsup,
    endpoint_memLp_id_of_support_Icc W ε⁻¹ hWsup⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointArmPotentialMean_upper {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) :
    (∫ p, (p.2 : ℝ) ∂endpointArmPotentialLaw
        H g Prel hMass hOverlap a true) =
      muUpper H g Prel hMass a := by
  rw [endpointArmPotentialMean_eq_sum_cellProducts
    H g Prel hMass hOverlap a true]
  unfold muUpper
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : 0 < armCellMass H g a r
  · simp only [hq, dif_pos, ↓reduceIte]
    let Y := armCellOutcomeLaw Prel hMass.2.1 a r
      (by rw [hMass.2.2.2 a r]; exact hq)
    let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
    letI : IsProbabilityMeasure H := hMass.1
    letI : IsProbabilityMeasure Prel := hMass.2.1
    letI : IsProbabilityMeasure Y :=
      armCellOutcomeLaw_isProbabilityMeasure Prel a r
        (by rw [hMass.2.2.2 a r]; exact hq)
    letI : IsProbabilityMeasure
        (armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq) :=
      armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
    letI : IsProbabilityMeasure W := by
      dsimp [W, armCellWeightLaw]
      exact Measure.isProbabilityMeasure_map (by
        cases a <;> simp [armProb] <;> fun_prop)
    have hm := endpointArmCell_moments H g Prel hMass hOverlap a r hq
    congr 1
    exact product_expectation_comonotoneCoupling_interval Y W hm.1 hm.2
  · simp [hq]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_armMean {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) (a : ArmSpace) :
    (∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ)
        ∂endpointFullLaw H g Prel hMass hOverlap upper0 upper1) =
      if (if a then upper1 else upper0) then muUpper H g Prel hMass a
      else muLower H g Prel hMass a := by
  have hmap := endpointFullLaw_potentialLaw
    H g Prel hMass hOverlap upper0 upper1 a
  have hint := congrArg
    (fun μ : Measure (ScoreSpace ε × OutcomeSpace) =>
      ∫ p, (p.2 : ℝ) ∂μ) hmap
  rw [integral_map (by
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ((by unfold score; fun_prop : Measurable
        (score (ε := ε) (J := J))).prodMk
          (by unfold outcome0; fun_prop)).aemeasurable
    · simp only [↓reduceIte]
      exact ((by unfold score; fun_prop : Measurable
        (score (ε := ε) (J := J))).prodMk
          (by unfold outcome1; fun_prop)).aemeasurable)
    (by fun_prop)] at hint
  change (∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ)
      ∂endpointFullLaw H g Prel hMass hOverlap upper0 upper1) =
    ∫ p, (p.2 : ℝ) ∂endpointArmPotentialLaw H g Prel hMass hOverlap a
      (if a then upper1 else upper0) at hint
  rw [hint]
  generalize hu : (if a then upper1 else upper0) = u
  cases u
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simpa [hu] using endpointArmPotentialMean_lower H g Prel hMass hOverlap a
  · simp only [↓reduceIte]
    simpa [hu] using endpointArmPotentialMean_upper H g Prel hMass hOverlap a

end
end CausalSmith.PartialID.UnlinkedPropensityAte
