module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompatibilityFullLawConstruction
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerTrialTesting

/-! Bernoulli sampling perturbations over an arbitrary fixed score law. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:a,p), [this definition](goal) introduces the corresponding object. -/
def samplingArmOutcomeLaw (a : ArmSpace) (p : ℝ) : Measure OutcomeSpace :=
  if a then trialOutcomeLaw p else Measure.dirac trialZeroOutcome

/-- For [the specified mathematical inputs](hyp:ε,H,p), [this definition](goal) introduces the corresponding object. -/
def directSamplingLatentLaw {ε : ℝ}
    (H : Measure (ScoreSpace ε)) (p : ℝ) :
    Measure (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :=
  H.prod ((Measure.dirac trialZeroOutcome).prod (trialOutcomeLaw p))

/-- For [the specified mathematical inputs](hyp:ε,K,H,g,p), [this definition](goal) introduces the corresponding object. -/
def directSamplingFullLaw {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace K)
    (p : ℝ) : Measure (FullRow ε K) :=
  ((directSamplingLatentLaw H p).withDensity
      (reconstructedAssignmentDensity false)).map (reconstructedFullRow g false) +
    ((directSamplingLatentLaw H p).withDensity
      (reconstructedAssignmentDensity true)).map (reconstructedFullRow g true)
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingLatentLaw_isProbabilityMeasure {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (directSamplingLatentLaw H p) := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  unfold directSamplingLatentLaw
  infer_instance

private lemma directSamplingAssignmentDensity_sum {ε : ℝ}
    (hOverlap : Overlap ε)
    (q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :
    reconstructedAssignmentDensity false q +
      reconstructedAssignmentDensity true q = 1 := by
  have he0 : 0 ≤ (q.1 : ℝ) := le_trans hOverlap.1.le q.1.property.1
  have he1 : (q.1 : ℝ) ≤ 1 := by linarith [q.1.property.2, hOverlap.1]
  unfold reconstructedAssignmentDensity armProb
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr he1) he0]
  norm_num
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,p,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingAssignmentMeasures_sum {ε : ℝ}
    (H : Measure (ScoreSpace ε)) (p : ℝ) (hOverlap : Overlap ε) :
    (directSamplingLatentLaw H p).withDensity
        (reconstructedAssignmentDensity false) +
      (directSamplingLatentLaw H p).withDensity
        (reconstructedAssignmentDensity true) =
      directSamplingLatentLaw H p := by
  rw [← withDensity_add_left (by
    change Measurable (fun q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      ENNReal.ofReal (1 - (q.1 : ℝ)))
    fun_prop)]
  have hfun : reconstructedAssignmentDensity false +
      reconstructedAssignmentDensity true =
      (1 : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) → ENNReal) := by
    funext q
    exact directSamplingAssignmentDensity_sum hOverlap q
  rw [hfun, withDensity_one]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_map_latentTriple {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace K)
    (hg : Measurable g) (hOverlap : Overlap ε) (p : ℝ) :
    (directSamplingFullLaw H g p).map latentTriple =
      directSamplingLatentLaw H p := by
  unfold directSamplingFullLaw
  rw [Measure.map_add _ _ (by unfold latentTriple score outcome0 outcome1; fun_prop),
    Measure.map_map (by unfold latentTriple score outcome0 outcome1; fun_prop)
      (reconstructedFullRow_measurable g hg false),
    Measure.map_map (by unfold latentTriple score outcome0 outcome1; fun_prop)
      (reconstructedFullRow_measurable g hg true)]
  have hfun (a : ArmSpace) :
      latentTriple ∘ reconstructedFullRow g a = id := by
    funext q
    cases a <;> rfl
  rw [hfun false, hfun true, Measure.map_id, Measure.map_id]
  change (directSamplingLatentLaw H p).withDensity
      (reconstructedAssignmentDensity false) +
    (directSamplingLatentLaw H p).withDensity
      (reconstructedAssignmentDensity true) = directSamplingLatentLaw H p
  exact directSamplingAssignmentMeasures_sum H p hOverlap
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_isProbabilityMeasure {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (directSamplingFullLaw H g p) := by
  let _ : IsProbabilityMeasure (directSamplingLatentLaw H p) :=
    directSamplingLatentLaw_isProbabilityMeasure H p hp0 hp1
  rw [isProbabilityMeasure_iff]
  unfold directSamplingFullLaw
  rw [Measure.add_apply,
    Measure.map_apply (reconstructedFullRow_measurable g hg false) MeasurableSet.univ,
    Measure.map_apply (reconstructedFullRow_measurable g hg true) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [← Measure.add_apply, directSamplingAssignmentMeasures_sum H p hOverlap]
  exact isProbabilityMeasure_iff.mp inferInstance
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_scoreMarginal {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ScoreMarginal (directSamplingFullLaw H g p) H := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  unfold ScoreMarginal directSamplingFullLaw
  rw [Measure.map_add _ _ (by unfold score; fun_prop),
    Measure.map_map (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg false),
    Measure.map_map (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg true)]
  have hfun (a : ArmSpace) :
      score ∘ reconstructedFullRow g a = Prod.fst := by
    funext q
    rfl
  rw [hfun false, hfun true, ← Measure.map_add _ _ measurable_fst,
    directSamplingAssignmentMeasures_sum H p hOverlap]
  unfold directSamplingLatentLaw
  rw [Measure.map_fst_prod]
  simp
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,p), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_consistency {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace K)
    (hg : Measurable g) (p : ℝ) :
    Consistency (directSamplingFullLaw H g p) := by
  unfold Consistency directSamplingFullLaw
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff (reconstructedFullRow_measurable g hg false).aemeasurable (by
      exact measurableSet_eq_fun (by unfold observed; fun_prop)
        (by
          have hcond : MeasurableSet {ω : FullRow ε K | arm ω = true} :=
            measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
          exact Measurable.ite hcond (by unfold outcome1; fun_prop)
            (by unfold outcome0; fun_prop)))]
    filter_upwards [] with q
    rfl
  · rw [ae_map_iff (reconstructedFullRow_measurable g hg true).aemeasurable (by
      exact measurableSet_eq_fun (by unfold observed; fun_prop)
        (by
          have hcond : MeasurableSet {ω : FullRow ε K | arm ω = true} :=
            measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
          exact Measurable.ite hcond (by unfold outcome1; fun_prop)
            (by unfold outcome0; fun_prop)))]
    filter_upwards [] with q
    rfl
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,p), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_deterministicRelease {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace K)
    (hg : Measurable g) (p : ℝ) :
    DeterministicRelease g (directSamplingFullLaw H g p) := by
  unfold DeterministicRelease directSamplingFullLaw
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff (reconstructedFullRow_measurable g hg false).aemeasurable (by
      exact measurableSet_eq_fun (by unfold label; fun_prop)
        (hg.comp (by unfold score; fun_prop)))]
    filter_upwards [] with q
    rfl
  · rw [ae_map_iff (reconstructedFullRow_measurable g hg true).aemeasurable (by
      exact measurableSet_eq_fun (by unfold label; fun_prop)
        (hg.comp (by unfold score; fun_prop)))]
    filter_upwards [] with q
    rfl

private lemma directSamplingLatentScore_integrable {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable (fun q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      (q.1 : ℝ)) (directSamplingLatentLaw H p) := by
  let _ : IsProbabilityMeasure (directSamplingLatentLaw H p) :=
    directSamplingLatentLaw_isProbabilityMeasure H p hp0 hp1
  apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with q
  rw [Real.norm_eq_abs]
  rcases q.1.property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma directSamplingAssignmentTrue_real {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Set (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)))
    (hD : MeasurableSet D) :
    ((directSamplingLatentLaw H p).withDensity
      (reconstructedAssignmentDensity true)).real D =
      ∫ q in D, (q.1 : ℝ) ∂directSamplingLatentLaw H p := by
  have hint : IntegrableOn
      (fun q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) => (q.1 : ℝ)) D
      (directSamplingLatentLaw H p) :=
    (directSamplingLatentScore_integrable H p hp0 hp1).integrableOn
  unfold Measure.real reconstructedAssignmentDensity armProb
  rw [withDensity_apply _ hD]
  simp only [ite_true]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun q =>
      le_trans hOverlap.1.le q.1.property.1)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun q =>
    le_trans hOverlap.1.le q.1.property.1)]

private lemma directSamplingComponent_finite {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ArmSpace) : IsFiniteMeasure
      ((directSamplingLatentLaw H p).withDensity
        (reconstructedAssignmentDensity a)) := by
  let _ : IsProbabilityMeasure (directSamplingLatentLaw H p) :=
    directSamplingLatentLaw_isProbabilityMeasure H p hp0 hp1
  let f : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) → ℝ :=
    fun q => armProb a q.1
  have hf : Integrable f (directSamplingLatentLaw H p) := by
    apply Integrable.of_bound (by
      dsimp [f]
      cases a <;> simp [armProb] <;> fun_prop) 1
    filter_upwards [] with q
    have he0 : 0 ≤ (q.1 : ℝ) := le_trans hOverlap.1.le q.1.property.1
    have he1 : (q.1 : ℝ) ≤ 1 := by linarith [q.1.property.2, hOverlap.1]
    cases a
    · change |1 - (q.1 : ℝ)| ≤ 1
      rw [abs_of_nonneg (by linarith)]
      linarith
    · change |(q.1 : ℝ)| ≤ 1
      rw [abs_of_nonneg he0]
      exact he1
  change IsFiniteMeasure
    ((directSamplingLatentLaw H p).withDensity
      (fun q => ENNReal.ofReal (f q)))
  exact isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral

private lemma samplingFullScore_integrable_finite {ε : ℝ} {K : ℕ}
    (P : Measure (FullRow ε K)) [IsFiniteMeasure P] :
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

private lemma samplingLatentScore_integrable_finite {ε : ℝ}
    (μ : Measure (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)))
    [IsFiniteMeasure μ] :
    Integrable (fun q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      (q.1 : ℝ)) μ := by
  apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with q
  rw [Real.norm_eq_abs]
  rcases q.1.property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_randomizedAssignment {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    RandomizedAssignment (directSamplingFullLaw H g p) := by
  intro B hB
  let L := directSamplingLatentLaw H p
  let M₀ := L.withDensity (reconstructedAssignmentDensity false)
  let M₁ := L.withDensity (reconstructedAssignmentDensity true)
  let D : Set (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :=
    {q | (q.1, q.2.1, q.2.2) ∈ B}
  have hD : MeasurableSet D := hB.preimage (by fun_prop)
  let S : Set (FullRow ε K) :=
    {ω | arm ω = true ∧ (score ω, outcome0 ω, outcome1 ω) ∈ B}
  let T : Set (FullRow ε K) :=
    {ω | (score ω, outcome0 ω, outcome1 ω) ∈ B}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const).inter
      (hB.preimage (by unfold score outcome0 outcome1; fun_prop))
  have hT : MeasurableSet T :=
    hB.preimage (by unfold score outcome0 outcome1; fun_prop)
  have hpre0S : reconstructedFullRow g false ⁻¹' S = ∅ := by
    ext q
    simp [S, reconstructedFullRow, arm]
  have hpre1S : reconstructedFullRow g true ⁻¹' S = D := by
    ext q
    simp [S, D, reconstructedFullRow, arm, score, outcome0, outcome1]
  have hpre0T : reconstructedFullRow g false ⁻¹' T = D := by
    ext q
    simp [T, D, reconstructedFullRow, score, outcome0, outcome1]
  have hpre1T : reconstructedFullRow g true ⁻¹' T = D := by
    ext q
    simp [T, D, reconstructedFullRow, score, outcome0, outcome1]
  let _ : IsFiniteMeasure M₀ :=
    directSamplingComponent_finite H hOverlap p hp0 hp1 false
  let _ : IsFiniteMeasure M₁ :=
    directSamplingComponent_finite H hOverlap p hp0 hp1 true
  have hmap0 : IsFiniteMeasure (M₀.map (reconstructedFullRow g false)) := ⟨by
    rw [Measure.map_apply (reconstructedFullRow_measurable g hg false)
      MeasurableSet.univ]
    exact measure_lt_top M₀ Set.univ
  ⟩
  have hmap1 : IsFiniteMeasure (M₁.map (reconstructedFullRow g true)) := ⟨by
    rw [Measure.map_apply (reconstructedFullRow_measurable g hg true)
      MeasurableSet.univ]
    exact measure_lt_top M₁ Set.univ
  ⟩
  change (directSamplingFullLaw H g p).real S =
    ∫ ω in T, (score ω : ℝ) ∂directSamplingFullLaw H g p
  have hleft : (directSamplingFullLaw H g p).real S =
      ∫ q in D, (q.1 : ℝ) ∂L := by
    unfold directSamplingFullLaw
    rw [Measure.real_def, Measure.add_apply,
      Measure.map_apply (reconstructedFullRow_measurable g hg false) hS,
      Measure.map_apply (reconstructedFullRow_measurable g hg true) hS,
      hpre0S, hpre1S, measure_empty, zero_add]
    change M₁.real D = _
    exact directSamplingAssignmentTrue_real H hOverlap p hp0 hp1 D hD
  rw [hleft]
  unfold directSamplingFullLaw
  let _ : IsFiniteMeasure (M₀.map (reconstructedFullRow g false)) := hmap0
  let _ : IsFiniteMeasure (M₁.map (reconstructedFullRow g true)) := hmap1
  rw [Measure.restrict_add,
    integral_add_measure (samplingFullScore_integrable_finite _).integrableOn
      (samplingFullScore_integrable_finite _).integrableOn,
    setIntegral_map hT (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg false).aemeasurable,
    setIntegral_map hT (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg true).aemeasurable,
    hpre0T, hpre1T]
  change (∫ q in D, (q.1 : ℝ) ∂L) =
    (∫ q in D, (q.1 : ℝ) ∂M₀) + (∫ q in D, (q.1 : ℝ) ∂M₁)
  rw [← integral_add_measure
    (samplingLatentScore_integrable_finite M₀).integrableOn
    (samplingLatentScore_integrable_finite M₁).integrableOn]
  rw [← Measure.restrict_add, directSamplingAssignmentMeasures_sum H p hOverlap]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_ate {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ate (directSamplingFullLaw H g p) = p := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  let _ : IsProbabilityMeasure (directSamplingLatentLaw H p) :=
    directSamplingLatentLaw_isProbabilityMeasure H p hp0 hp1
  let _ : IsProbabilityMeasure (directSamplingFullLaw H g p) :=
    directSamplingFullLaw_isProbabilityMeasure H g hg hOverlap p hp0 hp1
  have hlatentInt : Integrable
      (fun q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
        (q.2.2 : ℝ) - (q.2.1 : ℝ)) (directSamplingLatentLaw H p) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with q
    rw [Real.norm_eq_abs]
    have h0 := q.2.1.property
    have h1 := q.2.2.property
    change 0 ≤ (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 1 at h0
    change 0 ≤ (q.2.2 : ℝ) ∧ (q.2.2 : ℝ) ≤ 1 at h1
    exact abs_le.mpr ⟨by
      linarith [h0.1, h1.2], by linarith [h0.2, h1.1]⟩
  have houtInt : Integrable
      (fun q : OutcomeSpace × OutcomeSpace => (q.2 : ℝ) - (q.1 : ℝ))
      ((Measure.dirac trialZeroOutcome).prod (trialOutcomeLaw p)) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with q
    rw [Real.norm_eq_abs]
    have h0 := q.1.property
    have h1 := q.2.property
    change 0 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 1 at h0
    change 0 ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ 1 at h1
    exact abs_le.mpr ⟨by
      linarith [h0.1, h1.2], by linarith [h0.2, h1.1]⟩
  have hlatentMeas : Measurable (latentTriple (ε := ε) (J := K)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  calc
    ate (directSamplingFullLaw H g p) =
        ∫ q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace),
          ((q.2.2 : ℝ) - (q.2.1 : ℝ))
          ∂directSamplingLatentLaw H p := by
      unfold ate
      rw [← directSamplingFullLaw_map_latentTriple H g hg hOverlap p]
      rw [integral_map hlatentMeas.aemeasurable (by fun_prop)]
      rfl
    _ = ∫ e : ScoreSpace ε,
          (∫ q : OutcomeSpace × OutcomeSpace,
            ((q.2 : ℝ) - (q.1 : ℝ))
            ∂((Measure.dirac trialZeroOutcome).prod (trialOutcomeLaw p))) ∂H := by
      unfold directSamplingLatentLaw
      exact integral_prod _ hlatentInt
    _ = ∫ q : OutcomeSpace × OutcomeSpace,
          ((q.2 : ℝ) - (q.1 : ℝ))
          ∂((Measure.dirac trialZeroOutcome).prod (trialOutcomeLaw p)) := by
      simp [probReal_univ]
    _ = ∫ y : OutcomeSpace, (y : ℝ) ∂(trialOutcomeLaw p) := by
      rw [integral_prod _ houtInt]
      simp [trialZeroOutcome]
    _ = p := trialOutcomeLaw_mean p hp0 hp1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_mem_causalLaws {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    directSamplingFullLaw H g p ∈ CausalLaws H g := by
  have hprob := directSamplingFullLaw_isProbabilityMeasure
    H g hg hOverlap p hp0 hp1
  refine ⟨hprob, ?_⟩
  exact
    { probability := hprob
      measurableRelease := hg
      scoreMarginal := directSamplingFullLaw_scoreMarginal
        H g hg hOverlap p hp0 hp1
      randomizedAssignment := directSamplingFullLaw_randomizedAssignment
        H g hg hOverlap p hp0 hp1
      consistency := directSamplingFullLaw_consistency H g hg p
      deterministicRelease := directSamplingFullLaw_deterministicRelease H g hg p }

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,p,hp0,hp1,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingLatentLaw_withDensity {ε : ℝ}
    (H : Measure (ScoreSpace ε)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ArmSpace) :
    (directSamplingLatentLaw H p).withDensity
        (reconstructedAssignmentDensity a) =
      (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).prod
        ((Measure.dirac trialZeroOutcome).prod (trialOutcomeLaw p)) := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  unfold directSamplingLatentLaw reconstructedAssignmentDensity
  symm
  apply prod_withDensity_left
  cases a <;> simp only [armProb, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,p,hp0,hp1,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingReleasedComponent {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : ArmSpace) :
    (((directSamplingLatentLaw H p).withDensity
        (reconstructedAssignmentDensity a)).map
          (reconstructedFullRow g a)).map releasedRecord =
      ((H.withDensity (fun e => ENNReal.ofReal (armProb a e))).prod
        (samplingArmOutcomeLaw a p)).map
          (fun q => (g q.1, a, q.2)) := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  rw [Measure.map_map (by unfold releasedRecord label arm observed; fun_prop)
    (reconstructedFullRow_measurable g hg a)]
  rw [directSamplingLatentLaw_withDensity H p hp0 hp1 a]
  let μ := H.withDensity (fun e => ENNReal.ofReal (armProb a e))
  let ν := (Measure.dirac trialZeroOutcome).prod (trialOutcomeLaw p)
  let s : OutcomeSpace × OutcomeSpace → OutcomeSpace :=
    fun q => if a then q.2 else q.1
  have hs : Measurable s := by
    cases a <;> simp [s] <;> fun_prop
  have hselect : ν.map s = samplingArmOutcomeLaw a p := by
    cases a
    · simp only [s, Bool.false_eq_true, ↓reduceIte, samplingArmOutcomeLaw]
      rw [Measure.map_fst_prod]
      simp
    · simp only [s, ↓reduceIte, samplingArmOutcomeLaw]
      rw [Measure.map_snd_prod]
      simp
  rw [← hselect]
  have hprod : μ.prod (ν.map s) =
      (μ.prod ν).map (Prod.map id s) := by
    calc
      μ.prod (ν.map s) = (μ.map id).prod (ν.map s) := by rw [Measure.map_id]
      _ = (μ.prod ν).map (Prod.map id s) :=
        Measure.map_prod_map μ ν measurable_id hs
  rw [hprod, Measure.map_map (by fun_prop) (measurable_id.prodMap hs)]
  congr 1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_releasedComponents {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    releasedLaw (directSamplingFullLaw H g p) =
      ((H.withDensity (fun e => ENNReal.ofReal (armProb false e))).prod
        (samplingArmOutcomeLaw false p)).map
          (fun q => (g q.1, false, q.2)) +
      ((H.withDensity (fun e => ENNReal.ofReal (armProb true e))).prod
        (samplingArmOutcomeLaw true p)).map
          (fun q => (g q.1, true, q.2)) := by
  unfold releasedLaw directSamplingFullLaw
  rw [Measure.map_add _ _ (by unfold releasedRecord label arm observed; fun_prop)]
  rw [directSamplingReleasedComponent H g hg p hp0 hp1 false,
    directSamplingReleasedComponent H g hg p hp0 hp1 true]

/-- For [the specified mathematical inputs](hyp:ε,K,H,g), [this definition](goal) introduces the corresponding object. -/
def samplingDesignLaw {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace K) :
    Measure (LabelSpace K × ArmSpace) :=
  randomizedKeyLaw H g

/-- For [the specified mathematical inputs](hyp:K), [this definition](goal) introduces the corresponding object. -/
def samplingReadout {K : ℕ} :
    OutcomeSpace × (LabelSpace K × ArmSpace) → Observation K :=
  fun z => (z.2.1, z.2.2, if z.2.2 then z.1 else trialZeroOutcome)
/-- Given [the stated mathematical inputs and assumptions](hyp:K), this result [establishes the stated mathematical conclusion](goal). -/
lemma samplingReadout_measurable {K : ℕ} :
    Measurable (samplingReadout (K := K)) := by
  unfold samplingReadout
  have hcond : MeasurableSet
      {z : OutcomeSpace × (LabelSpace K × ArmSpace) | z.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hobs : Measurable
      (fun z : OutcomeSpace × (LabelSpace K × ArmSpace) =>
        if z.2.2 then z.1 else trialZeroOutcome) :=
    Measurable.ite hcond measurable_fst measurable_const
  fun_prop (disch := assumption)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma samplingDesignLaw_isProbabilityMeasure {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) :
    IsProbabilityMeasure (samplingDesignLaw H g) := by
  have hmeas (a : ArmSpace) : Measurable
      (fun e : ScoreSpace ε => ENNReal.ofReal (armProb a e)) := by
    cases a
    · change Measurable (fun e : ScoreSpace ε => ENNReal.ofReal (1 - (e : ℝ)))
      fun_prop
    · change Measurable (fun e : ScoreSpace ε => ENNReal.ofReal (e : ℝ))
      fun_prop
  have hsum :
      H.withDensity (fun e => ENNReal.ofReal (armProb false e)) +
        H.withDensity (fun e => ENNReal.ofReal (armProb true e)) = H := by
    rw [← withDensity_add_left (hmeas false)]
    have hfun :
        (fun e : ScoreSpace ε => ENNReal.ofReal (armProb false e)) +
          (fun e => ENNReal.ofReal (armProb true e)) = 1 := by
      funext e
      exact directSamplingAssignmentDensity_sum hOverlap
        (e, (trialZeroOutcome, trialZeroOutcome))
    rw [hfun, withDensity_one]
  apply isProbabilityMeasure_iff.mpr
  unfold samplingDesignLaw randomizedKeyLaw scoreAssignedKeyLaw
  rw [Measure.add_apply,
    Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [← Measure.add_apply, hsum]
  exact isProbabilityMeasure_iff.mp inferInstance

private lemma directSamplingReleasedComponent_design {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : ArmSpace) :
    ((H.withDensity (fun e => ENNReal.ofReal (armProb a e))).prod
        (samplingArmOutcomeLaw a p)).map
          (fun q => (g q.1, a, q.2)) =
      ((trialOutcomeLaw p).prod (scoreAssignedKeyLaw H g a)).map
        samplingReadout := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  let μ := H.withDensity (fun e => ENNReal.ofReal (armProb a e))
  have hkey : Measurable (fun e : ScoreSpace ε => (g e, a)) := by fun_prop
  cases a
  · change (μ.prod (Measure.dirac trialZeroOutcome)).map
        (fun q => (g q.1, false, q.2)) =
      ((trialOutcomeLaw p).prod (μ.map (fun e => (g e, false)))).map
        samplingReadout
    rw [Measure.prod_dirac]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hright :
        ((trialOutcomeLaw p).prod (μ.map (fun e => (g e, false)))).map
            samplingReadout =
          (μ.map (fun e => (g e, false))).map
            (fun k => (k.1, false, trialZeroOutcome)) := by
      have hprod :
          (trialOutcomeLaw p).prod (μ.map (fun e => (g e, false))) =
            ((trialOutcomeLaw p).prod μ).map
              (Prod.map id (fun e => (g e, false))) := by
        calc
          (trialOutcomeLaw p).prod (μ.map (fun e => (g e, false))) =
              ((trialOutcomeLaw p).map id).prod
                (μ.map (fun e => (g e, false))) := by rw [Measure.map_id]
          _ = ((trialOutcomeLaw p).prod μ).map
                (Prod.map id (fun e => (g e, false))) :=
            Measure.map_prod_map (trialOutcomeLaw p) μ measurable_id hkey
      rw [hprod, Measure.map_map samplingReadout_measurable
        (measurable_id.prodMap hkey)]
      change ((trialOutcomeLaw p).prod μ).map
          ((fun e : ScoreSpace ε => (g e, false, trialZeroOutcome)) ∘ Prod.snd) = _
      rw [← Measure.map_map (by fun_prop) measurable_snd]
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      rw [Measure.map_map (by fun_prop) hkey]
      congr 1
    rw [hright]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · change (μ.prod (trialOutcomeLaw p)).map
        (fun q => (g q.1, true, q.2)) =
      ((trialOutcomeLaw p).prod (μ.map (fun e => (g e, true)))).map
        samplingReadout
    have hprod :
        (trialOutcomeLaw p).prod (μ.map (fun e => (g e, true))) =
          ((trialOutcomeLaw p).prod μ).map
            (Prod.map id (fun e => (g e, true))) := by
      calc
        (trialOutcomeLaw p).prod (μ.map (fun e => (g e, true))) =
            ((trialOutcomeLaw p).map id).prod
              (μ.map (fun e => (g e, true))) := by rw [Measure.map_id]
        _ = ((trialOutcomeLaw p).prod μ).map
              (Prod.map id (fun e => (g e, true))) :=
          Measure.map_prod_map (trialOutcomeLaw p) μ measurable_id hkey
    rw [hprod]
    rw [Measure.map_map samplingReadout_measurable
      (measurable_id.prodMap hkey)]
    rw [← Measure.prod_swap]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSamplingFullLaw_releasedLaw {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    releasedLaw (directSamplingFullLaw H g p) =
      ((trialOutcomeLaw p).prod (samplingDesignLaw H g)).map
        samplingReadout := by
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  rw [directSamplingFullLaw_releasedComponents H g hg p hp0 hp1]
  unfold samplingDesignLaw randomizedKeyLaw
  rw [Measure.prod_add, Measure.map_add _ _ samplingReadout_measurable]
  rw [← directSamplingReleasedComponent_design H g hg p hp0 hp1 false,
    ← directSamplingReleasedComponent_design H g hg p hp0 hp1 true]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
