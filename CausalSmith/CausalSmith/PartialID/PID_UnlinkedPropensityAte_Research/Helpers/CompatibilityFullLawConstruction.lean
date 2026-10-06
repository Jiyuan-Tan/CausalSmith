module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompatibilityReconstruction

/-! Full-law reconstruction from compatible released arm-cell masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hg,a), [this definition](goal) introduces the corresponding object. -/
def reconstructedArmPotentialLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel]
    (hg : Measurable g) (a : ArmSpace) :
    Measure (ScoreSpace ε × OutcomeSpace) :=
  H ⊗ₘ Kernel.comap (releasedPairLaw Prel).condKernel
    (fun e => (g e, a)) (hg.prodMk measurable_const)
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hg,a), [this definition](goal) introduces the corresponding object. -/
instance reconstructedArmPotentialLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hg : Measurable g) (a : ArmSpace)
    [IsProbabilityMeasure H] [IsProbabilityMeasure Prel] :
    IsProbabilityMeasure (reconstructedArmPotentialLaw H g Prel hg a) := by
  unfold reconstructedArmPotentialLaw
  infer_instance

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedArmPotentialLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hg : Measurable g) (a : ArmSpace)
    [IsProbabilityMeasure H] [IsProbabilityMeasure Prel] :
    (reconstructedArmPotentialLaw H g Prel hg a).fst = H := by
  unfold reconstructedArmPotentialLaw
  exact Measure.fst_compProd H _

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hg), [this definition](goal) introduces the corresponding object. -/
def reconstructedLatentLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) :
    Measure (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :=
  glueAlongFst (reconstructedArmPotentialLaw H g Prel hg false)
    (reconstructedArmPotentialLaw H g Prel hg true)
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hg), [this definition](goal) introduces the corresponding object. -/
instance reconstructedLatentLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hg : Measurable g)
    [IsProbabilityMeasure H] [IsProbabilityMeasure Prel] :
    IsProbabilityMeasure (reconstructedLatentLaw H g Prel hg) := by
  unfold reconstructedLatentLaw
  exact glueAlongFst_isProbabilityMeasure _ _

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedLatentLaw_map_control {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hg : Measurable g)
    [IsProbabilityMeasure H] [IsProbabilityMeasure Prel] :
    (reconstructedLatentLaw H g Prel hg).map (fun p => (p.1, p.2.1)) =
      reconstructedArmPotentialLaw H g Prel hg false := by
  unfold reconstructedLatentLaw
  exact glueAlongFst_map_left _ _

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedLatentLaw_map_treated {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hg : Measurable g)
    [IsProbabilityMeasure H] [IsProbabilityMeasure Prel] :
    (reconstructedLatentLaw H g Prel hg).map (fun p => (p.1, p.2.2)) =
      reconstructedArmPotentialLaw H g Prel hg true := by
  unfold reconstructedLatentLaw
  apply glueAlongFst_map_right
  rw [reconstructedArmPotentialLaw_fst, reconstructedArmPotentialLaw_fst]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedLatentLaw_fst {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hg : Measurable g)
    [IsProbabilityMeasure H] [IsProbabilityMeasure Prel] :
    (reconstructedLatentLaw H g Prel hg).fst = H := by
  unfold Measure.fst
  calc
    (reconstructedLatentLaw H g Prel hg).map Prod.fst =
        ((reconstructedLatentLaw H g Prel hg).map
          (fun p => (p.1, p.2.1))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    _ = (reconstructedArmPotentialLaw H g Prel hg false).map Prod.fst := by
      rw [reconstructedLatentLaw_map_control]
    _ = H := reconstructedArmPotentialLaw_fst H g Prel hg false

/-- For [the specified mathematical inputs](hyp:ε,a,p), [this definition](goal) introduces the corresponding object. -/
def reconstructedAssignmentDensity {ε : ℝ}
    (a : ArmSpace) (p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) : ENNReal :=
  ENNReal.ofReal (armProb a p.1)

/-- For [the specified mathematical inputs](hyp:ε,J,g,a,p), [this definition](goal) introduces the corresponding object. -/
def reconstructedFullRow {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (a : ArmSpace)
    (p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) : FullRow ε J :=
  (p.1, p.2.1, p.2.2, a, if a then p.2.2 else p.2.1, g p.1)
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hg,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullRow_measurable {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g) (a : ArmSpace) :
    Measurable (reconstructedFullRow g a) := by
  unfold reconstructedFullRow
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    fun_prop
  · simp only [↓reduceIte]
    fun_prop

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,Prel,hg), [this definition](goal) introduces the corresponding object. -/
def reconstructedFullLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) : Measure (FullRow ε J) :=
  ((reconstructedLatentLaw H g Prel hg).withDensity
      (reconstructedAssignmentDensity false)).map (reconstructedFullRow g false) +
    ((reconstructedLatentLaw H g Prel hg).withDensity
      (reconstructedAssignmentDensity true)).map (reconstructedFullRow g true)

private lemma reconstructedAssignmentDensity_measurable {ε : ℝ}
    (a : ArmSpace) : Measurable
      (reconstructedAssignmentDensity (ε := ε) a) := by
  cases a
  · change Measurable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      ENNReal.ofReal (1 - (p.1 : ℝ)))
    fun_prop
  · change Measurable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      ENNReal.ofReal (p.1 : ℝ))
    fun_prop

private lemma map_withDensity_of_comp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (m : α → β) (hm : Measurable m)
    (f : β → ENNReal) (hf : Measurable f) :
    (μ.withDensity (f ∘ m)).map m = (μ.map m).withDensity f := by
  ext B hB
  rw [Measure.map_apply hm hB,
    withDensity_apply _ (hB.preimage hm), withDensity_apply _ hB,
    setLIntegral_map hB hf hm]
  rfl

private lemma withDensity_fst_compProd {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : Kernel α β) [SFinite μ] [IsSFiniteKernel κ]
    (f : α → ENNReal) (hf : Measurable f) :
    (μ ⊗ₘ κ).withDensity (fun p => f p.1) =
      (μ.withDensity f) ⊗ₘ κ := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hf
      (Kernel.measurable_kernel_prodMk_left hs)]
  rw [← lintegral_indicator hs, Measure.lintegral_compProd]
  · apply lintegral_congr
    intro a
    change (∫⁻ b, s.indicator (fun x => f x.1) (a, b) ∂κ a) =
      f a * (κ a) (Prod.mk a ⁻¹' s)
    calc
      _ = ∫⁻ b, (Prod.mk a ⁻¹' s).indicator (fun _ => f a) b ∂κ a := by
        apply lintegral_congr
        intro b
        rfl
      _ = _ := by
        rw [lintegral_indicator (measurable_prodMk_left hs), setLIntegral_const]
  · exact (hf.comp measurable_fst).indicator hs

private lemma map_compProd_comap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (κ : Kernel β γ) [SFinite μ] [IsSFiniteKernel κ]
    (f : α → β) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (fun p => (f p.1, p.2)) =
      (μ.map f) ⊗ₘ κ := by
  have hpair : Measurable (fun p : α × γ => (f p.1, p.2)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hpair hs,
    Measure.compProd_apply (hs.preimage hpair),
    Measure.compProd_apply hs]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedAssignedPotentialLaw { ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (a : ArmSpace) :
    ((reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity a)).map
        (fun p => (p.1, if a then p.2.2 else p.2.1)) =
      (reconstructedArmPotentialLaw H g Prel hg a).withDensity
        (fun p => ENNReal.ofReal (armProb a p.1)) := by
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    change ((reconstructedLatentLaw H g Prel hg).withDensity
        ((fun q : ScoreSpace ε × OutcomeSpace =>
          ENNReal.ofReal (1 - (q.1 : ℝ))) ∘
          (fun p => (p.1, p.2.1)))).map (fun p => (p.1, p.2.1)) = _
    rw [map_withDensity_of_comp _ _ (by fun_prop) _ (by fun_prop),
      reconstructedLatentLaw_map_control H g Prel hg]
    rfl
  · simp only [↓reduceIte]
    change ((reconstructedLatentLaw H g Prel hg).withDensity
        ((fun q : ScoreSpace ε × OutcomeSpace =>
          ENNReal.ofReal (q.1 : ℝ)) ∘
          (fun p => (p.1, p.2.2)))).map (fun p => (p.1, p.2.2)) = _
    rw [map_withDensity_of_comp _ _ (by fun_prop) _ (by fun_prop),
      reconstructedLatentLaw_map_treated H g Prel hg]
    rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedAssignedReleasedPairLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (a : ArmSpace) :
    ((reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity a)).map
        (fun p => ((g p.1, a), if a then p.2.2 else p.2.1)) =
      scoreAssignedKeyLaw H g a ⊗ₘ (releasedPairLaw Prel).condKernel := by
  let k : ScoreSpace ε → LabelSpace J × ArmSpace := fun e => (g e, a)
  let d : ScoreSpace ε → ENNReal :=
    fun e => ENNReal.ofReal (armProb a e)
  let q : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) →
      ScoreSpace ε × OutcomeSpace :=
    fun p => (p.1, if a then p.2.2 else p.2.1)
  let v : ScoreSpace ε × OutcomeSpace →
      (LabelSpace J × ArmSpace) × OutcomeSpace :=
    fun p => (k p.1, p.2)
  have hk : Measurable k := hg.prodMk measurable_const
  have hq : Measurable q := by
    cases a <;> simp [q] <;> fun_prop
  have hv : Measurable v := by
    dsimp [v]
    exact (hk.comp measurable_fst).prodMk measurable_snd
  have hd : Measurable d := by
    cases a <;> simp [d, armProb] <;> fun_prop
  calc
    ((reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity a)).map
        (fun p => ((g p.1, a), if a then p.2.2 else p.2.1)) =
        (((reconstructedLatentLaw H g Prel hg).withDensity
          (reconstructedAssignmentDensity a)).map q).map v := by
          rw [Measure.map_map hv hq]
          rfl
    _ = ((reconstructedArmPotentialLaw H g Prel hg a).withDensity
        (fun p => d p.1)).map v := by
      rw [reconstructedAssignedPotentialLaw H g Prel hg a]
    _ = (((H.withDensity d) ⊗ₘ
        Kernel.comap (releasedPairLaw Prel).condKernel k hk).map v) := by
      unfold reconstructedArmPotentialLaw
      rw [withDensity_fst_compProd H _ d hd]
    _ = (H.withDensity d).map k ⊗ₘ
        (releasedPairLaw Prel).condKernel := by
      exact map_compProd_comap (H.withDensity d)
        (releasedPairLaw Prel).condKernel k hk
    _ = scoreAssignedKeyLaw H g a ⊗ₘ
        (releasedPairLaw Prel).condKernel := by
      rfl

private lemma reconstructedAssignmentDensity_sum {ε : ℝ}
    (hOverlap : Overlap ε)
    (p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace)) :
    reconstructedAssignmentDensity false p +
      reconstructedAssignmentDensity true p = 1 := by
  have he0 : 0 ≤ (p.1 : ℝ) := by
    exact le_trans hOverlap.1.le p.1.property.1
  have he1 : (p.1 : ℝ) ≤ 1 := by linarith [p.1.property.2, hOverlap.1]
  unfold reconstructedAssignmentDensity armProb
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr he1) he0]
  norm_num

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedAssignmentMeasures_sum {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (hOverlap : Overlap ε) :
    (reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity false) +
      (reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity true) =
      reconstructedLatentLaw H g Prel hg := by
  rw [← withDensity_add_left (reconstructedAssignmentDensity_measurable false)]
  have hfun : reconstructedAssignmentDensity false +
      reconstructedAssignmentDensity true =
      (1 : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) → ENNReal) := by
    funext p
    exact reconstructedAssignmentDensity_sum hOverlap p
  rw [hfun, withDensity_one]
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (hOverlap : Overlap ε) :
    IsProbabilityMeasure (reconstructedFullLaw H g Prel hg) := by
  rw [isProbabilityMeasure_iff]
  unfold reconstructedFullLaw
  rw [Measure.add_apply,
    Measure.map_apply (reconstructedFullRow_measurable g hg false) MeasurableSet.univ,
    Measure.map_apply (reconstructedFullRow_measurable g hg true) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [← Measure.add_apply, reconstructedAssignmentMeasures_sum H g Prel hg hOverlap]
  exact isProbabilityMeasure_iff.mp inferInstance

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_scoreMarginal {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (hOverlap : Overlap ε) :
    ScoreMarginal (reconstructedFullLaw H g Prel hg) H := by
  unfold ScoreMarginal reconstructedFullLaw
  rw [Measure.map_add _ _ (by unfold score; fun_prop),
    Measure.map_map (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg false),
    Measure.map_map (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg true)]
  change Measure.map Prod.fst
      ((reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity false)) +
      Measure.map Prod.fst
      ((reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity true)) = H
  rw [← Measure.map_add _ _ measurable_fst,
    reconstructedAssignmentMeasures_sum H g Prel hg hOverlap]
  exact reconstructedLatentLaw_fst H g Prel hg

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_consistency {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) :
    Consistency (reconstructedFullLaw H g Prel hg) := by
  unfold Consistency reconstructedFullLaw
  rw [ae_add_measure_iff]
  constructor
  · have hrow := reconstructedFullRow_measurable g hg false
    rw [ae_map_iff hrow.aemeasurable (by
      exact measurableSet_eq_fun (by unfold observed; fun_prop)
        (by
          have hcond : MeasurableSet {ω : FullRow ε J | arm ω = true} :=
            measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
          exact Measurable.ite hcond (by unfold outcome1; fun_prop)
            (by unfold outcome0; fun_prop)))]
    filter_upwards [] with p
    rfl
  · have hrow := reconstructedFullRow_measurable g hg true
    rw [ae_map_iff hrow.aemeasurable (by
      exact measurableSet_eq_fun (by unfold observed; fun_prop)
        (by
          have hcond : MeasurableSet {ω : FullRow ε J | arm ω = true} :=
            measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
          exact Measurable.ite hcond (by unfold outcome1; fun_prop)
            (by unfold outcome0; fun_prop)))]
    filter_upwards [] with p
    rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_deterministicRelease {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) :
    DeterministicRelease g (reconstructedFullLaw H g Prel hg) := by
  unfold DeterministicRelease reconstructedFullLaw
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff (reconstructedFullRow_measurable g hg false).aemeasurable (by
      exact measurableSet_eq_fun (by unfold label; fun_prop)
        (hg.comp (by unfold score; fun_prop)))]
    filter_upwards [] with p
    rfl
  · rw [ae_map_iff (reconstructedFullRow_measurable g hg true).aemeasurable (by
      exact measurableSet_eq_fun (by unfold label; fun_prop)
        (hg.comp (by unfold score; fun_prop)))]
    filter_upwards [] with p
    rfl

private lemma latentScore_integrable {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) :
    Integrable (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) =>
      (p.1 : ℝ)) (reconstructedLatentLaw H g Prel hg) := by
  apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  rcases p.1.property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma assignmentTrue_real {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (hOverlap : Overlap ε)
    (D : Set (ScoreSpace ε × (OutcomeSpace × OutcomeSpace)))
    (hD : MeasurableSet D) :
    ((reconstructedLatentLaw H g Prel hg).withDensity
      (reconstructedAssignmentDensity true)).real D =
      ∫ p in D, (p.1 : ℝ) ∂reconstructedLatentLaw H g Prel hg := by
  have hint : IntegrableOn
      (fun p : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) => (p.1 : ℝ)) D
      (reconstructedLatentLaw H g Prel hg) :=
    (latentScore_integrable H g Prel hg).integrableOn
  unfold Measure.real reconstructedAssignmentDensity armProb
  rw [withDensity_apply _ hD]
  simp only [ite_true]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun p => by
      exact le_trans hOverlap.1.le p.1.property.1)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun p =>
    le_trans hOverlap.1.le p.1.property.1)]

private lemma reconstructedComponent_finite {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (hOverlap : Overlap ε)
    (a : ArmSpace) : IsFiniteMeasure
      ((reconstructedLatentLaw H g Prel hg).withDensity
        (reconstructedAssignmentDensity a)) := by
  let f : ScoreSpace ε × (OutcomeSpace × OutcomeSpace) → ℝ :=
    fun p => armProb a p.1
  have hf : Integrable f (reconstructedLatentLaw H g Prel hg) := by
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
    ((reconstructedLatentLaw H g Prel hg).withDensity
      (fun p => ENNReal.ofReal (f p)))
  exact isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral

private lemma fullScore_integrable_finite {ε : ℝ} {J : ℕ}
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

private lemma latentScore_integrable_finite {ε : ℝ}
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

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_randomizedAssignment {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g) (hOverlap : Overlap ε) :
    RandomizedAssignment (reconstructedFullLaw H g Prel hg) := by
  intro B hB
  let L := reconstructedLatentLaw H g Prel hg
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
  letI : IsFiniteMeasure M₀ := reconstructedComponent_finite H g Prel hg hOverlap false
  letI : IsFiniteMeasure M₁ := reconstructedComponent_finite H g Prel hg hOverlap true
  have hmap0 : IsFiniteMeasure (M₀.map (reconstructedFullRow g false)) := ⟨by
    rw [Measure.map_apply (reconstructedFullRow_measurable g hg false)
      MeasurableSet.univ]
    simpa using measure_lt_top M₀ Set.univ
  ⟩
  have hmap1 : IsFiniteMeasure (M₁.map (reconstructedFullRow g true)) := ⟨by
    rw [Measure.map_apply (reconstructedFullRow_measurable g hg true)
      MeasurableSet.univ]
    simpa using measure_lt_top M₁ Set.univ
  ⟩
  change (reconstructedFullLaw H g Prel hg).real S =
    ∫ ω in T, (score ω : ℝ) ∂reconstructedFullLaw H g Prel hg
  have hleft : (reconstructedFullLaw H g Prel hg).real S =
      ∫ p in D, (p.1 : ℝ) ∂L := by
    unfold reconstructedFullLaw
    rw [Measure.real_def, Measure.add_apply,
      Measure.map_apply (reconstructedFullRow_measurable g hg false) hS,
      Measure.map_apply (reconstructedFullRow_measurable g hg true) hS,
      hpre0S, hpre1S, measure_empty, zero_add]
    change M₁.real D = _
    exact assignmentTrue_real H g Prel hg hOverlap D hD
  rw [hleft]
  unfold reconstructedFullLaw
  letI : IsFiniteMeasure (M₀.map (reconstructedFullRow g false)) := hmap0
  letI : IsFiniteMeasure (M₁.map (reconstructedFullRow g true)) := hmap1
  rw [Measure.restrict_add,
    integral_add_measure (fullScore_integrable_finite _).integrableOn
      (fullScore_integrable_finite _).integrableOn,
    setIntegral_map hT (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg false).aemeasurable,
    setIntegral_map hT (by unfold score; fun_prop)
      (reconstructedFullRow_measurable g hg true).aemeasurable,
    hpre0T, hpre1T]
  change (∫ p in D, (p.1 : ℝ) ∂L) =
    (∫ p in D, (p.1 : ℝ) ∂M₀) + (∫ p in D, (p.1 : ℝ) ∂M₁)
  rw [← integral_add_measure
    (latentScore_integrable_finite M₀).integrableOn
    (latentScore_integrable_finite M₁).integrableOn]
  rw [← Measure.restrict_add, reconstructedAssignmentMeasures_sum H g Prel hg hOverlap]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_releasedPairLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε) :
    (reconstructedFullLaw H g Prel hg).map
        (fun ω => ((label ω, arm ω), observed ω)) =
      releasedPairLaw Prel := by
  have hp : Measurable
      (fun ω : FullRow ε J => ((label ω, arm ω), observed ω)) := by
    unfold label arm observed
    fun_prop
  unfold reconstructedFullLaw
  rw [Measure.map_add _ _ hp,
    Measure.map_map hp (reconstructedFullRow_measurable g hg false),
    Measure.map_map hp (reconstructedFullRow_measurable g hg true)]
  change ((reconstructedLatentLaw H g Prel hg).withDensity
      (reconstructedAssignmentDensity false)).map
        (fun p => ((g p.1, false), p.2.1)) +
    ((reconstructedLatentLaw H g Prel hg).withDensity
      (reconstructedAssignmentDensity true)).map
        (fun p => ((g p.1, true), p.2.2)) = _
  have hfalse := reconstructedAssignedReleasedPairLaw H g Prel hg false
  have htrue := reconstructedAssignedReleasedPairLaw H g Prel hg true
  simp only [Bool.false_eq_true, ↓reduceIte] at hfalse
  simp only [↓reduceIte] at htrue
  rw [hfalse, htrue, ← Measure.compProd_add_left]
  change randomizedKeyLaw H g ⊗ₘ (releasedPairLaw Prel).condKernel = _
  rw [randomizedKeyLaw_eq_releasedKeyLaw H g Prel hMass hOverlap,
    releasedPairLaw_disintegrate Prel]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_releasedLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε) :
    ReleasedLaw (reconstructedFullLaw H g Prel hg) Prel := by
  unfold ReleasedLaw releasedLaw
  have hp : Measurable
      (fun ω : FullRow ε J => ((label ω, arm ω), observed ω)) := by
    unfold label arm observed
    fun_prop
  have hu : Measurable
      (fun p : (LabelSpace J × ArmSpace) × OutcomeSpace =>
        (p.1.1, p.1.2, p.2)) := by fun_prop
  calc
    (reconstructedFullLaw H g Prel hg).map releasedRecord =
        ((reconstructedFullLaw H g Prel hg).map
          (fun ω => ((label ω, arm ω), observed ω))).map
          (fun p => (p.1.1, p.1.2, p.2)) := by
            rw [Measure.map_map hu hp]
            rfl
    _ = (releasedPairLaw Prel).map
        (fun p => (p.1.1, p.1.2, p.2)) := by
      rw [reconstructedFullLaw_releasedPairLaw H g Prel hg hMass hOverlap]
    _ = Prel := releasedPairLaw_map_unpair Prel

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hg,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma reconstructedFullLaw_compatibleCausalLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure Prel] (hg : Measurable g)
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε) :
    CompatibleCausalLaw H g Prel (reconstructedFullLaw H g Prel hg) := by
  exact
    { probability := reconstructedFullLaw_isProbabilityMeasure H g Prel hg hOverlap
      measurableRelease := hg
      scoreMarginal := reconstructedFullLaw_scoreMarginal H g Prel hg hOverlap
      randomizedAssignment :=
        reconstructedFullLaw_randomizedAssignment H g Prel hg hOverlap
      consistency := reconstructedFullLaw_consistency H g Prel hg
      deterministicRelease := reconstructedFullLaw_deterministicRelease H g Prel hg
      releasedLaw := reconstructedFullLaw_releasedLaw H g Prel hg hMass hOverlap }

end
end CausalSmith.PartialID.UnlinkedPropensityAte
