module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Bridge.Identification
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.DecisionSampling
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TVModel

/-!
# Independent rows in the paired attaining experiment

The finite paired sign-vector transcript factors into averaged participant rows.
Its transcript-only squared risk is the corresponding finite product integral.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [For fixed records the concrete transcript consists of independent message rows](goal). -/
-- @node: tvFrontier_fixedTranscriptLaw_product
lemma tvFrontier_fixedTranscriptLaw_product (n d : ℕ) (eps : ℝ)
    (o : Fin n → PairedSymbol d) (r : (tvFrontierProtocol n d eps).Seed) :
    fixedTranscriptLaw (tvFrontierProtocol n d eps) o r =
      Measure.pi (fun i => tvFrontierKernel n d eps i (o i)) := by
  letI : Countable (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
    change Countable (Fin n → (Fin d → Bool))
    infer_instance
  haveI : ∀ i, IsProbabilityMeasure (tvFrontierKernel n d eps i (o i)) :=
    fun i => (tvFrontierStage_markov n d eps i).isProbabilityMeasure
      ((o i,r), fun _ => fun _ => false)
  change (fixedTranscriptLaw (tvFrontierProtocol n d eps) o r :
    Measure (Fin n → (Fin d → Bool))) = _
  apply Measure.ext_of_singleton
  intro z
  change Fin n → (Fin d → Bool) at z
  erw [Measure.pi_singleton]
  exact Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw_singleton
    (tvFrontierProtocol n d eps).kernels (tvFrontierProtocol n d eps).markov
    (fun i => (o i,r)) z

/-- [Averaging independent input records preserves the product of private row laws](goal). -/
-- @node: tvFrontier_iidTranscriptLaw_product
lemma tvFrontier_iidTranscriptLaw_product (n d : ℕ) (eps : ℝ)
    (mu : Measure (PairedSymbol d)) [IsProbabilityMeasure mu]
    (r : (tvFrontierProtocol n d eps).Seed) :
    (Measure.pi (fun _ : Fin n => mu)).bind
      (fun o => fixedTranscriptLaw (tvFrontierProtocol n d eps) o r) =
      Measure.pi (fun i => mu.bind (tvFrontierKernel n d eps i)) := by
  classical
  letI : Countable (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
    change Countable (Fin n → (Fin d → Bool))
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → (Fin d → Bool))
    infer_instance
  haveI : ∀ i, IsMarkovKernel (tvFrontierKernel n d eps i) := by
    intro i
    exact ⟨fun o => (tvFrontierStage_markov n d eps i).isProbabilityMeasure
      ((o,r), fun _ => fun _ => false)⟩
  haveI : ∀ i, IsProbabilityMeasure (mu.bind (tvFrontierKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (tvFrontierKernel n d eps i).measurable.aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  apply Measure.ext_of_singleton
  intro z
  change Fin n → (Fin d → Bool) at z
  erw [Measure.bind_apply (measurableSet_singleton z)
    ((measurable_fixedTranscriptLaw (tvFrontierProtocol n d eps)).comp
      (show Measurable (fun o : Fin n → PairedSymbol d => (o,r)) by fun_prop)).aemeasurable,
    Measure.pi_singleton]
  simp only [tvFrontier_fixedTranscriptLaw_product]
  change (∫⁻ o, (Measure.pi (fun i => tvFrontierKernel n d eps i (o i))) {z} ∂Measure.pi (fun _ : Fin n => mu)) = _
  simp_rw [ Measure.pi_singleton,
    Measure.bind_apply (measurableSet_singleton _) (Kernel.measurable _).aemeasurable]
  simp_rw [lintegral_fintype, Measure.pi_singleton]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i o => tvFrontierKernel n d eps i o {z i} * mu {o})).symm

/-- [The actual sampling decision law has the independent averaged message-row marginal](goal). -/
-- @node: tvFrontier_sampling_transcript_product
lemma tvFrontier_sampling_transcript_product (n d : ℕ) (eps : ℝ)
    (p : Measure (PairedSymbol d)) [IsProbabilityMeasure p] :
    (canonicalDecisionLaw (tvFrontierProtocol n d eps) p).map
      (fun w => w.1) = Measure.pi (fun i => p.bind (tvFrontierKernel n d eps i)) := by
  apply Measure.ext
  intro E hE
  erw [Measure.map_apply measurable_fst hE]
  have hpre : (fun w : DecisionSpace (tvFrontierProtocol n d eps) => w.1) ⁻¹' E =
      E ×ˢ Set.univ ×ˢ Set.univ := by ext w; simp
  rw [hpre]
  unfold canonicalDecisionLaw
  rw [product_decisionRows_rectangle _ _ E Set.univ Set.univ hE
      MeasurableSet.univ MeasurableSet.univ]
  simp only [Set.indicator_univ, tvFrontier_fixedTranscriptLaw_product]
  simp only [lintegral_const, measure_univ, mul_one, uniform01,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  have hmix := congrArg (fun L => L E)
    (tvFrontier_iidTranscriptLaw_product n d eps p (0 : Fin 1))
  erw [Measure.bind_apply hE
    ((measurable_fixedTranscriptLaw (tvFrontierProtocol n d eps)).comp
      (show Measurable (fun o : Fin n → PairedSymbol d => (o,(0 : Fin 1))) by fun_prop)).aemeasurable]
      at hmix
  simp only [tvFrontier_fixedTranscriptLaw_product] at hmix
  norm_num only [sub_zero, ENNReal.ofReal_one, mul_one]
  exact hmix

/-- [The risk of the actual transcript-only frontier estimate is a finite product-law integral](goal). -/
-- @node: tvFrontierEstimator_risk_product
lemma tvFrontierEstimator_risk_product (n d : ℕ) (eps : ℝ)
    (p : Measure (PairedSymbol d)) [IsProbabilityMeasure p] :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) p)
      (tvFrontierEstimator n d eps) (tvFromUniform p) =
      ∫⁻ z : Fin n → (Fin d → Bool),
        ENNReal.ofReal ((tvFrontierEstimate n d eps (z,(0 : Fin 1),0) - tvFromUniform p)^2)
          ∂Measure.pi (fun i => p.bind (tvFrontierKernel n d eps i)) := by
  let f : ProtocolTranscript (tvFrontierProtocol n d eps) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((tvFrontierEstimate n d eps (z,(0 : Fin 1),0) - tvFromUniform p)^2)
  have hf : Measurable f := by
    letI : Countable (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
      change Countable (Fin n → (Fin d → Bool))
      infer_instance
    letI : MeasurableSingletonClass (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
      change MeasurableSingletonClass (Fin n → (Fin d → Bool))
      infer_instance
    exact measurable_of_countable f
  have htrans := tvFrontier_sampling_transcript_product n d eps p
  change _ = ∫⁻ z, f z ∂Measure.pi (fun i => p.bind (tvFrontierKernel n d eps i))
  rw [← htrans]
  erw [lintegral_map hf measurable_fst]
  unfold squaredRisk
  apply lintegral_congr
  intro w
  rfl

/-- Assume [the stated hi condition](hyp:hi), [the causal-model conditions for the data law](hyp:hP), and [positive dimension](hyp:hd). [An active paired row, averaged over the causal signed marginal, is exactly the vector-message law used by the moment calibration](goal). -/
-- @node: tvFrontier_active_row_law
lemma tvFrontier_active_row_law (n d : ℕ) (eps : ℝ) (i : Fin n)
    (hi : i.val < 2*(frontierDesign n d eps).resources.m)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d) :
    (pairedLaw (contrast P)).bind (tvFrontierKernel n d eps i) =
      vectorMessageLaw P eps := by
  classical
  rw [← causal_signed_law P hP hd]
  apply Measure.ext
  intro E hE
  rw [Measure.bind_apply hE (Kernel.measurable _).aemeasurable]
  unfold vectorMessageLaw
  rw [Measure.bind_apply hE (Kernel.measurable _).aemeasurable]
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro o
  change atomLaw (fun z => if i.val < 2*(frontierDesign n d eps).resources.m then
    _ else _) E = atomLaw (vectorMass eps o) E
  simp only [hi, ↓reduceIte]
  congr 1
  apply congrArg atomLaw
  funext z
  rcases o with ⟨j, a, y⟩
  cases a <;> cases y <;> simp [vectorMass, signedObserve, obsSign, signVal]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [positive dimension](hyp:hd), [the stated hg condition](hyp:hg), and [the stated hactive condition](hyp:hactive). [Distinct active participants in the paired protocol provide exactly the iid vector block experiment, so all finite moment calibrations apply to their messages](goal). -/
-- @node: tvFrontier_vector_selection_law
lemma tvFrontier_vector_selection_law {n d k : ℕ} (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d)
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hactive : ∀ i, (g i).val < 2*(frontierDesign n d eps).resources.m) :
    (canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))).map
      (fun w i => w.1 (g i)) = vectorBlockLaw P eps k := by
  haveI : IsProbabilityMeasure (pairedLaw (contrast P)) :=
    pairedFamily_subset_simplex hd
      (Set.mem_image_of_mem pairedLaw (contrast_mem_parameterCube P hP))
  haveI : ∀ i, IsMarkovKernel (tvFrontierKernel n d eps i) := by
    intro i
    exact ⟨fun v => (tvFrontierStage_markov n d eps i).isProbabilityMeasure
      ((v,(0 : Fin 1)), fun _ => fun _ => false)⟩
  haveI : ∀ i, IsProbabilityMeasure
      ((pairedLaw (contrast P)).bind (tvFrontierKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  have hmap : (fun w : DecisionSpace (tvFrontierProtocol n d eps) =>
      fun i => w.1 (g i)) = (fun z : Fin n → Fin d → Bool => fun i => z (g i)) ∘
        (fun w => w.1) := rfl
  rw [hmap]
  erw [← Measure.map_map (by fun_prop) measurable_fst]
  erw [tvFrontier_sampling_transcript_product n d eps (pairedLaw (contrast P))]
  have hind := (iIndepFun_pi
    (μ := fun i => (pairedLaw (contrast P)).bind (tvFrontierKernel n d eps i))
    (X := fun (_ : Fin n) (z : Fin d → Bool) => z)
    (fun _ => measurable_id.aemeasurable)).precomp hg
  have hlaw := hind.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (g i)).aemeasurable)
  refine hlaw.trans ?_
  unfold vectorBlockLaw
  congr 1
  funext i
  rw [(measurePreserving_eval
    (fun i => (pairedLaw (contrast P)).bind (tvFrontierKernel n d eps i)) (g i)).map_eq]
  exact tvFrontier_active_row_law n d eps (g i) (hactive i) P hP hd

end CausalSmith.Stat.LdpOptvalueUniformFrontier
