module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Upper

/-!
# Independent message rows in the attaining experiment

The concrete noninteractive transcript law factors into participant row laws.
Averaging the iid inputs preserves this product structure, allowing the finite
vector-block moment calculations to apply to the actual private transcript.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [For fixed records the concrete transcript consists of independent message rows](goal). -/
-- @node: frontier_fixedTranscriptLaw_product
lemma frontier_fixedTranscriptLaw_product (n d : ℕ) (eps : ℝ)
    (o : Fin n → ObsRecord d) (r : (frontierProtocol n d eps).Seed) :
    fixedTranscriptLaw (frontierProtocol n d eps) o r =
      Measure.pi (fun i => frontierKernel n d eps i (o i)) := by
  letI : Countable (ProtocolTranscript (frontierProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  haveI : ∀ i, IsProbabilityMeasure (frontierKernel n d eps i (o i)) :=
    fun i => (frontierStage_markov n d eps i).isProbabilityMeasure
      ((o i,r), fun _ => (false,fun _ => false))
  change (fixedTranscriptLaw (frontierProtocol n d eps) o r :
    Measure (Fin n → FrontierMessage d)) = _
  apply Measure.ext_of_singleton
  intro z
  change Fin n → FrontierMessage d at z
  erw [Measure.pi_singleton]
  exact Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw_singleton
    (frontierProtocol n d eps).kernels (frontierProtocol n d eps).markov
    (fun i => (o i,r)) z

/-- [Averaging independent input records preserves the product of private row laws](goal). -/
-- @node: frontier_iidTranscriptLaw_product
lemma frontier_iidTranscriptLaw_product (n d : ℕ) (eps : ℝ)
    (mu : Measure (ObsRecord d)) [IsProbabilityMeasure mu]
    (r : (frontierProtocol n d eps).Seed) :
    (Measure.pi (fun _ : Fin n => mu)).bind
      (fun o => fixedTranscriptLaw (frontierProtocol n d eps) o r) =
      Measure.pi (fun i => mu.bind (frontierKernel n d eps i)) := by
  classical
  letI : Countable (ProtocolTranscript (frontierProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (frontierProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → FrontierMessage d)
    infer_instance
  haveI : ∀ i, IsMarkovKernel (frontierKernel n d eps i) := by
    intro i
    exact ⟨fun o => (frontierStage_markov n d eps i).isProbabilityMeasure
      ((o,r), fun _ => (false,fun _ => false))⟩
  haveI : ∀ i, IsProbabilityMeasure (mu.bind (frontierKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (frontierKernel n d eps i).measurable.aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  apply Measure.ext_of_singleton
  intro z
  change Fin n → FrontierMessage d at z
  erw [Measure.bind_apply (measurableSet_singleton z)
    ((measurable_fixedTranscriptLaw (frontierProtocol n d eps)).comp
      (show Measurable (fun o : Fin n → ObsRecord d => (o,r)) by fun_prop)).aemeasurable,
    Measure.pi_singleton]
  simp only [frontier_fixedTranscriptLaw_product]
  change (∫⁻ o, (Measure.pi (fun i => frontierKernel n d eps i (o i))) {z} ∂Measure.pi (fun _ : Fin n => mu)) = _
  simp_rw [ Measure.pi_singleton,
    Measure.bind_apply (measurableSet_singleton _) (Kernel.measurable _).aemeasurable]
  simp_rw [lintegral_fintype, Measure.pi_singleton]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i o => frontierKernel n d eps i o {z i} * mu {o})).symm

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The actual sampling decision law has the independent averaged message-row marginal](goal). -/
-- @node: frontier_sampling_transcript_product
lemma frontier_sampling_transcript_product (n d : ℕ) (eps : ℝ)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    (decisionLaw S (frontierProtocol n d eps) P).map
      (fun w => w.1) =
      Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i)) := by
  haveI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  apply Measure.ext
  intro E hE
  erw [Measure.map_apply measurable_fst hE]
  have hpre : (fun w : DecisionSpace (frontierProtocol n d eps) => w.1) ⁻¹' E =
      E ×ˢ Set.univ ×ˢ Set.univ := by ext w; simp
  rw [hpre]
  unfold decisionLaw
  rw [iid_sampling_inputLaw S hIID hRandom (frontierProtocol n d eps) P hP,
    product_decisionRows_rectangle _ _ E Set.univ Set.univ hE
      MeasurableSet.univ MeasurableSet.univ]
  simp only [Set.indicator_univ, frontier_fixedTranscriptLaw_product]
  simp only [lintegral_const, measure_univ, mul_one, uniform01,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  have hmix := congrArg (fun L => L E)
    (frontier_iidTranscriptLaw_product n d eps (observedLaw P) (0 : Fin 1))
  erw [Measure.bind_apply hE
    ((measurable_fixedTranscriptLaw (frontierProtocol n d eps)).comp
      (show Measurable (fun o : Fin n → ObsRecord d => (o,(0 : Fin 1))) by fun_prop)).aemeasurable]
      at hmix
  simp only [frontier_fixedTranscriptLaw_product] at hmix
  norm_num only [sub_zero, ENNReal.ofReal_one, mul_one]
  exact hmix

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The risk of the actual transcript-only frontier estimate is a finite product-law integral](goal). -/
-- @node: frontierEstimator_risk_product
lemma frontierEstimator_risk_product (n d : ℕ) (eps : ℝ)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    squaredRisk (decisionLaw S (frontierProtocol n d eps) P)
      (frontierEstimator n d eps) (value P) =
      ∫⁻ z : Fin n → FrontierMessage d,
        ENNReal.ofReal ((frontierEstimate n d eps (z,(0 : Fin 1),0) - value P)^2)
          ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i)) := by
  let f : ProtocolTranscript (frontierProtocol n d eps) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((frontierEstimate n d eps (z,(0 : Fin 1),0) - value P)^2)
  have hf : Measurable f := by
    letI : Countable (ProtocolTranscript (frontierProtocol n d eps)) := by
      change Countable (Fin n → FrontierMessage d)
      infer_instance
    letI : MeasurableSingletonClass (ProtocolTranscript (frontierProtocol n d eps)) := by
      change MeasurableSingletonClass (Fin n → FrontierMessage d)
      infer_instance
    exact measurable_of_countable f
  have htrans := frontier_sampling_transcript_product n d eps S hIID hRandom P hP
  change _ = ∫⁻ z, f z ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))
  rw [← htrans]
  erw [lintegral_map hf measurable_fst]
  unfold squaredRisk
  apply lintegral_congr
  intro w
  rfl

end CausalSmith.Stat.LdpOptvalueUniformFrontier
