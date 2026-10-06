module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.BaselineCalibration

/-!
# Half-block binary/vector protocol

The two-cell construction assigns the first half of people to binary outcome
releases and the remaining people to signed-vector releases. All rows are total,
private, and independent of histories; their sampling transcript has product law.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), [the participant index](hyp:i), [the observed participant record](hyp:o), and [the parameter z](hyp:z). [Original-input participant-specific finite atom channel](goal). -/
-- @node: twoCellMass
def twoCellMass (n d : ℕ) (eps : ℝ) (i : Fin n) (o : ObsRecord d)
    (z : FrontierMessage d) : ℝ :=
  if i.val < (n / 2) then
    (1+privacyDelta eps*signVal o.2.2*signVal z.1)/2 *
      (if z.2 = (fun _ => false) then 1 else 0)
  else vectorMass eps o z.2 * (if z.1 = false then 1 else 0)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Finite participant channel ignoring histories](goal). -/
-- @node: twoCellKernel
def twoCellKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel (ObsRecord d) (FrontierMessage d) :=
  ⟨fun o => atomLaw (twoCellMass n d eps i o), measurable_of_countable _⟩
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Participant stage with ignored histories](goal). -/
-- @node: twoCellStageKernel
def twoCellStageKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel ((ObsRecord d × Fin 1) ×
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.History
        (fun _ : Fin n => FrontierMessage d) i.val (Nat.le_of_lt i.isLt)) (FrontierMessage d) :=
  (twoCellKernel n d eps i).comap (fun w => w.1.1) (measurable_fst.comp measurable_fst)
/-- [Stage Markov certificate](goal). -/
-- @node: twoCellStage_markov
lemma twoCellStage_markov (n d : ℕ) (eps : ℝ) (i : Fin n) :
    IsMarkovKernel (twoCellStageKernel n d eps i) := by
  classical
  have hm : ∀ o z, 0 ≤ twoCellMass n d eps i o z := by
    intro o z
    unfold twoCellMass
    split
    · exact mul_nonneg (binaryOutcomeMass_nonneg eps o.2.2 z.1) (by split <;> positivity)
    · exact mul_nonneg (vectorMass_nonneg eps o z.2) (by split <;> positivity)
  have hs : ∀ o, ∑ z, twoCellMass n d eps i o z = 1 := by
    intro o
    unfold twoCellMass
    by_cases hi : i.val < n / 2
    · simp only [hi, ↓reduceIte]
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum]
      simpa [Fintype.sum_bool] using binaryOutcomeMass_sum eps o.2.2
    · simp only [hi, ↓reduceIte]
      rw [Fintype.sum_prod_type]
      simp [vectorMass_sum]
  have hk : IsMarkovKernel (twoCellKernel n d eps i) := by
    constructor
    intro o
    constructor
    change atomLaw _ Set.univ = 1
    simp only [atomLaw, Measure.finsetSum_apply, MeasurableSet.univ,
      Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hm o z), hs]
    simp
  letI := hk
  unfold twoCellStageKernel
  infer_instance
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Explicit noninteractive original-record attaining protocol](goal). -/
-- @node: twoCellProtocol
def twoCellProtocol (n d : ℕ) (eps : ℝ) : LocalProtocol n (ObsRecord d) where
  Seed := Fin 1
  seedMeasurable := inferInstance
  seedStandard := inferInstance
  seedLaw := Measure.dirac 0
  seedProbability := inferInstance
  Message := fun _ => FrontierMessage d
  messageMeasurable := fun _ => inferInstance
  messageStandard := fun _ => inferInstance
  kernels := twoCellStageKernel n d eps
  markov := twoCellStage_markov n d eps
/-- Assume [a nonnegative privacy budget](hyp:heps). [Each branch of the combined finite message channel satisfies the atomwise privacy bound](goal). -/
-- @node: twoCellMass_privacy
lemma twoCellMass_privacy (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (i : Fin n) (o o' : ObsRecord d) (z : FrontierMessage d) :
    twoCellMass n d eps i o z ≤ Real.exp eps * twoCellMass n d eps i o' z := by
  unfold twoCellMass
  by_cases hi : i.val < n / 2
  · simp only [hi, ↓reduceIte]
    split_ifs
    · simpa using binaryOutcomeMass_privacy eps heps o.2.2 o'.2.2 z.1
    · simp
  · simp only [hi, ↓reduceIte]
    split_ifs
    · simpa using vectorMass_privacy eps heps o o' z.2
    · simp

/-- Assume [a nonnegative privacy budget](hyp:heps). [Summing the finite atom inequalities proves privacy for every message event](goal). -/
-- @node: twoCellKernel_privacy
lemma twoCellKernel_privacy (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (i : Fin n) (o o' : ObsRecord d) (E : Set (FrontierMessage d)) :
    twoCellKernel n d eps i o E ≤
      ENNReal.ofReal (Real.exp eps) * twoCellKernel n d eps i o' E := by
  classical
  change (atomLaw (twoCellMass n d eps i o)) E ≤
    ENNReal.ofReal (Real.exp eps) * (atomLaw (twoCellMass n d eps i o')) E
  simp only [atomLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos eps).le]
  simpa only [mul_comm] using
    mul_le_mul_right (ENNReal.ofReal_le_ofReal (twoCellMass_privacy n d eps heps i o o' z))
      ((Measure.dirac z) E)

/-- Assume [a nonnegative privacy budget](hyp:heps). [The entire resource-selected original-input procedure is noninteractive and pure private](goal). -/
-- @node: twoCellProtocol_noninteractive
lemma twoCellProtocol_noninteractive (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    NoninteractiveClass (twoCellProtocol n d eps) eps := by
  constructor
  · intro i o o' eta r E _
    exact twoCellKernel_privacy n d eps heps i o o' E
  · intro i o eta eta' r
    rfl

/-- [For fixed records the concrete transcript consists of independent message rows](goal). -/
-- @node: twoCell_fixedTranscriptLaw_product
lemma twoCell_fixedTranscriptLaw_product (n d : ℕ) (eps : ℝ)
    (o : Fin n → ObsRecord d) (r : (twoCellProtocol n d eps).Seed) :
    fixedTranscriptLaw (twoCellProtocol n d eps) o r =
      Measure.pi (fun i => twoCellKernel n d eps i (o i)) := by
  letI : Countable (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  haveI : ∀ i, IsProbabilityMeasure (twoCellKernel n d eps i (o i)) :=
    fun i => (twoCellStage_markov n d eps i).isProbabilityMeasure
      ((o i,r), fun _ => (false,fun _ => false))
  change (fixedTranscriptLaw (twoCellProtocol n d eps) o r :
    Measure (Fin n → FrontierMessage d)) = _
  apply Measure.ext_of_singleton
  intro z
  change Fin n → FrontierMessage d at z
  erw [Measure.pi_singleton]
  exact Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw_singleton
    (twoCellProtocol n d eps).kernels (twoCellProtocol n d eps).markov
    (fun i => (o i,r)) z

/-- [Averaging independent input records preserves the product of private row laws](goal). -/
-- @node: twoCell_iidTranscriptLaw_product
lemma twoCell_iidTranscriptLaw_product (n d : ℕ) (eps : ℝ)
    (mu : Measure (ObsRecord d)) [IsProbabilityMeasure mu]
    (r : (twoCellProtocol n d eps).Seed) :
    (Measure.pi (fun _ : Fin n => mu)).bind
      (fun o => fixedTranscriptLaw (twoCellProtocol n d eps) o r) =
      Measure.pi (fun i => mu.bind (twoCellKernel n d eps i)) := by
  classical
  letI : Countable (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → FrontierMessage d)
    infer_instance
  haveI : ∀ i, IsMarkovKernel (twoCellKernel n d eps i) := by
    intro i
    exact ⟨fun o => (twoCellStage_markov n d eps i).isProbabilityMeasure
      ((o,r), fun _ => (false,fun _ => false))⟩
  haveI : ∀ i, IsProbabilityMeasure (mu.bind (twoCellKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (twoCellKernel n d eps i).measurable.aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  apply Measure.ext_of_singleton
  intro z
  change Fin n → FrontierMessage d at z
  erw [Measure.bind_apply (measurableSet_singleton z)
    ((measurable_fixedTranscriptLaw (twoCellProtocol n d eps)).comp
      (show Measurable (fun o : Fin n → ObsRecord d => (o,r)) by fun_prop)).aemeasurable,
    Measure.pi_singleton]
  simp only [twoCell_fixedTranscriptLaw_product]
  change (∫⁻ o, (Measure.pi (fun i => twoCellKernel n d eps i (o i))) {z} ∂Measure.pi (fun _ : Fin n => mu)) = _
  simp_rw [ Measure.pi_singleton,
    Measure.bind_apply (measurableSet_singleton _) (Kernel.measurable _).aemeasurable]
  simp_rw [lintegral_fintype, Measure.pi_singleton]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i o => twoCellKernel n d eps i o {z i} * mu {o})).symm

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The actual sampling decision law has the independent averaged message-row marginal](goal). -/
-- @node: twoCell_sampling_transcript_product
lemma twoCell_sampling_transcript_product (n d : ℕ) (eps : ℝ)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    (decisionLaw S (twoCellProtocol n d eps) P).map
      (fun w => w.1) =
      Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i)) := by
  haveI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  apply Measure.ext
  intro E hE
  erw [Measure.map_apply measurable_fst hE]
  have hpre : (fun w : DecisionSpace (twoCellProtocol n d eps) => w.1) ⁻¹' E =
      E ×ˢ Set.univ ×ˢ Set.univ := by ext w; simp
  rw [hpre]
  unfold decisionLaw
  rw [iid_sampling_inputLaw S hIID hRandom (twoCellProtocol n d eps) P hP,
    product_decisionRows_rectangle _ _ E Set.univ Set.univ hE
      MeasurableSet.univ MeasurableSet.univ]
  simp only [Set.indicator_univ, twoCell_fixedTranscriptLaw_product]
  simp only [lintegral_const, measure_univ, mul_one, uniform01,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  have hmix := congrArg (fun L => L E)
    (twoCell_iidTranscriptLaw_product n d eps (observedLaw P) (0 : Fin 1))
  erw [Measure.bind_apply hE
    ((measurable_fixedTranscriptLaw (twoCellProtocol n d eps)).comp
      (show Measurable (fun o : Fin n → ObsRecord d => (o,(0 : Fin 1))) by fun_prop)).aemeasurable]
      at hmix
  simp only [twoCell_fixedTranscriptLaw_product] at hmix
  norm_num only [sub_zero, ENNReal.ofReal_one, mul_one]
  exact hmix


end CausalSmith.Stat.LdpOptvalueUniformFrontier
