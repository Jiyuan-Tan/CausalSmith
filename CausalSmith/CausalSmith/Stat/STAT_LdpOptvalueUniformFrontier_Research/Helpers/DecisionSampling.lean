module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Decision
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TranscriptPreprocessing

/-!
# Sampling and analyst randomness

Probability, measurability and independent analyst-coin factorization of causal decision laws.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- The finite causal value is [measurable in the population law](goal). -/
-- @node: measurable_causal_value
@[fun_prop] lemma measurable_causal_value : Measurable (value (d := d)) := by
  unfold value armMean Measure.real
  have h (E : Set (FullRecord d)) : Measurable (fun P : Measure (FullRecord d) => (P E).toReal) :=
    (Measure.measurable_coe (MeasurableSet.of_discrete : MeasurableSet E)).ennreal_toReal
  fun_prop

/-- A sampling scheme whose law is [measurable](hyp:hS) induces a [measurable decision
experiment](goal). -/
-- @node: measurable_sampling_decisionLaw
@[fun_prop] lemma measurable_sampling_decisionLaw
    (S : SamplingScheme n d) (Q : LocalProtocol n (ObsRecord d))
    (hS : Measurable (S Q.Seed Q.seedLaw)) : Measurable (decisionLaw S Q) := by
  exact (Measure.measurable_bind' (measurable_protocol_decisionRows Q)).comp hS

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The two sampling conditions identify the input law, including both independent coins](goal). -/
-- @node: iid_sampling_inputLaw
lemma iid_sampling_inputLaw (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    S Q.Seed Q.seedLaw P =
      (Measure.pi (fun _ : Fin n => observedLaw P)).prod (Q.seedLaw.prod uniform01) := by
  rw [hRandom Q.Seed Q.seedLaw P hP, hIID Q.Seed Q.seedLaw P hP]

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [Every causal decision row is a probability law under the stated sampling scheme](goal). -/
-- @node: sampling_decisionLaw_probability
lemma sampling_decisionLaw_probability (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    IsProbabilityMeasure (decisionLaw S Q P) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  haveI : IsProbabilityMeasure (S Q.Seed Q.seedLaw P) := by
    rw [iid_sampling_inputLaw S hIID hRandom Q P hP]
    infer_instance
  apply isProbabilityMeasure_bind (measurable_protocol_decisionRows Q).aemeasurable
  exact Filter.Eventually.of_forall (fun w => by
    haveI : IsProbabilityMeasure (fixedTranscriptLaw Q w.1 w.2.1) :=
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_transcriptLaw
        Q.kernels Q.markov (fun i => (w.1 i,w.2.1))
    exact Measure.isProbabilityMeasure_map (by fun_prop))

/-- Assume [the set hE](hyp:hE), [the set hF](hyp:hF), and [the set hG](hyp:hG). [Rectangle probabilities separate the independent analyst coin from the transcript experiment](goal). -/
-- @node: product_decisionRows_rectangle
lemma product_decisionRows_rectangle {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) (mu : Measure (Fin n → α)) [IsProbabilityMeasure mu]
    (E : Set (ProtocolTranscript Q)) (F : Set Q.Seed) (G : Set ℝ)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hG : MeasurableSet G) :
    ((mu.prod (Q.seedLaw.prod uniform01)).bind (fun w =>
      (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2))))
        (E ×ˢ F ×ˢ G) =
      (∫⁻ o, ∫⁻ r, F.indicator (fun r => fixedTranscriptLaw Q o r E) r ∂Q.seedLaw ∂mu) *
        uniform01 G := by
  classical
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  rw [Measure.bind_apply (hE.prod (hF.prod hG))
    (measurable_protocol_decisionRows Q).aemeasurable]
  have hmap (o : Fin n → α) (r : Q.Seed) (u : ℝ) :
      ((fixedTranscriptLaw Q o r).map (fun z => (z,r,u))) (E ×ˢ F ×ˢ G) =
      (fixedTranscriptLaw Q o r) ((fun z => (z,r,u)) ⁻¹' (E ×ˢ F ×ˢ G)) :=
    Measure.map_apply (by fun_prop) (hE.prod (hF.prod hG))
  have hmeas := (Measure.measurable_coe (hE.prod (hF.prod hG))).comp
    (measurable_protocol_decisionRows Q)
  simp only [Function.comp_def] at hmeas
  rw [lintegral_prod _ hmeas.aemeasurable]
  have htonelli (o : Fin n → α) :
      (∫⁻ p : Q.Seed × ℝ,
        ((fixedTranscriptLaw Q o p.1).map (fun z => (z,p.1,p.2)))
          (E ×ˢ F ×ˢ G) ∂Q.seedLaw.prod uniform01) =
      ∫⁻ r, ∫⁻ u, ((fixedTranscriptLaw Q o r).map (fun z => (z,r,u)))
        (E ×ˢ F ×ˢ G) ∂uniform01 ∂Q.seedLaw :=
    lintegral_prod _ (hmeas.comp (show Measurable (fun p : Q.Seed × ℝ => (o,p))
      by fun_prop)).aemeasurable
  simp_rw [htonelli, hmap]
  have hpre (r : Q.Seed) (u : ℝ) :
      (fun z : ProtocolTranscript Q => (z,r,u)) ⁻¹' (E ×ˢ F ×ˢ G) =
        if r ∈ F ∧ u ∈ G then E else ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod]
    split_ifs <;> simp_all
  simp_rw [hpre]
  have hinner (o : Fin n → α) (r : Q.Seed) :
      (∫⁻ u, (fixedTranscriptLaw Q o r) (if r ∈ F ∧ u ∈ G then E else ∅) ∂uniform01) =
        F.indicator (fun r => fixedTranscriptLaw Q o r E) r * uniform01 G := by
    by_cases hr : r ∈ F
    · simp only [hr, true_and, Set.indicator_of_mem hr, apply_ite, measure_empty]
      change (∫⁻ u, G.indicator (fun _ => fixedTranscriptLaw Q o r E) u ∂uniform01) = _
      rw [lintegral_indicator_const hG]
    · simp [hr]
  simp_rw [hinner]
  simp_rw [lintegral_mul_const' _ _ (measure_ne_top uniform01 G)]

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The analyst coin remains independent after any sequential transcript is generated](goal). -/
-- @node: sampling_decisionLaw_randomizer
lemma sampling_decisionLaw_randomizer (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    decisionLaw S Q P =
      (((decisionLaw S Q P).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) := by
  haveI := sampling_decisionLaw_probability S hIID hRandom Q P hP
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  have hrect (E : Set (ProtocolTranscript Q)) (F : Set Q.Seed) (G : Set ℝ)
      (hE : MeasurableSet E) (hF : MeasurableSet F) (hG : MeasurableSet G) :
      (decisionLaw S Q P) (E ×ˢ F ×ˢ G) =
        (∫⁻ o, ∫⁻ r, F.indicator (fun r => fixedTranscriptLaw Q o r E) r
          ∂Q.seedLaw ∂Measure.pi (fun _ : Fin n => observedLaw P)) * uniform01 G := by
    unfold decisionLaw
    rw [iid_sampling_inputLaw S hIID hRandom Q P hP]
    exact product_decisionRows_rectangle Q _ E F G hE hF hG
  apply Measure.ext_prod₃
  intro E F G hE hF hG
  rw [Measure.map_apply (by fun_prop) (hE.prod (hF.prod hG))]
  have hpre : (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) ⁻¹'
      (E ×ˢ F ×ˢ G) = (E ×ˢ F) ×ˢ G := by ext w; simp [and_assoc]
  rw [hpre, Measure.prod_prod, Measure.map_apply (by fun_prop) (hE.prod hF)]
  have hmarg : (fun w : DecisionSpace Q => (w.1,w.2.1)) ⁻¹' (E ×ˢ F) =
      E ×ˢ F ×ˢ Set.univ := by ext w; simp
  rw [hmarg, hrect E F G hE hF hG, hrect E F Set.univ hE hF MeasurableSet.univ]
  simp

end CausalSmith.Stat.LdpOptvalueUniformFrontier
