module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.ExactCancellation
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.MixtureProbability

/-!
# Public-seed disintegration of supported transcript mixtures

The sampling atoms identify the joint seed/transcript law with the fixed-seed
experiment integrated against the same independent public-seed law. Supported
product priors can then be integrated before the public seed.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [Appending the public seed to the clipped conditional experiment is jointly measurable](goal) when [the record dimension is positive](hyp:hd). -/
-- @node: measurable_clipped_seedTranscriptRows
@[fun_prop] lemma measurable_clipped_seedTranscriptRows
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) :
    Measurable (fun w : (Fin d → ℝ) × Q.Seed =>
      (conditionalTranscriptLaw Q (densityCubeClamp w.1) w.2).map
        (fun z => (w.2,z))) := by
  let κ : Kernel ((Fin d → ℝ) × Q.Seed) (ProtocolTranscript Q) :=
    ⟨fun w => conditionalTranscriptLaw Q (densityCubeClamp w.1) w.2,
      measurable_conditionalTranscriptLaw_clipped Q hd⟩
  haveI : IsMarkovKernel κ := ⟨fun w =>
    conditionalTranscriptLaw_probability Q _ (densityCubeClamp_mem w.1) hd w.2⟩
  let η : Kernel (((Fin d → ℝ) × Q.Seed) × ProtocolTranscript Q)
      (Q.Seed × ProtocolTranscript Q) :=
    Kernel.deterministic (fun w => (w.1.2,w.2)) (by fun_prop)
  have heq : (fun w : (Fin d → ℝ) × Q.Seed =>
      (conditionalTranscriptLaw Q (densityCubeClamp w.1) w.2).map (fun z => (w.2,z))) =
      ((κ ⊗ₖ η).map Prod.snd) := by
    funext w
    rw [Kernel.map_apply _ measurable_snd]
    ext E hE
    rw [Measure.map_apply (by fun_prop) hE,
      Measure.map_apply measurable_snd hE, Kernel.compProd_apply (measurable_snd hE)]
    simp only [η, Kernel.deterministic_apply]
    change _ = ∫⁻ z, (Measure.dirac (w.2,z)) E ∂κ w
    simp only [Measure.dirac_apply' _ hE]
    change _ = ∫⁻ z, Set.indicator ((fun z => (w.2,z)) ⁻¹' E) 1 z ∂κ w
    rw [lintegral_indicator
      ((show Measurable (fun z : ProtocolTranscript Q => (w.2,z)) by fun_prop) hE)]
    simp [κ]
  rw [heq]
  exact Kernel.measurable _

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), and [the stated htheta condition](hyp:htheta). [The sampling assumptions give the common-seed representation at every cube parameter](goal). -/
-- @node: seedTranscriptLaw_conditional_bind
lemma seedTranscriptLaw_conditional_bind
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
    seedTranscriptLaw S Q (symmetricLaw theta) =
      Q.seedLaw.bind (fun r => (conditionalTranscriptLaw Q theta r).map (fun z => (r,z))) := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI := sampling_decisionLaw_probability S hIID hRandom Q _
    (symmetricLaw_causalModel theta htheta hd)
  haveI : IsProbabilityMeasure (seedTranscriptLaw S Q (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hrows : Measurable (fun r : Q.Seed =>
      (conditionalTranscriptLaw Q theta r).map (fun z => (r,z))) := by
    simpa only [Function.comp_def, densityCubeClamp_eq theta htheta] using
      (measurable_clipped_seedTranscriptRows Q hd).comp
        (show Measurable (fun r : Q.Seed => (theta,r)) by fun_prop)
  apply Measure.ext_prod
  intro F E hF hE
  rw [seedTranscriptLaw, Measure.map_apply (by fun_prop) (hF.prod hE)]
  have hpre : (fun w : DecisionSpace Q => (w.2.1,w.1)) ⁻¹' (F ×ˢ E) =
      E ×ˢ F ×ˢ Set.univ := by ext w; simp [and_comm]
  rw [hpre, decisionLaw, iid_sampling_inputLaw S hIID hRandom Q _
    (symmetricLaw_causalModel theta htheta hd),
    product_decisionRows_rectangle Q _ E F Set.univ hE hF MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  rw [Measure.bind_apply (hF.prod hE) hrows.aemeasurable]
  have hr (r : Q.Seed) :
      ((conditionalTranscriptLaw Q theta r).map (fun z => (r,z))) (F ×ˢ E) =
      F.indicator (fun r => conditionalTranscriptLaw Q theta r E) r := by
    rw [Measure.map_apply (by fun_prop) (hF.prod hE)]
    by_cases h : r ∈ F
    · simp [h, Set.preimage, Set.indicator_of_mem]
    · simp [h, Set.preimage, Set.indicator_of_notMem]
  simp_rw [hr]
  have hm : Measurable (fun w : (Fin n → ObsRecord d) × Q.Seed =>
      F.indicator (fun r => fixedTranscriptLaw Q w.1 r E) w.2) :=
    ((Measure.measurable_coe hE).comp (measurable_fixedTranscriptLaw Q)).indicator
      (measurable_snd hF)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro r
  by_cases h : r ∈ F
  · simp only [Set.indicator_of_mem h]
    rw [conditionalTranscriptLaw, Measure.bind_apply hE
      (show Measurable (fun o => fixedTranscriptLaw Q o r) by fun_prop).aemeasurable]
  · simp [h]

/-- Assume [measurability of rows](hyp:hrows). [Jointly measurable measure rows remain measurable after integrating one independent index](goal). -/
-- @node: measurable_bind_product_rows
lemma measurable_bind_product_rows {A B Z : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Z] (nu : Measure B) [SFinite nu]
    (rows : A × B → Measure Z) (hrows : Measurable rows) :
    Measurable (fun a => nu.bind (fun b => rows (a,b))) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hsection (a : A) : Measurable (fun b => rows (a,b)) :=
    hrows.comp (by fun_prop)
  simp_rw [Measure.bind_apply hE (hsection _).aemeasurable]
  exact ((Measure.measurable_coe hE).comp hrows).lintegral_prod_right'

/-- Assume [measurability of rows](hyp:hrows). [Independent mixing indices commute for jointly measurable measure rows](goal). -/
-- @node: bind_product_rows_swap
lemma bind_product_rows_swap {A B Z : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Z] (mu : Measure A) (nu : Measure B)
    [SFinite mu] [SFinite nu] (rows : A × B → Measure Z) (hrows : Measurable rows) :
    mu.bind (fun a => nu.bind (fun b => rows (a,b))) =
      nu.bind (fun b => mu.bind (fun a => rows (a,b))) := by
  have hleft := measurable_bind_product_rows nu rows hrows
  have hright := measurable_bind_product_rows mu (fun w : B × A => rows (w.2,w.1))
    (hrows.comp measurable_swap)
  ext E hE
  rw [Measure.bind_apply hE hleft.aemeasurable,
    Measure.bind_apply hE hright.aemeasurable]
  have ha (a : A) : Measurable (fun b => rows (a,b)) := hrows.comp (by fun_prop)
  have hb (b : B) : Measurable (fun a => rows (a,b)) := hrows.comp (by fun_prop)
  simp_rw [Measure.bind_apply hE (ha _).aemeasurable,
    Measure.bind_apply hE (hb _).aemeasurable]
  exact lintegral_lintegral_swap ((Measure.measurable_coe hE).comp hrows).aemeasurable

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Supported product priors mix conditionally before the independent public seed](goal). -/
-- @node: mixtureLaw_common_seed_bind
lemma mixtureLaw_common_seed_bind
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (a : ℝ) (ha : a ≤ (1 / 2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    mixtureLaw S Q nu = Q.seedLaw.bind (fun r =>
      (productPrior d nu).bind (fun theta =>
        (conditionalTranscriptLaw Q (densityCubeClamp theta) r).map (fun z => (r,z)))) := by
  letI := hnu.1
  haveI : IsProbabilityMeasure (productPrior d nu) := by
    unfold productPrior
    infer_instance
  rw [← bind_product_rows_swap (productPrior d nu) Q.seedLaw _
    (measurable_clipped_seedTranscriptRows Q hd)]
  apply Measure.bind_congr_right
  filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
  rw [densityCubeClamp_eq theta htheta]
  exact seedTranscriptLaw_conditional_bind S hIID hRandom Q hd theta htheta

/-- Assume [measurability of rows](hyp:hrows), [the stated probability-measure property](hyp:hprob), [measurability of p](hyp:hp), [the stated hnonneg condition](hyp:hnonneg), and [the stated hdensity condition](hyp:hdensity). [A probability mixture has the prior-averaged real density against its common reference. This is the arbitrary-parameter version of the scalar-prior mixture likelihood identity](goal). -/
-- @node: probability_bind_withDensity_average
lemma probability_bind_withDensity_average {T Z : Type} [MeasurableSpace T]
    [MeasurableSpace Z] (pi : Measure T) [IsProbabilityMeasure pi]
    (mu : Measure Z) [SigmaFinite mu] (rows : T → Measure Z) (hrows : Measurable rows)
    (hprob : ∀ t, IsProbabilityMeasure (rows t)) (p : T × Z → ℝ)
    (hp : Measurable p) (hnonneg : ∀ w, 0 ≤ p w)
    (hdensity : ∀ t, rows t = mu.withDensity (fun z => ENNReal.ofReal (p (t,z)))) :
    pi.bind rows = mu.withDensity (fun z => ENNReal.ofReal (∫ t, p (t,z) ∂pi)) := by
  have hmass (t : T) : ∫⁻ z, ENNReal.ofReal (p (t,z)) ∂mu = 1 := by
    rw [← Measure.restrict_univ (μ := mu), ← withDensity_apply _ MeasurableSet.univ, ← hdensity t]
    exact (hprob t).measure_univ
  have hjoint : Integrable p (pi.prod mu) := by
    refine ⟨hp.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnonneg)).2
    rw [lintegral_prod _ hp.ennreal_ofReal.aemeasurable]
    simp_rw [hmass]
    simp
  have havg : ∀ᵐ z ∂mu,
      ENNReal.ofReal (∫ t, p (t,z) ∂pi) = ∫⁻ t, ENNReal.ofReal (p (t,z)) ∂pi := by
    filter_upwards [hjoint.prod_left_ae] with z hz
    exact ofReal_integral_eq_lintegral_ofReal hz (ae_of_all _ (fun t => hnonneg (t,z)))
  ext E hE
  rw [Measure.bind_apply hE hrows.aemeasurable, withDensity_apply _ hE]
  simp_rw [hdensity, withDensity_apply _ hE]
  calc
    _ = ∫⁻ z in E, ∫⁻ t, ENNReal.ofReal (p (t,z)) ∂pi ∂mu :=
      lintegral_lintegral_swap hp.ennreal_ofReal.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae havg] with z hz
      exact hz.symm

/-- Assume [positive dimension](hyp:hd), [the stated hp condition](hyp:hp), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The supported fixed-seed mixture is represented by the average of the given density version](goal). -/
-- @node: conditionalMixture_withDensity_average
lemma conditionalMixture_withDensity_average
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) (eps : ℝ)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hp : DensityCertificate Q eps p) (r : Q.Seed)
    (a : ℝ) (ha : a ≤ (1 / 2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (productPrior d nu).bind (fun theta =>
      conditionalTranscriptLaw Q (densityCubeClamp theta) r) =
      (referenceLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∫ theta, p (theta,r,z) ∂productPrior d nu)) := by
  letI := hnu.1
  haveI : IsProbabilityMeasure (productPrior d nu) := by
    unfold productPrior
    infer_instance
  have hzero : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  haveI : IsProbabilityMeasure (referenceLaw Q r) :=
    conditionalTranscriptLaw_probability Q _ hzero hd r
  have hrows : Measurable (fun theta : Fin d → ℝ =>
      conditionalTranscriptLaw Q (densityCubeClamp theta) r) := by
    simpa only [Function.comp_def] using
      (measurable_conditionalTranscriptLaw_clipped Q hd).comp
        (show Measurable (fun theta : Fin d → ℝ => (theta,r)) from
          measurable_id.prodMk measurable_const)
  have hmeas : Measurable (fun w : (Fin d → ℝ) × ProtocolTranscript Q =>
      p (densityCubeClamp w.1,r,w.2)) := by
    simpa only [Function.comp_def] using hp.1.comp
      ((measurable_densityCubeClamp.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))
  have heq := probability_bind_withDensity_average (productPrior d nu) (referenceLaw Q r)
    (fun theta : Fin d → ℝ => conditionalTranscriptLaw Q (densityCubeClamp theta) r) hrows
    (fun theta => conditionalTranscriptLaw_probability Q _ (densityCubeClamp_mem theta) hd r)
    (fun w : (Fin d → ℝ) × ProtocolTranscript Q => p (densityCubeClamp w.1,r,w.2))
    hmeas
    (fun w => (hp.2.1 _ (densityCubeClamp_mem w.1) r).1 w.2)
    (fun theta => (hp.2.1 _ (densityCubeClamp_mem theta) r).2.symm)
  refine heq.trans ?_
  congr 1
  funext z
  congr 1
  apply integral_congr_ae
  filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
  rw [densityCubeClamp_eq theta htheta]

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), [the stated hp condition](hyp:hp), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Joint seed/transcript mixtures use the same seed law and the prior-integrated conditional density, including arbitrary public seeds of law-zero mass](goal). -/
-- @node: mixtureLaw_seed_density_average
lemma mixtureLaw_seed_density_average
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) (eps : ℝ)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hp : DensityCertificate Q eps p)
    (a : ℝ) (ha : a ≤ (1 / 2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    mixtureLaw S Q nu = Q.seedLaw.bind (fun r =>
      ((referenceLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∫ theta, p (theta,r,z) ∂productPrior d nu))).map
          (fun z => (r,z))) := by
  rw [mixtureLaw_common_seed_bind S hIID hRandom Q hd a ha nu hnu]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro r
  change (productPrior d nu).bind (fun theta =>
    (conditionalTranscriptLaw Q (densityCubeClamp theta) r).map (fun z => (r,z))) =
    ((referenceLaw Q r).withDensity (fun z =>
      ENNReal.ofReal (∫ theta, p (theta,r,z) ∂productPrior d nu))).map (fun z => (r,z))
  rw [← conditionalMixture_withDensity_average Q hd eps p hp r a ha nu hnu]
  exact (map_bind_measurable_rows (productPrior d nu) _
    (by
      simpa only [Function.comp_def] using
        (measurable_conditionalTranscriptLaw_clipped Q hd).comp
          (show Measurable (fun theta : Fin d → ℝ => (theta,r)) from
            measurable_id.prodMk measurable_const)) _
    (by fun_prop)).symm

end CausalSmith.Stat.LdpOptvalueUniformFrontier
