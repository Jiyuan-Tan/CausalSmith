module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.PriorTelescoping
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.ExactCancellation
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.MixtureProbability
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.JointSeed
public import Causalean.Stat.Minimax.Scheffe

/-!
# Helpers/Contraction/Mixture

Finite original-record private value frontiers: Helpers/Contraction/Mixture.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ}
/-- Assume [measurability of p](hyp:hp), [measurability of q](hyp:hq), [the stated hp0 condition](hyp:hp0), [the stated hq0 condition](hyp:hq0), [the stated hmu condition](hyp:hmu), and [the stated hnu condition](hyp:hnu). [Probability densities against a common reference obey the half-L1 TV bound](goal). -/
-- @node: probability_density_tv_le_half_L1
lemma probability_density_tv_le_half_L1 {Z : Type*} [MeasurableSpace Z]
    (mu nu xi : Measure Z) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure xi] (p q : Z → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ z, 0 ≤ p z) (hq0 : ∀ z, 0 ≤ q z)
    (hmu : mu = xi.withDensity (fun z => ENNReal.ofReal (p z)))
    (hnu : nu = xi.withDensity (fun z => ENNReal.ofReal (q z))) :
    Causalean.Stat.tvDist mu nu ≤ (1/2 : ℝ) * ∫ z, |p z - q z| ∂xi := by
  have hacp : mu ≪ xi := hmu ▸ withDensity_absolutelyContinuous xi _
  have hacq : nu ≪ xi := hnu ▸ withDensity_absolutelyContinuous xi _
  have hrp : (fun z => (mu.rnDeriv xi z).toReal) =ᵐ[xi] p := by
    have h := hmu ▸ Measure.rnDeriv_withDensity xi hp.ennreal_ofReal
    filter_upwards [h] with z hz
    rw [hz, ENNReal.toReal_ofReal (hp0 z)]
  have hrq : (fun z => (nu.rnDeriv xi z).toReal) =ᵐ[xi] q := by
    have h := hnu ▸ Measure.rnDeriv_withDensity xi hq.ennreal_ofReal
    filter_upwards [h] with z hz
    rw [hz, ENNReal.toReal_ofReal (hq0 z)]
  have hpi : Integrable p xi := Measure.integrable_toReal_rnDeriv.congr hrp
  have hqi : Integrable q xi := Measure.integrable_toReal_rnDeriv.congr hrq
  have hp1 : ∫ z, p z ∂xi = 1 := by
    rw [← integral_congr_ae hrp, Measure.integral_toReal_rnDeriv hacp]; simp
  have hq1 : ∫ z, q z ∂xi = 1 := by
    rw [← integral_congr_ae hrq, Measure.integral_toReal_rnDeriv hacq]; simp
  refine ciSup_le fun E => ?_
  have hgap : mu.real E.1 - nu.real E.1 = ∫ z in E.1, (p z - q z) ∂xi := by
    rw [← Measure.setIntegral_toReal_rnDeriv hacp,
      ← Measure.setIntegral_toReal_rnDeriv hacq,
      integral_congr_ae (ae_restrict_of_ae hrp),
      integral_congr_ae (ae_restrict_of_ae hrq),
      integral_sub hpi.integrableOn hqi.integrableOn]
  rw [hgap]
  exact Causalean.Stat.abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
    (hpi.sub hqi) (by change (∫ z, p z - q z ∂xi) = 0; rw [integral_sub hpi hqi, hp1, hq1, sub_self]) E.2

/-- Assume [measurability of m](hyp:hm), [the stated probability-measure property](hyp:hprob), and [the set hE](hyp:hE). [Real event masses of measurable probability mixtures are averages of row masses](goal). -/
-- @node: probability_bind_real_event
lemma probability_bind_real_event {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (mu : Measure A) [IsProbabilityMeasure mu] (rows : A → Measure Z)
    (hm : Measurable rows) (hprob : ∀ a, IsProbabilityMeasure (rows a))
    (E : Set Z) (hE : MeasurableSet E) :
    (mu.bind rows).real E = ∫ a, (rows a).real E ∂mu := by
  letI : ∀ a, IsProbabilityMeasure (rows a) := hprob
  rw [measureReal_def, Measure.bind_apply hE hm.aemeasurable]
  exact (integral_toReal
    (((Measure.measurable_coe hE).comp hm).aemeasurable)
    (ae_of_all _ (fun a => measure_lt_top (rows a) E))).symm

/-- Assume [measurability of m0](hyp:hm0), [measurability of m1](hyp:hm1), [the stated probability-measure property](hyp:hprob0), [the stated probability-measure property](hyp:hprob1), and [the stated b condition](hyp:hB). [A uniform rowwise TV bound survives mixing with the same independent seed law](goal). -/
-- @node: probability_bind_tv_le_constant
lemma probability_bind_tv_le_constant {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (mu : Measure A) [IsProbabilityMeasure mu] (rows0 rows1 : A → Measure Z)
    (hm0 : Measurable rows0) (hm1 : Measurable rows1)
    (hprob0 : ∀ a, IsProbabilityMeasure (rows0 a))
    (hprob1 : ∀ a, IsProbabilityMeasure (rows1 a))
    (B : ℝ) (hB : ∀ a, Causalean.Stat.tvDist (rows0 a) (rows1 a) ≤ B) :
    Causalean.Stat.tvDist (mu.bind rows0) (mu.bind rows1) ≤ B := by
  letI : ∀ a, IsProbabilityMeasure (rows0 a) := hprob0
  letI : ∀ a, IsProbabilityMeasure (rows1 a) := hprob1
  refine ciSup_le fun E => ?_
  have hi0 : Integrable (fun a => (rows0 a).real E.1) mu :=
    Integrable.of_bound (((Measure.measurable_coe E.2).comp hm0).ennreal_toReal.aestronglyMeasurable)
      1 (ae_of_all _ fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hi1 : Integrable (fun a => (rows1 a).real E.1) mu :=
    Integrable.of_bound (((Measure.measurable_coe E.2).comp hm1).ennreal_toReal.aestronglyMeasurable)
      1 (ae_of_all _ fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  rw [probability_bind_real_event mu rows0 hm0 hprob0 E.1 E.2,
    probability_bind_real_event mu rows1 hm1 hprob1 E.1 E.2,
    ← integral_sub hi0 hi1]
  calc
    _ ≤ ∫ a, |(rows0 a).real E.1 - (rows1 a).real E.1| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ _a, B ∂mu := integral_mono_ae (hi0.sub hi1).abs (integrable_const B)
      (ae_of_all _ fun a => (Causalean.Stat.abs_measureReal_sub_le_tvDist E.2).trans (hB a))
    _ = B := by simp

/-- Assume [measurability of f](hyp:hf). [Applying a measurable transcript map cannot increase TV](goal). -/
-- @node: probability_tv_map_le
lemma probability_tv_map_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : X → Y) (hf : Measurable f) :
    Causalean.Stat.tvDist (mu.map f) (nu.map f) ≤ Causalean.Stat.tvDist mu nu := by
  refine ciSup_le fun E => ?_
  simp only [measureReal_def, Measure.map_apply hf E.2]
  exact Causalean.Stat.abs_measureReal_sub_le_tvDist (E.2.preimage hf)

/-- Assume [the stated hp condition](hyp:hp), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The supported conditional mixture has a measurable, nonnegative real density](goal). -/
-- @node: conditionalMixture_density_measurable_nonneg
lemma conditionalMixture_density_measurable_nonneg
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hp : DensityCertificate Q eps p) (r : Q.Seed)
    (a : ℝ) (ha : a ≤ (1/2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    Measurable (fun z => ∫ theta, p (theta,r,z) ∂productPrior d nu) ∧
      ∀ z, 0 ≤ ∫ theta, p (theta,r,z) ∂productPrior d nu := by
  letI := hnu.1
  haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
  constructor
  · exact (hp.1.comp (show Measurable
      (fun w : (Fin d → ℝ) × ProtocolTranscript Q => (w.1,r,w.2)) by fun_prop)
      ).stronglyMeasurable.integral_prod_left' (μ := productPrior d nu) |>.measurable
  · intro z
    apply integral_nonneg_of_ae
    filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
    exact (hp.2.1 theta htheta r).1 z

/-- Assume [positive dimension](hyp:hd), [the stated hp condition](hyp:hp), [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), and [the stated hnu1 condition](hyp:hnu1). [Fixed-seed supported transcript mixtures obey their density L1 bound](goal). -/
-- @node: conditionalMixture_tv_le_half_L1
lemma conditionalMixture_tv_le_half_L1
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) (eps : ℝ)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hp : DensityCertificate Q eps p) (r : Q.Seed)
    (a : ℝ) (ha : a ≤ (1/2 : ℝ)) (nu0 nu1 : Measure ℝ)
    (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1) :
    Causalean.Stat.tvDist
      ((productPrior d nu0).bind (fun theta => conditionalTranscriptLaw Q (densityCubeClamp theta) r))
      ((productPrior d nu1).bind (fun theta => conditionalTranscriptLaw Q (densityCubeClamp theta) r)) ≤
        (1/2 : ℝ) * ∫ z, |(∫ theta, p (theta,r,z) ∂productPrior d nu0) -
          ∫ theta, p (theta,r,z) ∂productPrior d nu1| ∂referenceLaw Q r := by
  have hm : Measurable (fun theta => conditionalTranscriptLaw Q (densityCubeClamp theta) r) := by
    simpa only [Function.comp_def] using (measurable_conditionalTranscriptLaw_clipped Q hd).comp
      (show Measurable (fun theta : Fin d → ℝ => (theta,r)) by fun_prop)
  have hprob (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
      IsProbabilityMeasure ((productPrior d nu).bind
        (fun theta => conditionalTranscriptLaw Q (densityCubeClamp theta) r)) := by
    letI := hnu.1
    haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
    exact isProbabilityMeasure_bind hm.aemeasurable (ae_of_all _ fun theta =>
      conditionalTranscriptLaw_probability Q _ (densityCubeClamp_mem theta) hd r)
  letI := hprob nu0 hnu0
  letI := hprob nu1 hnu1
  have hzero : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  haveI : IsProbabilityMeasure (referenceLaw Q r) :=
    conditionalTranscriptLaw_probability Q _ hzero hd r
  obtain ⟨hm0, hn0⟩ := conditionalMixture_density_measurable_nonneg Q eps p hp r a ha nu0 hnu0
  obtain ⟨hm1, hn1⟩ := conditionalMixture_density_measurable_nonneg Q eps p hp r a ha nu1 hnu1
  exact probability_density_tv_le_half_L1 _ _ _ _ _ hm0 hm1 hn0 hn1
    (conditionalMixture_withDensity_average Q hd eps p hp r a ha nu0 hnu0)
    (conditionalMixture_withDensity_average Q hd eps p hp r a ha nu1 hnu1)

set_option maxHeartbeats 1000000 in
-- @node: lem:adaptive-moment-contraction
/-- [Adaptive higher-order transcript contraction holds for arbitrary public seeds and randomized tests](goal) when [the measurable-kernel Radon–Nikodym property](hyp:hRN_of_gate), [iid sampling](hyp:hIID), [independent randomness](hyp:hRandom), [sequential ε-local privacy](hyp:hQ), and [the admissible parameter regime](hyp:hAllowed) hold. -/
lemma adaptive_moment_contraction (hRN_of_gate : MeasurableKernelRadonNikodym)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) :
    (∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      DensityCertificate Q eps p) ∧
    (∀ (a : ℝ), a ∈ Set.Ioc 0 (1/2 : ℝ) → -- @realizes \alpha(0<amplitude≤1/2)
      ∀ (nu0 nu1 : Measure ℝ), AmplitudePrior a nu0 → AmplitudePrior a nu1 →
      ∀ k : ℕ, 1 ≤ k → MatchingMoments k nu0 nu1 →
        (k ≤ n → Causalean.Stat.tvDist (mixtureLaw S Q nu0) (mixtureLaw S Q nu1) ≤
          min 1 (d * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k)) ∧
        (n < k → mixtureLaw S Q nu0 = mixtureLaw S Q nu1) ∧
        (∀ f : Q.Seed × ProtocolTranscript Q → ℝ, Measurable f →
          (∀ w, f w ∈ Set.Icc 0 1) →
          |(∫ w, f w ∂(mixtureLaw S Q nu0)) - (∫ w, f w ∂(mixtureLaw S Q nu1))| ≤
            Causalean.Stat.tvDist (mixtureLaw S Q nu0) (mixtureLaw S Q nu1))) := by
  obtain ⟨p, hp, hProduct⟩ := density_product_matching_of_gate hRN_of_gate Q eps hQ hAllowed
  constructor
  · exact ⟨p, hp⟩
  · intro a ha nu0 nu1 hnu0 hnu1 k hk hmom
    refine ⟨?_, ?_, ?_⟩
    · intro hkn
      have hL1 (r : Q.Seed) := hProduct r a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom
      have hd : 0 < d := by have := hAllowed.2.1; omega
      let m (nu : Measure ℝ) (r : Q.Seed) := (productPrior d nu).bind
        (fun theta => conditionalTranscriptLaw Q (densityCubeClamp theta) r)
      let rows (nu : Measure ℝ) (r : Q.Seed) := (productPrior d nu).bind
        (fun theta => (conditionalTranscriptLaw Q (densityCubeClamp theta) r).map (fun z => (r,z)))
      have hm (r : Q.Seed) : Measurable
          (fun theta => conditionalTranscriptLaw Q (densityCubeClamp theta) r) := by
        simpa only [Function.comp_def] using (measurable_conditionalTranscriptLaw_clipped Q hd).comp
          (show Measurable (fun theta : Fin d → ℝ => (theta,r)) by fun_prop)
      have hprob (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (r : Q.Seed) :
          IsProbabilityMeasure (m nu r) := by
        letI := hnu.1
        haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
        exact isProbabilityMeasure_bind (hm r).aemeasurable (ae_of_all _ fun theta =>
          conditionalTranscriptLaw_probability Q _ (densityCubeClamp_mem theta) hd r)
      have hmap (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (r : Q.Seed) :
          rows nu r = (m nu r).map (fun z => (r,z)) := by
        letI := hnu.1
        haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
        exact (map_bind_measurable_rows (productPrior d nu) _ (hm r) _ (by fun_prop)).symm
      have hrprob (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (r : Q.Seed) :
          IsProbabilityMeasure (rows nu r) := by
        rw [hmap nu hnu r]
        letI := hprob nu hnu r
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      have hrmeas (nu : Measure ℝ) (hnu : AmplitudePrior a nu) : Measurable (rows nu) := by
        letI := hnu.1
        haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
        exact measurable_bind_product_rows (productPrior d nu)
          (fun w : Q.Seed × (Fin d → ℝ) =>
            (conditionalTranscriptLaw Q (densityCubeClamp w.2) w.1).map (fun z => (w.1,z)))
          ((measurable_clipped_seedTranscriptRows Q hd).comp measurable_swap)
      have hrowbound (r : Q.Seed) : Causalean.Stat.tvDist (rows nu0 r) (rows nu1 r) ≤
          d * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
        rw [hmap nu0 hnu0 r, hmap nu1 hnu1 r]
        letI := hprob nu0 hnu0 r
        letI := hprob nu1 hnu1 r
        calc
          _ ≤ Causalean.Stat.tvDist (m nu0 r) (m nu1 r) := probability_tv_map_le _ _ _ (by fun_prop)
          _ ≤ (1/2 : ℝ) * ∫ z, |(∫ theta, p (theta,r,z) ∂productPrior d nu0) -
              ∫ theta, p (theta,r,z) ∂productPrior d nu1| ∂referenceLaw Q r :=
            conditionalMixture_tv_le_half_L1 Q hd eps p hp r a ha.2 nu0 nu1 hnu0 hnu1
          _ ≤ _ := by nlinarith [hL1 r]
      haveI := mixtureLaw_probability S hIID hRandom Q hd a ha.2 nu0 hnu0
      haveI := mixtureLaw_probability S hIID hRandom Q hd a ha.2 nu1 hnu1
      apply le_min (Causalean.Stat.tvDist_le_one)
      rw [mixtureLaw_common_seed_bind S hIID hRandom Q hd a ha.2 nu0 hnu0,
        mixtureLaw_common_seed_bind S hIID hRandom Q hd a ha.2 nu1 hnu1]
      exact probability_bind_tv_le_constant Q.seedLaw (rows nu0) (rows nu1)
        (hrmeas nu0 hnu0) (hrmeas nu1 hnu1) (hrprob nu0 hnu0) (hrprob nu1 hnu1) _ hrowbound
    · intro hnk
      exact mixtureLaw_eq_of_matching_above_sample S hIID hRandom Q
        (by have := hAllowed.2.1; omega) a ha.2 nu0 nu1 hnu0 hnu1 k hnk hmom
    · intro f hf hrange
      exact mixtureLaw_bounded_test S hIID hRandom Q (by have := hAllowed.2.1; omega)
        a ha.2 nu0 nu1 hnu0 hnu1 f hf hrange


end CausalSmith.Stat.LdpOptvalueUniformFrontier
