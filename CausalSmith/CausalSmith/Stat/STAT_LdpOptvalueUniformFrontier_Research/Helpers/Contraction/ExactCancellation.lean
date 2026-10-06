module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.MixtureProbability
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact cancellation of finite iid experiments

Expanding the finite iid input probabilities into coordinate monomials shows that
matching moments above the sample degree identify the prior predictive input law.
Applying the same sequential decision kernel preserves this equality.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [Grouping repeated coordinates turns a sample monomial into a product of powers. [](](goal). -/
-- @node: sampleMonomial_eq_coordinatePowers
lemma sampleMonomial_eq_coordinatePowers (s : Finset (Fin n)) (c : Fin n → Fin d)
    (theta : Fin d → ℝ) :
    (∏ i ∈ s, theta (c i)) = ∏ j, theta j ^ (s.filter (fun i => c i = j)).card := by
  classical
  rw [← Finset.prod_fiberwise' s c theta]
  simp

/-- Assume [the stated hnk condition](hyp:hnk) and [the stated hmom condition](hyp:hmom). [Product priors with matching moments give identical sample monomial means](goal). -/
-- @node: matchingMoments_sampleMonomial
lemma matchingMoments_sampleMonomial (nu0 nu1 : Measure ℝ)
    [IsProbabilityMeasure nu0] [IsProbabilityMeasure nu1]
    (k : ℕ) (hnk : n < k) (hmom : MatchingMoments k nu0 nu1)
    (s : Finset (Fin n)) (c : Fin n → Fin d) :
    (∫ theta, ∏ i ∈ s, theta (c i) ∂productPrior d nu0) =
      ∫ theta, ∏ i ∈ s, theta (c i) ∂productPrior d nu1 := by
  simp_rw [sampleMonomial_eq_coordinatePowers]
  unfold productPrior
  rw [integral_fintype_prod_eq_prod (fun (j : Fin d) (x : ℝ) => x ^ (s.filter (fun i => c i = j)).card),
    integral_fintype_prod_eq_prod (fun (j : Fin d) (x : ℝ) => x ^ (s.filter (fun i => c i = j)).card)]
  apply Finset.prod_congr rfl
  intro j _
  apply hmom
  have hcard : (s.filter (fun i => c i = j)).card ≤ n :=
    (Finset.card_filter_le _ _).trans (by simpa using Finset.card_le_card (Finset.subset_univ s))
  omega

/-- Assume [the stated ha condition](hyp:ha) and [the stated hnu condition](hyp:hnu). [Supported sample monomials are integrable without an extra moment assumption](goal). -/
-- @node: integrable_sampleMonomial
lemma integrable_sampleMonomial (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu)
    (s : Finset (Fin n)) (c : Fin n → Fin d) :
    Integrable (fun theta => ∏ i ∈ s, theta (c i)) (productPrior d nu) := by
  letI := hnu.1
  haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
  apply Integrable.of_bound
    ((Finset.measurable_prod s (fun i _ => measurable_pi_apply (c i))).aestronglyMeasurable) 1
  filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    (∏ i ∈ s, |theta (c i)|) ≤ ∏ _i ∈ s, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _; exact abs_nonneg _
      · intro i _
        have hi := htheta (c i)
        exact (abs_le.mpr hi).trans (by norm_num)
    _ = 1 := by simp

/-- Assume [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hnk condition](hyp:hnk), and [the stated hmom condition](hyp:hmom). [The affine sample likelihood has the same mean under moment-matched product priors](goal). -/
-- @node: matchingMoments_affineSample
lemma matchingMoments_affineSample (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hnk : n < k) (hmom : MatchingMoments k nu0 nu1)
    (c : Fin n → Fin d) (b : Fin n → ℝ) :
    (∫ theta, ∏ i, (1 + b i * theta (c i)) ∂productPrior d nu0) =
      ∫ theta, ∏ i, (1 + b i * theta (c i)) ∂productPrior d nu1 := by
  classical
  letI := hnu0.1
  letI := hnu1.1
  have hexpand (theta : Fin d → ℝ) :
      (∏ i, (1 + b i * theta (c i))) =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ s, b i) * ∏ i ∈ s, theta (c i) := by
    simp_rw [add_comm (1 : ℝ)]
    rw [Finset.prod_add]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib]
  simp_rw [hexpand]
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [integral_const_mul, integral_const_mul,
      matchingMoments_sampleMonomial nu0 nu1 k hnk hmom s c]
  · intro s _
    exact (integrable_sampleMonomial a ha nu1 hnu1 s c).const_mul _
  · intro s _
    exact (integrable_sampleMonomial a ha nu0 hnu0 s c).const_mul _

/-- Assume [the stated htheta condition](hyp:htheta). [The observed symmetric-law atom is affine in its cell contrast. [](](goal). -/
-- @node: observed_symmetric_atom_affine
lemma observed_symmetric_atom_affine (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (o : ObsRecord d) :
    (observedLaw (symmetricLaw theta)).real {o} =
      (d : ℝ)⁻¹ / 4 * (1 + obsSign o * theta o.1) := by
  rw [observedLaw, Measure.real, Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
  change (symmetricLaw theta).real (observe ⁻¹' {o}) = _
  rw [symmetricLaw_real_event theta htheta]
  rcases o with ⟨j,a,y⟩
  cases a <;> cases y <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, observe, cell, arm, outcome,
      outcome0, outcome1, potential, bernMass, obsSign, signVal]
  <;> ring

/-- Assume [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hnk condition](hyp:hnk), and [the stated hmom condition](hyp:hmom). [Moment matching identifies the mean real mass of each iid input vector](goal). -/
-- @node: matchingMoments_iid_realMass
lemma matchingMoments_iid_realMass (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hnk : n < k) (hmom : MatchingMoments k nu0 nu1)
    (o : Fin n → ObsRecord d) :
    (∫ theta, ∏ i, (d : ℝ)⁻¹ / 4 * (1 + obsSign (o i) * theta (o i).1)
      ∂productPrior d nu0) =
      ∫ theta, ∏ i, (d : ℝ)⁻¹ / 4 * (1 + obsSign (o i) * theta (o i).1)
        ∂productPrior d nu1 := by
  simp_rw [Finset.prod_mul_distrib]
  rw [integral_const_mul, integral_const_mul,
    matchingMoments_affineSample a ha nu0 nu1 hnu0 hnu1 k hnk hmom]

/-- Assume [positive dimension](hyp:hd) and [the stated htheta condition](hyp:htheta). [The affine iid mass is nonnegative and at most one on the parameter cube](goal). -/
-- @node: iid_affineMass_range
lemma iid_affineMass_range (hd : 0 < d) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (o : Fin n → ObsRecord d) :
    (∏ i, (d : ℝ)⁻¹ / 4 * (1 + obsSign (o i) * theta (o i).1)) ∈ Set.Icc 0 1 := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  simp_rw [← observed_symmetric_atom_affine theta htheta]
  constructor
  · exact Finset.prod_nonneg (fun _ _ => measureReal_nonneg)
  · calc
      (∏ i, (observedLaw (symmetricLaw theta)).real {o i}) ≤ ∏ _i : Fin n, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => measureReal_nonneg) (fun i _ => by
          simpa using measureReal_mono (mu := observedLaw (symmetricLaw theta))
            (Set.subset_univ ({o i} : Set (ObsRecord d))))
      _ = 1 := by simp

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The affine iid mass is integrable under each supported product prior](goal). -/
-- @node: integrable_iid_affineMass
lemma integrable_iid_affineMass (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (o : Fin n → ObsRecord d) :
    Integrable (fun theta => ∏ i, (d : ℝ)⁻¹ / 4 *
      (1 + obsSign (o i) * theta (o i).1)) (productPrior d nu) := by
  letI := hnu.1
  haveI : IsProbabilityMeasure (productPrior d nu) := by unfold productPrior; infer_instance
  apply Integrable.of_bound
    ((Finset.measurable_prod Finset.univ (fun i _ => by fun_prop)).aestronglyMeasurable) 1
  filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
  have h := iid_affineMass_range hd theta htheta o
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The clipped iid input mixture's atom equals the integral of its affine mass](goal). -/
-- @node: priorPredictive_iid_atom
lemma priorPredictive_iid_atom (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (o : Fin n → ObsRecord d) :
    ((productPrior d nu).bind (fun theta => Measure.pi (fun _ : Fin n =>
      observedLaw (symmetricLaw (densityCubeClamp theta))))) {o} =
    ENNReal.ofReal (∫ theta, ∏ i, (d : ℝ)⁻¹ / 4 *
      (1 + obsSign (o i) * theta (o i).1) ∂productPrior d nu) := by
  have hmeas : Measurable (fun theta : Fin d → ℝ => Measure.pi (fun _ : Fin n =>
      observedLaw (symmetricLaw (densityCubeClamp theta)))) := by
    apply measurable_finite_iid_inputLaw
    · exact (Measure.measurable_map observe (by fun_prop)).comp
        (measurable_symmetricLaw_parameter.comp measurable_densityCubeClamp)
    · intro theta
      haveI := symmetricLaw_probability _ (densityCubeClamp_mem theta) hd
      haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (densityCubeClamp theta))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      infer_instance
  rw [Measure.bind_apply (measurableSet_singleton _) hmeas.aemeasurable]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_iid_affineMass hd a ha nu hnu o)]
  · apply lintegral_congr_ae
    filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
    haveI := symmetricLaw_probability theta htheta hd
    haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    rw [densityCubeClamp_eq theta htheta, Measure.pi_singleton]
    simp_rw [← observed_symmetric_atom_affine theta htheta]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => measureReal_nonneg)]
    apply Finset.prod_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (measure_ne_top (observedLaw (symmetricLaw theta)) {o i})).symm
  · filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
    exact (iid_affineMass_range hd theta htheta o).1

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hnk condition](hyp:hnk), and [the stated hmom condition](hyp:hmom). [Matching moments through the sample degree identify the entire finite input mixture](goal). -/
-- @node: matchingMoments_iid_inputLaw
lemma matchingMoments_iid_inputLaw (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hnk : n < k) (hmom : MatchingMoments k nu0 nu1) :
    (productPrior d nu0).bind (fun theta => Measure.pi (fun _ : Fin n =>
      observedLaw (symmetricLaw (densityCubeClamp theta)))) =
    (productPrior d nu1).bind (fun theta => Measure.pi (fun _ : Fin n =>
      observedLaw (symmetricLaw (densityCubeClamp theta)))) := by
  apply Measure.ext_of_singleton
  intro o
  rw [priorPredictive_iid_atom hd a ha nu0 hnu0, priorPredictive_iid_atom hd a ha nu1 hnu1,
    matchingMoments_iid_realMass a ha nu0 nu1 hnu0 hnu1 k hnk hmom]

/-- Assume [measurability of rows](hyp:hrows) and [measurability of f](hyp:hf). [Mapping the output of a measurable mixture commutes with mixing its rows](goal). -/
-- @node: map_bind_measurable_rows
lemma map_bind_measurable_rows {I Z W : Type} [MeasurableSpace I]
    [MeasurableSpace Z] [MeasurableSpace W] (mu : Measure I) (rows : I → Measure Z)
    (hrows : Measurable rows) (f : Z → W) (hf : Measurable f) :
    (mu.bind rows).map f = mu.bind (fun i => (rows i).map f) := by
  have hm : Measurable (fun i => (rows i).map f) :=
    (Measure.measurable_map f hf).comp hrows
  ext E hE
  rw [Measure.map_apply hf hE, Measure.bind_apply (hf hE) hrows.aemeasurable,
    Measure.bind_apply hE hm.aemeasurable]
  simp_rw [Measure.map_apply hf hE]

/-- [Integrate the independent public seed and analyst coin after fixing the iid input vector](goal). -/
-- @node: canonicalDecisionLaw_input_bind
lemma canonicalDecisionLaw_input_bind (Q : LocalProtocol n (ObsRecord d))
    (p : Measure (ObsRecord d)) [IsProbabilityMeasure p] :
    canonicalDecisionLaw Q p =
      (Measure.pi (fun _ : Fin n => p)).bind (fun o =>
        (Q.seedLaw.prod uniform01).bind (fun ru =>
          (fixedTranscriptLaw Q o ru.1).map (fun z => (z,ru.1,ru.2)))) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hrows (o : Fin n → ObsRecord d) : Measurable (fun ru : Q.Seed × ℝ =>
      (fixedTranscriptLaw Q o ru.1).map (fun z => (z,ru.1,ru.2))) :=
    (measurable_protocol_decisionRows Q).comp
      (show Measurable (fun ru : Q.Seed × ℝ => (o,ru)) by fun_prop)
  unfold canonicalDecisionLaw
  ext E hE
  have hmeas := (Measure.measurable_coe hE).comp (measurable_protocol_decisionRows Q)
  simp only [Function.comp_def] at hmeas
  rw [Measure.bind_apply hE (measurable_protocol_decisionRows Q).aemeasurable,
    lintegral_prod _ hmeas.aemeasurable,
    Measure.bind_apply hE (measurable_of_finite _).aemeasurable]
  apply lintegral_congr
  intro o
  rw [Measure.bind_apply hE (hrows o).aemeasurable]

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hnk condition](hyp:hnk), and [the stated hmom condition](hyp:hmom). [Exact input cancellation survives arbitrary sequential channels and independent seeds](goal). -/
-- @node: mixtureLaw_eq_of_matching_above_sample
lemma mixtureLaw_eq_of_matching_above_sample
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hnk : n < k) (hmom : MatchingMoments k nu0 nu1) :
    mixtureLaw S Q nu0 = mixtureLaw S Q nu1 := by
  let inputRows := fun theta : Fin d → ℝ => Measure.pi (fun _ : Fin n =>
    observedLaw (symmetricLaw (densityCubeClamp theta)))
  let decisionRows := fun o : Fin n → ObsRecord d =>
    (Q.seedLaw.prod uniform01).bind (fun ru =>
      (fixedTranscriptLaw Q o ru.1).map (fun z => (z,ru.1,ru.2)))
  let seedRows := fun o : Fin n → ObsRecord d =>
    (decisionRows o).map (fun w => (w.2.1,w.1))
  have hinput : Measurable inputRows := by
    apply measurable_finite_iid_inputLaw
    · exact (Measure.measurable_map observe (by fun_prop)).comp
        (measurable_symmetricLaw_parameter.comp measurable_densityCubeClamp)
    · intro theta
      haveI := symmetricLaw_probability _ (densityCubeClamp_mem theta) hd
      haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (densityCubeClamp theta))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      infer_instance
  have hdecision : Measurable decisionRows := measurable_of_finite _
  have hseed : Measurable seedRows := measurable_of_finite _
  have hcanonical (theta : Fin d → ℝ) :
      (canonicalDecisionLaw Q (observedLaw (symmetricLaw (densityCubeClamp theta)))).map
          (fun w => (w.2.1,w.1)) = (inputRows theta).bind seedRows := by
    haveI := symmetricLaw_probability _ (densityCubeClamp_mem theta) hd
    haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (densityCubeClamp theta))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    rw [canonicalDecisionLaw_input_bind]
    exact map_bind_measurable_rows _ decisionRows hdecision _ (by fun_prop)
  have hmixture (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
      mixtureLaw S Q nu = ((productPrior d nu).bind inputRows).bind seedRows := by
    rw [Measure.bind_bind hinput.aemeasurable hseed.aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
    rw [← hcanonical]
    unfold seedTranscriptLaw
    rw [clipped_canonicalDecisionLaw_eq S hIID hRandom Q hd theta htheta]
  rw [hmixture nu0 hnu0, hmixture nu1 hnu1]
  rw [show (productPrior d nu0).bind inputRows = (productPrior d nu1).bind inputRows from
    matchingMoments_iid_inputLaw hd a ha nu0 nu1 hnu0 hnu1 k hnk hmom]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
