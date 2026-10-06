module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.ContractionCalibration
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoPoint

/-!
# Causal product priors in the measurable decision experiment

Supported symmetric-law priors retain the transcript contraction bound after
passing to law space. The measurable completion lets the separated-mixture
reduction apply to every sampling scheme satisfying iid and independent coins.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [The finite causal model is a Borel set of population laws](goal). -/
-- @node: measurableSet_causalClass
lemma measurableSet_causalClass (d : ℕ) : MeasurableSet (causalClass d) := by
  have hm (E : Set (FullRecord d)) : Measurable (fun P : Measure (FullRecord d) => P.real E) :=
    (Measure.measurable_coe (MeasurableSet.of_discrete : MeasurableSet E)).ennreal_toReal
  have ha (a : Bool) (j : Fin d) : Measurable (fun P : Measure (FullRecord d) => armMean P a j) := by
    unfold armMean
    exact (hm _).div (hm _)
  have heq : causalClass d = {P : Measure (FullRecord d) | P Set.univ = 1} ∩
      ({P | UniformCovariates P} ∩ ({P | FairRandomization P} ∩
        ({P | Consistency P} ∩ {P | InteriorMeans P}))) := by
    ext P
    simp only [causalClass, Set.mem_setOf_eq, Set.mem_inter_iff, isProbabilityMeasure_iff]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, h.uniform, h.fair, h.consistent, h.interior⟩
    · rintro ⟨hp, hu, hf, hc, hi⟩
      exact ⟨hp, ⟨hu, hf, hc, hi⟩⟩
  rw [heq]
  refine (measurableSet_eq_fun (Measure.measurable_coe MeasurableSet.univ) measurable_const).inter
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
  · simp only [UniformCovariates, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun (hm _) measurable_const
  · simp only [FairRandomization, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun a =>
      MeasurableSet.iInter fun y0 => MeasurableSet.iInter fun y1 =>
        measurableSet_eq_fun (hm _) ((hm _).const_mul _)
  · exact measurableSet_eq_fun (hm _) measurable_const
  · simp only [InteriorMeans, Set.setOf_forall]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun j =>
      isClosed_Icc.measurableSet.preimage (ha a j)

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Supported parameter priors push forward into the unchanged causal class](goal). -/
-- @node: symmetricLaw_productPrior_support
lemma symmetricLaw_productPrior_support (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    ((productPrior d nu).map symmetricLaw) (causalClass d)ᶜ = 0 := by
  rw [Measure.map_apply measurable_symmetricLaw_parameter (measurableSet_causalClass d).compl]
  apply ae_iff.mp
  filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta ht
  exact ⟨symmetricLaw_probability theta ht hd, symmetricLaw_causalModel theta ht hd⟩

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The completed law-space decision marginal equals the parameter transcript mixture](goal). -/
-- @node: causal_prior_completed_marginal
lemma causal_prior_completed_marginal (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (((productPrior d nu).map symmetricLaw).bind (completedDecisionLaw Q)).map
        (fun w => (w.2.1,w.1)) = mixtureLaw (canonicalScheme n d) Q nu := by
  have hm : Measurable (fun theta : Fin d → ℝ => completedDecisionLaw Q (symmetricLaw theta)) :=
    (measurable_completedDecisionLaw Q).comp measurable_symmetricLaw_parameter
  have hbind : ((productPrior d nu).map symmetricLaw).bind (completedDecisionLaw Q) =
      (productPrior d nu).bind (fun theta => completedDecisionLaw Q (symmetricLaw theta)) := by
    ext E hE
    rw [Measure.bind_apply hE (measurable_completedDecisionLaw Q).aemeasurable,
      Measure.bind_apply hE hm.aemeasurable]
    exact lintegral_map ((Measure.measurable_coe hE).comp
      (measurable_completedDecisionLaw Q)) measurable_symmetricLaw_parameter
  rw [hbind, map_bind_measurable_rows _ _ hm _ (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta ht
  haveI := symmetricLaw_probability theta ht hd
  rw [completedDecisionLaw_eq_canonical]
  rfl

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hQ), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), and [the stated hmatch condition](hyp:hmatch). [Prescribed amplitude and matching degree make the causal law-space transcript mixtures at most one hundredth apart, including orders beyond the sample size](goal). -/
-- @node: causal_lawspace_resource_contraction
lemma causal_lawspace_resource_contraction (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ)
    (hQ : SequentialClass Q eps) (hAllowed : Allowed n d eps)
    (nu0 nu1 : Measure ℝ)
    (hnu0 : AmplitudePrior (frontierResources n d eps).converseAmp nu0)
    (hnu1 : AmplitudePrior (frontierResources n d eps).converseAmp nu1)
    (hmatch : MatchingMoments (frontierResources n d eps).converseDegree nu0 nu1) :
    Causalean.Stat.tvDist
      ((((productPrior d nu0).map symmetricLaw).bind (completedDecisionLaw Q)).map
        (fun w => (w.2.1,w.1)))
      ((((productPrior d nu1).map symmetricLaw).bind (completedDecisionLaw Q)).map
        (fun w => (w.2.1,w.1))) ≤ (1/100 : ℝ) := by
  have hd : 0 < d := by have := hAllowed.2.1; omega
  have ha := frontier_converse_amplitude_domain n d eps hAllowed
  rw [causal_prior_completed_marginal Q hd _ ha.2 nu0 hnu0,
    causal_prior_completed_marginal Q hd _ ha.2 nu1 hnu1]
  let k := (frontierResources n d eps).converseDegree
  have hk : 1 ≤ k := by have := frontier_converse_degree_domain n d eps hAllowed; dsimp [k]; omega
  have hcontract := (adaptive_moment_contraction hRN (canonicalScheme n d)
    canonicalScheme_iidPeople canonicalScheme_independentRandomness Q eps hQ hAllowed).2
    _ ha nu0 nu1 hnu0 hnu1 k hk hmatch
  by_cases hkn : k ≤ n
  · exact ((hcontract.1 hkn).trans (min_le_right _ _)).trans
      ((contraction_coefficient_geometric_le n d k hd (by omega) eps _
        hAllowed.2.2 ha.1.le).trans (frontier_converse_geometric_small n d eps hAllowed))
  · rw [hcontract.2.1 (by omega)]
    simpa [Causalean.Stat.tvDist] using (show (0 : ℝ) ≤ 1/100 by norm_num)

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [the stated support condition](hyp:hSupport0), [the stated support condition](hyp:hSupport1), [strict separation of the two target values](hyp:hv), [the stated concentration near the target value](hyp:hEscape0), [the stated concentration near the target value](hyp:hEscape1), and [the probability law hTV](hyp:hTV). [Law-space separated priors give the stated causal risk and honest interval bounds for every iid scheme with independent public and analyst randomness](goal). -/
-- @node: causal_separated_lawspace_decisions
lemma causal_separated_lawspace_decisions
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d))
    (pi0 pi1 : Measure (Measure (FullRecord d)))
    [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 (causalClass d)ᶜ = 0) (hSupport1 : pi1 (causalClass d)ᶜ = 0)
    (v0 v1 eta omega : ℝ) (hv : v0 < v1)
    (hEscape0 : pi0.real {P | (v1-v0)/8 < |value P-v0|} ≤ eta)
    (hEscape1 : pi1.real {P | (v1-v0)/8 < |value P-v1|} ≤ eta)
    (hTV : Causalean.Stat.tvDist
      ((pi0.bind (completedDecisionLaw Q)).map (fun w => (w.2.1,w.1)))
      ((pi1.bind (completedDecisionLaw Q)).map (fun w => (w.2.1,w.1))) ≤ omega) :
    (∀ T : Estimator Q,
      ENNReal.ofReal (9*(v1-v0)^2/128 * max 0 (1-omega-2*eta)) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
    (∀ I : IntervalDecision Q (1/4) (3/4),
      (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
      ENNReal.ofReal (3*(v1-v0)/4 * max 0 ((0.80 : ℝ)-2*eta-omega)) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          expectedLength (decisionLaw S Q P.1) I) := by
  have hEq (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      completedDecisionLaw Q P = decisionLaw S Q P := by
    haveI := hP.1
    rw [completedDecisionLaw_eq_canonical]
    unfold decisionLaw
    rw [iid_sampling_inputLaw S hIID hRandom Q P hP.2]
    rfl
  have hProb (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      IsProbabilityMeasure (completedDecisionLaw Q P) := by
    haveI := hP.1
    rw [hEq P hP]
    exact sampling_decisionLaw_probability S hIID hRandom Q P hP.2
  have hProduct (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      completedDecisionLaw Q P =
        (((completedDecisionLaw Q P).map (fun w => (w.1,w.2.1))).prod uniform01).map
          (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) := by
    haveI := hP.1
    rw [hEq P hP]
    exact sampling_decisionLaw_randomizer S hIID hRandom Q P hP.2
  have hsep := separated_value_mixtures_generic Q (causalClass d) value
    (completedDecisionLaw Q) hProduct hProb pi0 pi1 hSupport0 hSupport1
    measurable_causal_value (measurable_completedDecisionLaw Q)
    v0 v1 eta omega hv hEscape0 hEscape1 hTV (1/4) (3/4)
  constructor
  · intro T
    convert hsep.1 T using 1
    congr 1
    funext P
    rw [hEq P.1 P.2]
  · intro I hCov
    have hCov' : ∀ P ∈ causalClass d, (0.90 : ℝ) ≤
        coverage (completedDecisionLaw Q P) I (value P) := by
      intro P hP
      rw [hEq P hP]
      exact hCov P hP
    convert hsep.2 I hCov' using 1
    congr 1
    funext P
    rw [hEq P.1 P.2]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
