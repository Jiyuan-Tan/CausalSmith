module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Density
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.DecisionSampling

/-!
# Probability laws for supported transcript mixtures

Clipped measurable experiment versions agree with the original sampling scheme on the
parameter cube. Supported product priors therefore induce probability mixtures, to which
the bounded-statistic total-variation inequality applies.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [Finite iid input laws vary measurably with their atom probabilities](goal) when [the one-sample laws vary measurably](hyp:hmu) and [each such law is finite](hyp:hfin). -/
-- @node: measurable_finite_iid_inputLaw
@[fun_prop] lemma measurable_finite_iid_inputLaw {H I : Type}
    [MeasurableSpace H] [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : H → Measure I) (hmu : Measurable mu) (hfin : ∀ h, IsFiniteMeasure (mu h)) :
    Measurable (fun h => Measure.pi (fun _ : Fin n => mu h)) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hexpand (h : H) : (Measure.pi (fun _ : Fin n => mu h)) E =
      ∑ o : Fin n → I, E.indicator (fun o => ∏ i, mu h {o i}) o := by
    letI := hfin h
    rw [← Measure.tsum_indicator_apply_singleton _ E hE, tsum_fintype]
    simp only [Measure.pi_singleton]
  simp_rw [hexpand]
  apply Finset.measurable_sum
  intro o _
  by_cases ho : o ∈ E
  · simp only [Set.indicator_of_mem ho]
    exact Finset.measurable_prod _ (fun i _ =>
      (Measure.measurable_coe (measurableSet_singleton _)).comp hmu)
  · simp only [Set.indicator_of_notMem ho]
    exact measurable_const

/-- [Clipping gives a globally measurable canonical decision experiment](goal) when [the record dimension is positive](hyp:hd). -/
-- @node: measurable_clipped_canonicalDecisionLaw
@[fun_prop] lemma measurable_clipped_canonicalDecisionLaw
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) :
    Measurable (fun theta : Fin d → ℝ =>
      canonicalDecisionLaw Q (observedLaw (symmetricLaw (densityCubeClamp theta)))) := by
  have hobs : Measurable (fun theta : Fin d → ℝ =>
      observedLaw (symmetricLaw (densityCubeClamp theta))) := by
    exact (Measure.measurable_map observe (by fun_prop)).comp
      (measurable_symmetricLaw_parameter.comp measurable_densityCubeClamp)
  have hprob (theta : Fin d → ℝ) :
      IsProbabilityMeasure (observedLaw (symmetricLaw (densityCubeClamp theta))) := by
    haveI := symmetricLaw_probability _ (densityCubeClamp_mem theta) hd
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hpi := measurable_finite_iid_inputLaw (n := n) _ hobs
    (fun theta => by haveI := hprob theta; infer_instance)
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hinput : Measurable (fun theta : Fin d → ℝ =>
      (Measure.pi (fun _ : Fin n =>
        observedLaw (symmetricLaw (densityCubeClamp theta)))).prod
          (Q.seedLaw.prod uniform01)) := by
    conv => arg 1; ext theta; rw [Measure.prod_def]
    exact (Measure.measurable_bind'
      (Measurable.map_prodMk_left (ν := Q.seedLaw.prod uniform01))).comp hpi
  unfold canonicalDecisionLaw
  exact (Measure.measurable_bind' (measurable_protocol_decisionRows Q)).comp hinput

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), and [the stated htheta condition](hyp:htheta). [The sampling hypotheses identify decision laws with their clipped versions on the cube](goal). -/
-- @node: clipped_canonicalDecisionLaw_eq
lemma clipped_canonicalDecisionLaw_eq (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
    canonicalDecisionLaw Q (observedLaw (symmetricLaw (densityCubeClamp theta))) =
      decisionLaw S Q (symmetricLaw theta) := by
  rw [densityCubeClamp_eq theta htheta]
  haveI := symmetricLaw_probability theta htheta hd
  unfold canonicalDecisionLaw decisionLaw
  rw [iid_sampling_inputLaw S hIID hRandom Q _
    (symmetricLaw_causalModel theta htheta hd)]

/-- Assume [the stated ha condition](hyp:ha) and [the stated hnu condition](hyp:hnu). [A supported coordinate prior places its entire product mass in the parameter cube](goal). -/
-- @node: amplitude_productPrior_ae_cube
lemma amplitude_productPrior_ae_cube (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    ∀ᵐ theta ∂productPrior d nu, theta ∈ parameterCube d := by
  letI := hnu.1
  have hcoord : ∀ᵐ u ∂nu, u ∈ Set.Icc (-a) a := ae_iff.mpr hnu.2
  have hall : ∀ᵐ theta ∂productPrior d nu, ∀ j, theta j ∈ Set.Icc (-a) a :=
    Filter.eventually_all.mpr (fun j => Measure.tendsto_eval_ae_ae.eventually hcoord)
  filter_upwards [hall] with theta htheta
  intro j
  exact ⟨by linarith [(htheta j).1], (htheta j).2.trans ha⟩

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Every supported mixture is a probability law, even for a sampling scheme specified only through its iid and independent-randomness properties](goal). -/
-- @node: mixtureLaw_probability
lemma mixtureLaw_probability (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    IsProbabilityMeasure (mixtureLaw S Q nu) := by
  letI := hnu.1
  let rows := fun theta : Fin d → ℝ =>
    (canonicalDecisionLaw Q (observedLaw (symmetricLaw (densityCubeClamp theta)))).map
      (fun w => (w.2.1,w.1))
  have hm : Measurable rows :=
    (Measure.measurable_map _ (by fun_prop)).comp
      (measurable_clipped_canonicalDecisionLaw Q hd)
  have heq : mixtureLaw S Q nu = (productPrior d nu).bind rows := by
    apply Measure.bind_congr_right
    filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
    dsimp [rows, seedTranscriptLaw]
    rw [clipped_canonicalDecisionLaw_eq S hIID hRandom Q hd theta htheta]
  rw [heq]
  haveI : IsProbabilityMeasure (productPrior d nu) := by
    unfold productPrior
    infer_instance
  apply isProbabilityMeasure_bind hm.aemeasurable
  filter_upwards [amplitude_productPrior_ae_cube (d := d) a ha nu hnu] with theta htheta
  haveI := symmetricLaw_probability theta htheta hd
  haveI := sampling_decisionLaw_probability S hIID hRandom Q _
    (symmetricLaw_causalModel theta htheta hd)
  dsimp [rows]
  rw [clipped_canonicalDecisionLaw_eq S hIID hRandom Q hd theta htheta]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [measurability of f](hyp:hf), and [the protocol transcript](hyp:hrange). [Arbitrary Borel randomized transcript statistics obey the mixture TV bound](goal). -/
-- @node: mixtureLaw_bounded_test
lemma mixtureLaw_bounded_test (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (f : Q.Seed × ProtocolTranscript Q → ℝ) (hf : Measurable f)
    (hrange : ∀ w, f w ∈ Set.Icc 0 1) :
    |(∫ w, f w ∂mixtureLaw S Q nu0) - (∫ w, f w ∂mixtureLaw S Q nu1)| ≤
      Causalean.Stat.tvDist (mixtureLaw S Q nu0) (mixtureLaw S Q nu1) := by
  haveI := mixtureLaw_probability S hIID hRandom Q hd a ha nu0 hnu0
  haveI := mixtureLaw_probability S hIID hRandom Q hd a ha nu1 hnu1
  simpa using Causalean.Stat.tvDist_integral_range
    (mixtureLaw S Q nu0) (mixtureLaw S Q nu1) f hf 0 1 (by norm_num)
    (by simpa using hrange)

end CausalSmith.Stat.LdpOptvalueUniformFrontier
