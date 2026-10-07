module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Decision
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.DecisionSampling
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.DecisionCompletion
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Helpers/SeparatedMixtures

Finite original-record private value frontiers: Helpers/SeparatedMixtures.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology ProbabilityTheory

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier



/-- Fix [the local protocol Q](hyp:Q). [Reattach an independent uniform analyst coin to a seed/transcript pair](goal). -/
-- @node: analystRandomizerKernel
def analystRandomizerKernel {n : ℕ} {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) : Kernel (Q.Seed × ProtocolTranscript Q) (DecisionSpace Q) :=
  ((Kernel.id : Kernel (Q.Seed × ProtocolTranscript Q) (Q.Seed × ProtocolTranscript Q)) ×ₖ
    Kernel.const _ uniform01).map (fun w => (w.1.2,w.1.1,w.2))

/-- [The reattachment channel is Markov, including for arbitrary public seeds](goal). -/
-- @node: analystRandomizerKernel_markov
lemma analystRandomizerKernel_markov {n : ℕ} {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) : IsMarkovKernel (analystRandomizerKernel Q) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  unfold analystRandomizerKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- [The reconstruction kernel is exactly the declared product with the analyst coin](goal). -/
-- @node: analystRandomizerKernel_reconstruct
lemma analystRandomizerKernel_reconstruct {n : ℕ} {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) (mu : Measure (DecisionSpace Q)) [IsProbabilityMeasure mu] :
    (mu.map (fun w => (w.2.1,w.1))).bind (analystRandomizerKernel Q) =
      (((mu.map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2))) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  ext E hE
  rw [Measure.bind_apply hE (Kernel.measurable _).aemeasurable,
    lintegral_map (show Measurable (fun x => analystRandomizerKernel Q x E) from
      (analystRandomizerKernel Q).measurable_coe hE) (by fun_prop)]
  have hpre : MeasurableSet
      ((fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) ⁻¹' E) :=
    (show Measurable (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ =>
      (w.1.1,w.1.2,w.2)) by fun_prop) hE
  rw [Measure.map_apply (by fun_prop) hE, Measure.prod_apply hpre]
  rw [lintegral_map (measurable_measure_prodMk_left hpre) (by fun_prop)]
  apply lintegral_congr
  intro w
  rw [analystRandomizerKernel, Kernel.map_apply _ (by fun_prop),
    Measure.map_apply (by fun_prop) hE,
    Kernel.id_prod_apply' _ _
      ((show Measurable (fun w : (Q.Seed × ProtocolTranscript Q) × ℝ =>
        (w.1.2,w.1.1,w.2)) by fun_prop) hE), Kernel.const_apply]
  rfl

/-- Assume [measurability of laws](hyp:hLaws), [the stated probability-measure property](hyp:hProbability), [the product-law representation](hyp:hProduct), and [the stated support condition](hyp:hSupport). [Supported rowwise coin independence also holds for a predictive mixture](goal). -/
-- @node: supported_mixture_randomizer_reconstruct
lemma supported_mixture_randomizer_reconstruct {n : ℕ} {α Ω : Type}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (Q : LocalProtocol n α) (M : Set (Measure Ω))
    (laws : Measure Ω → Measure (DecisionSpace Q)) (hLaws : Measurable laws)
    (hProbability : ∀ p ∈ M, IsProbabilityMeasure (laws p))
    (hProduct : ∀ p ∈ M, laws p =
      (((laws p).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)))
    (pi : Measure (Measure Ω)) [IsProbabilityMeasure pi] (hSupport : pi Mᶜ = 0) :
    ((pi.bind laws).map (fun w => (w.2.1,w.1))).bind (analystRandomizerKernel Q) =
      pi.bind laws := by
  have hg : Measurable (fun w : DecisionSpace Q => (w.2.1,w.1)) := by fun_prop
  have hH := (analystRandomizerKernel Q).measurable
  ext E hE
  rw [Measure.bind_apply hE hH.aemeasurable,
    lintegral_map ((analystRandomizerKernel Q).measurable_coe hE) hg,
    Measure.bind_apply hE hLaws.aemeasurable]
  have hlin := Measure.lintegral_bind (m := pi) hLaws.aemeasurable
    (((analystRandomizerKernel Q).measurable_coe hE).comp hg).aemeasurable
  simp only [Function.comp_def] at hlin
  rw [hlin]
  apply lintegral_congr_ae
  filter_upwards [ae_iff.mpr hSupport] with p hp
  haveI := hProbability p hp
  have hr := (analystRandomizerKernel_reconstruct Q (laws p)).trans (hProduct p hp).symm
  have hh := congrArg (fun mu : Measure (DecisionSpace Q) => mu E) hr
  rw [Measure.bind_apply hE hH.aemeasurable,
    lintegral_map ((analystRandomizerKernel Q).measurable_coe hE) hg] at hh
  exact hh

/-- Assume [measurability of laws](hyp:hLaws), [the stated probability-measure property](hyp:hProbability), [the product-law representation](hyp:hProduct), [the stated support condition](hyp:hSupport0), and [the stated support condition](hyp:hSupport1). [Appending independent analyst randomness cannot increase predictive total variation](goal). -/
-- @node: supported_mixture_randomizer_tv
lemma supported_mixture_randomizer_tv {n : ℕ} {α Ω : Type}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (Q : LocalProtocol n α) (M : Set (Measure Ω))
    (laws : Measure Ω → Measure (DecisionSpace Q)) (hLaws : Measurable laws)
    (hProbability : ∀ p ∈ M, IsProbabilityMeasure (laws p))
    (hProduct : ∀ p ∈ M, laws p =
      (((laws p).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)))
    (pi0 pi1 : Measure (Measure Ω)) [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 Mᶜ = 0) (hSupport1 : pi1 Mᶜ = 0) :
    Causalean.Stat.tvDist (pi0.bind laws) (pi1.bind laws) ≤
      Causalean.Stat.tvDist
        ((pi0.bind laws).map (fun w => (w.2.1,w.1)))
        ((pi1.bind laws).map (fun w => (w.2.1,w.1))) := by
  haveI : IsProbabilityMeasure (pi0.bind laws) := isProbabilityMeasure_bind
    hLaws.aemeasurable ((ae_iff.mpr hSupport0).mono (fun p hp => hProbability p hp))
  haveI : IsProbabilityMeasure (pi1.bind laws) := isProbabilityMeasure_bind
    hLaws.aemeasurable ((ae_iff.mpr hSupport1).mono (fun p hp => hProbability p hp))
  haveI : IsProbabilityMeasure ((pi0.bind laws).map (fun w => (w.2.1,w.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure ((pi1.bind laws).map (fun w => (w.2.1,w.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI := analystRandomizerKernel_markov Q
  have ht := Causalean.Stat.tvDist_bind_le
    ((pi0.bind laws).map (fun w => (w.2.1,w.1)))
    ((pi1.bind laws).map (fun w => (w.2.1,w.1))) (analystRandomizerKernel Q)
  rw [supported_mixture_randomizer_reconstruct Q M laws hLaws hProbability hProduct pi0 hSupport0,
    supported_mixture_randomizer_reconstruct Q M laws hLaws hProbability hProduct pi1 hSupport1] at ht
  exact ht

/-- Assume [the stated hsupport condition](hyp:hsupport). [A supported prior averages no more risk than the supremum on its support](goal). -/
-- @node: supported_prior_risk_le
lemma supported_prior_risk_le {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (pi : Measure Θ) [IsProbabilityMeasure pi] (M : Set Θ)
    (hsupport : pi Mᶜ = 0) (K : Kernel Θ X) (target : Θ → ℝ) (T : X → ℝ) :
    Causalean.Stat.Minimax.FuzzyHypotheses.bayesSquaredRisk pi K target T ≤
      ⨆ p : {p : Θ // p ∈ M},
        Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk K target T p.1 := by
  apply lintegral_le_const
  have hs : ∀ᵐ p ∂pi, p ∈ M := ae_iff.mpr hsupport
  filter_upwards [hs] with p hp
  exact le_iSup (fun p : {p : Θ // p ∈ M} =>
    Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk K target T p.1) ⟨p,hp⟩

/-- Assume [the stated probability-measure property](hyp:hLawProbability), [the stated support condition](hyp:hSupport0), [the stated support condition](hyp:hSupport1), [measurability of target](hyp:hTarget), [measurability of laws](hyp:hLaws), [strict separation of the two target values](hyp:hv), [the stated concentration near the target value](hyp:hEscape0), [the stated concentration near the target value](hyp:hEscape1), and [the stated total-variation bound](hyp:hTV). [The exact paper risk constant follows from classification at the midpoint. Rows outside the model are completed to probability rows without changing either prior](goal). -/
-- @node: separated_prior_squared_risk
lemma separated_prior_squared_risk {n : ℕ} {α Ω : Type}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (Q : LocalProtocol n α) (M : Set (Measure Ω)) (target : Measure Ω → ℝ)
    (laws : Measure Ω → Measure (DecisionSpace Q))
    (hLawProbability : ∀ p ∈ M, IsProbabilityMeasure (laws p))
    (pi0 pi1 : Measure (Measure Ω)) [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 Mᶜ = 0) (hSupport1 : pi1 Mᶜ = 0)
    (hTarget : Measurable target) (hLaws : Measurable laws)
    (v0 v1 eta0 omega : ℝ) (hv : v0 < v1)
    (hEscape0 : pi0.real {p | (v1-v0)/8 < |target p - v0|} ≤ eta0)
    (hEscape1 : pi1.real {p | (v1-v0)/8 < |target p - v1|} ≤ eta0)
    (hTV : Causalean.Stat.tvDist (pi0.bind laws) (pi1.bind laws) ≤ omega)
    (T : Estimator Q) :
    ENNReal.ofReal (9*(v1-v0)^2/128 * max 0 (1-omega-2*eta0)) ≤
      ⨆ p : {p : Measure Ω // p ∈ M}, squaredRisk (laws p.1) T (target p.1) := by
  classical
  have hnonempty : M.Nonempty := by
    by_contra h
    have hM : M = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simpa [hM] using hSupport0
  obtain ⟨p0,hp0⟩ := hnonempty
  let K : Kernel (Measure Ω) (DecisionSpace Q) :=
    ⟨fun p => if (laws p) Set.univ = 1 then laws p else laws p0,
      hLaws.ite (measurableSet_eq_fun
        ((Measure.measurable_coe MeasurableSet.univ).comp hLaws) measurable_const)
        measurable_const⟩
  have hK : ∀ p, IsProbabilityMeasure (K p) := by
    intro p
    change IsProbabilityMeasure (if (laws p) Set.univ = 1 then laws p else laws p0)
    split_ifs with h
    · exact ⟨h⟩
    · exact hLawProbability p0 hp0
  have hKM : ∀ p ∈ M, K p = laws p := by
    intro p hp
    haveI := hLawProbability p hp
    simp [K]
  have hbind (pi : Measure (Measure Ω)) (hsupport : pi Mᶜ = 0) :
      pi.bind K = pi.bind laws := by
    apply Measure.bind_congr_right
    filter_upwards [ae_iff.mpr hsupport] with p hp
    exact hKM p hp
  haveI : IsProbabilityMeasure (pi0.bind laws) :=
    isProbabilityMeasure_bind hLaws.aemeasurable
      ((ae_iff.mpr hSupport0).mono (fun p hp => hLawProbability p hp))
  haveI : IsProbabilityMeasure (pi1.bind laws) :=
    isProbabilityMeasure_bind hLaws.aemeasurable
      ((ae_iff.mpr hSupport1).mono (fun p hp => hLawProbability p hp))
  have heta : 0 ≤ eta0 := (measureReal_nonneg).trans hEscape0
  have homega : 0 ≤ omega := (Causalean.Stat.tvDist_nonneg).trans hTV
  have htvK : Causalean.Stat.tvDist
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi0 K)
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi1 K) ≤ omega := by
    simpa only [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive,
      hbind pi0 hSupport0, hbind pi1 hSupport1] using hTV
  have hbayes := Causalean.Stat.Minimax.FuzzyHypotheses.twoFuzzyHypotheses_bayesRisk_lower
    pi0 pi1 K target hK T.1 T.2 hTarget v0 v1 (v1-v0) ((v1-v0)/8)
    eta0 eta0 omega (by linarith) le_rfl
    hEscape0 hEscape1 htvK
  have hconst : (((v1-v0)/2 - (v1-v0)/8)^2 * (1-omega-eta0-eta0))/2 =
      9*(v1-v0)^2/128 * (1-omega-2*eta0) := by ring
  rw [hconst] at hbayes
  have hupper : max
      (Causalean.Stat.Minimax.FuzzyHypotheses.bayesSquaredRisk pi0 K target T.1)
      (Causalean.Stat.Minimax.FuzzyHypotheses.bayesSquaredRisk pi1 K target T.1) ≤
      ⨆ p : {p : Measure Ω // p ∈ M}, squaredRisk (laws p.1) T (target p.1) := by
    apply max_le
    all_goals
      refine (supported_prior_risk_le _ M ?_ K target T.1).trans ?_
      first | exact hSupport0 | exact hSupport1
      apply iSup_le
      intro p
      have heq : Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk K target T.1 p.1 =
          squaredRisk (laws p.1) T (target p.1) := by
        simp only [Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk, squaredRisk,
          hKM p.1 p.2]
      rw [heq]
      exact le_iSup (fun p : {p : Measure Ω // p ∈ M} =>
        squaredRisk (laws p.1) T (target p.1)) p
  by_cases hpos : 0 ≤ 1-omega-2*eta0
  · rw [max_eq_right hpos]
    exact hbayes.trans hupper
  · rw [max_eq_left (le_of_not_ge hpos), mul_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- Assume [measurability of laws](hyp:hLaws), [the stated probability-measure property](hyp:hProbability), [the stated support condition](hyp:hSupport), [measurability of target](hyp:hTarget), [the stated concentration near the target value](hyp:hEscape), and [uniform ninety-percent coverage](hyp:hCoverage). [Integrating global coverage loses at most the prior's target escape probability](goal). -/
-- @node: supported_prior_neighborhood_mass
lemma supported_prior_neighborhood_mass {n : ℕ} {α Ω : Type}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (Q : LocalProtocol n α) (M : Set (Measure Ω)) (target : Measure Ω → ℝ)
    (laws : Measure Ω → Measure (DecisionSpace Q)) (hLaws : Measurable laws)
    (hProbability : ∀ p ∈ M, IsProbabilityMeasure (laws p))
    (pi : Measure (Measure Ω)) [IsProbabilityMeasure pi] (hSupport : pi Mᶜ = 0)
    (hTarget : Measurable target) (v r eta : ℝ)
    (hEscape : pi.real {p | r < |target p - v|} ≤ eta)
    {lower upper : ℝ} (I : IntervalDecision Q lower upper)
    (hCoverage : ∀ p ∈ M, (0.90 : ℝ) ≤ coverage (laws p) I (target p)) :
    (0.90 : ℝ) - eta ≤ (pi.bind laws).real
      {w | I.lo w ≤ v+r ∧ v-r ≤ I.hi w} := by
  let A : Set (DecisionSpace Q) := {w | I.lo w ≤ v+r ∧ v-r ≤ I.hi w}
  let B : Set (Measure Ω) := {p | r < |target p-v|}
  have hA : MeasurableSet A :=
    (measurableSet_le I.measurable_lo measurable_const).inter
      (measurableSet_le measurable_const I.measurable_hi)
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hTarget.sub measurable_const))
  have hs : ∀ᵐ p ∂pi, p ∈ M := ae_iff.mpr hSupport
  have hrow : Integrable (fun p => (laws p).real A) pi := by
    apply Integrable.of_bound
      (((Measure.measurable_coe hA).comp hLaws).ennreal_toReal.aestronglyMeasurable) 1
    filter_upwards [hs] with p hp
    haveI := hProbability p hp
    change ‖(laws p).real A‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (Set.subset_univ A)).trans (by simp)
  have hind : Integrable (B.indicator (fun _ => (1 : ℝ))) pi :=
    (integrable_const _).indicator hB
  have hpoint : ∀ᵐ p ∂pi,
      (0.90 : ℝ) ≤ (laws p).real A + B.indicator (fun _ => (1 : ℝ)) p := by
    filter_upwards [hs] with p hp
    haveI := hProbability p hp
    by_cases hb : p ∈ B
    · rw [Set.indicator_of_mem hb]
      linarith [measureReal_nonneg (μ := laws p) (s := A)]
    · rw [Set.indicator_of_notMem hb, add_zero]
      have hgood : |target p-v| ≤ r := le_of_not_gt hb
      refine (hCoverage p hp).trans (measureReal_mono ?_)
      intro w hw
      rcases hw with ⟨hwlo,hwhi⟩
      exact ⟨by linarith [(abs_le.mp hgood).2], by linarith [(abs_le.mp hgood).1]⟩
  have hint := integral_mono_ae (integrable_const (0.90 : ℝ)) (hrow.add hind) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add hrow hind] at hint
  have hindval : (∫ p, B.indicator (fun _ => (1 : ℝ)) p ∂pi) = pi.real B := by
    simpa only [Pi.one_def] using integral_indicator_one (μ := pi) hB
  rw [hindval] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  have hreal : (pi.bind laws).real A = ∫ p, (laws p).real A ∂pi := by
    rw [Measure.real, Measure.bind_apply hA hLaws.aemeasurable]
    symm
    apply integral_toReal ((Measure.measurable_coe hA).comp hLaws).aemeasurable
    filter_upwards [hs] with p hp
    haveI := hProbability p hp
    exact measure_lt_top _ _
  change (0.90 : ℝ) - eta ≤ (pi.bind laws).real A
  rw [hreal]
  change pi.real B ≤ eta at hEscape
  linarith

/-- Assume [the stated probability-measure property](hyp:hProbability), [the stated support condition](hyp:hSupport0), [the stated support condition](hyp:hSupport1), [measurability of target](hyp:hTarget), [measurability of laws](hyp:hLaws), [strict separation of the two target values](hyp:hv), [the stated concentration near the target value](hyp:hEscape0), [the stated concentration near the target value](hyp:hEscape1), [the stated total-variation bound](hyp:hTV), and [uniform ninety-percent coverage](hyp:hCoverage). [Two concentrated target neighborhoods force the paper's connected-interval length bound](goal). -/
-- @node: separated_prior_interval_length
lemma separated_prior_interval_length {n : ℕ} {α Ω : Type}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (Q : LocalProtocol n α) (M : Set (Measure Ω)) (target : Measure Ω → ℝ)
    (laws : Measure Ω → Measure (DecisionSpace Q))
    (hProbability : ∀ p ∈ M, IsProbabilityMeasure (laws p))
    (pi0 pi1 : Measure (Measure Ω)) [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 Mᶜ = 0) (hSupport1 : pi1 Mᶜ = 0)
    (hTarget : Measurable target) (hLaws : Measurable laws)
    (v0 v1 eta0 omega : ℝ) (hv : v0 < v1)
    (hEscape0 : pi0.real {p | (v1-v0)/8 < |target p - v0|} ≤ eta0)
    (hEscape1 : pi1.real {p | (v1-v0)/8 < |target p - v1|} ≤ eta0)
    (hTV : Causalean.Stat.tvDist (pi0.bind laws) (pi1.bind laws) ≤ omega)
    {lower upper : ℝ} (I : IntervalDecision Q lower upper)
    (hCoverage : ∀ p ∈ M, (0.90 : ℝ) ≤ coverage (laws p) I (target p)) :
    ENNReal.ofReal (3*(v1-v0)/4 * max 0 ((0.80 : ℝ)-2*eta0-omega)) ≤
      ⨆ p : {p : Measure Ω // p ∈ M}, expectedLength (laws p.1) I := by
  haveI : IsProbabilityMeasure (pi0.bind laws) := isProbabilityMeasure_bind
    hLaws.aemeasurable ((ae_iff.mpr hSupport0).mono (fun p hp => hProbability p hp))
  haveI : IsProbabilityMeasure (pi1.bind laws) := isProbabilityMeasure_bind
    hLaws.aemeasurable ((ae_iff.mpr hSupport1).mono (fun p hp => hProbability p hp))
  let A := fun v : ℝ => {w : DecisionSpace Q |
    I.lo w ≤ v+(v1-v0)/8 ∧ v-(v1-v0)/8 ≤ I.hi w}
  have hA (v : ℝ) : MeasurableSet (A v) :=
    (measurableSet_le I.measurable_lo measurable_const).inter
      (measurableSet_le measurable_const I.measurable_hi)
  have hm0 := supported_prior_neighborhood_mass Q M target laws hLaws hProbability
    pi0 hSupport0 hTarget v0 ((v1-v0)/8) eta0 hEscape0 I hCoverage
  have hm1 := supported_prior_neighborhood_mass Q M target laws hLaws hProbability
    pi1 hSupport1 hTarget v1 ((v1-v0)/8) eta0 hEscape1 I hCoverage
  change (0.90 : ℝ)-eta0 ≤ (pi0.bind laws).real (A v0) at hm0
  change (0.90 : ℝ)-eta0 ≤ (pi1.bind laws).real (A v1) at hm1
  have htransfer := (abs_le.mp
    ((Causalean.Stat.abs_measureReal_sub_le_tvDist (μ := pi0.bind laws)
      (ν := pi1.bind laws) (hA v1)).trans hTV)).1
  have hinter : (0.80 : ℝ)-2*eta0-omega ≤
      (pi0.bind laws).real (A v0 ∩ A v1) := by
    have hsplit := measureReal_inter_add_sdiff (μ := pi0.bind laws) (s := A v0) (hA v1)
    have hdiff := measureReal_mono (μ := pi0.bind laws)
      (show A v0 \ A v1 ⊆ (A v1)ᶜ from fun _ h => h.2)
    rw [probReal_compl_eq_one_sub (hA v1)] at hdiff
    linarith
  have hc : 0 ≤ 3*(v1-v0)/4 := by linarith
  have hmass : max 0 ((0.80 : ℝ)-2*eta0-omega) ≤
      (pi0.bind laws).real (A v0 ∩ A v1) := max_le measureReal_nonneg hinter
  have hlength : ENNReal.ofReal (3*(v1-v0)/4) *
      (pi0.bind laws) (A v0 ∩ A v1) ≤ expectedLength (pi0.bind laws) I := by
    rw [← lintegral_indicator_const (hA v0 |>.inter (hA v1))]
    apply lintegral_mono
    intro w
    by_cases hw : w ∈ A v0 ∩ A v1
    · rw [Set.indicator_of_mem hw]
      apply ENNReal.ofReal_le_ofReal
      apply le_trans _ (le_max_right _ _)
      change 3*(v1-v0)/4 ≤ I.hi w - I.lo w
      rcases hw with ⟨h0,h1⟩
      dsimp [A] at h0 h1
      linarith [h0.1,h1.2]
    · rw [Set.indicator_of_notMem hw]
      exact zero_le
  have hbayes : expectedLength (pi0.bind laws) I ≤
      ⨆ p : {p : Measure Ω // p ∈ M}, expectedLength (laws p.1) I := by
    unfold expectedLength
    have hmeas : Measurable (fun w =>
      ENNReal.ofReal (Causalean.Stat.intervalLength (I.lo w) (I.hi w))) :=
      (Causalean.Stat.measurable_intervalLength I.measurable_lo I.measurable_hi).ennreal_ofReal
    rw [Measure.lintegral_bind hLaws.aemeasurable hmeas.aemeasurable]
    apply lintegral_le_const
    filter_upwards [ae_iff.mpr hSupport0] with p hp
    exact le_iSup (fun p : {p : Measure Ω // p ∈ M} =>
      ∫⁻ w, ENNReal.ofReal (Causalean.Stat.intervalLength (I.lo w) (I.hi w)) ∂laws p.1) ⟨p,hp⟩
  refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmass hc)).trans ?_
  rw [ENNReal.ofReal_mul hc, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact hlength.trans hbayes


variable {n : ℕ} {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω]
/-- Assume [the product-law representation](hyp:hProduct), [the stated probability-measure property](hyp:hLawProbability), [the stated support condition](hyp:hSupport0), [the stated support condition](hyp:hSupport1), [measurability of target](hyp:hTarget), [measurability of laws](hyp:hLaws), [strict separation of the two target values](hyp:hv), [the stated concentration near the target value](hyp:hEscape0), [the stated concentration near the target value](hyp:hEscape1), and [the stated total-variation bound](hyp:hTV). [Generic concentrated-prior squared-risk and connected honest-length lower bounds](goal). -/
-- @node: separated_value_mixtures_generic
lemma separated_value_mixtures_generic
    (Q : LocalProtocol n α) (M : Set (Measure Ω)) (target : Measure Ω → ℝ)
    (laws : Measure Ω → Measure (DecisionSpace Q))
    (hProduct : ∀ p ∈ M, laws p =
      (((laws p).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)))
    (hLawProbability : ∀ p ∈ M, IsProbabilityMeasure (laws p))
    (pi0 pi1 : Measure (Measure Ω)) [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 Mᶜ = 0) (hSupport1 : pi1 Mᶜ = 0)
    (hTarget : Measurable target) (hLaws : Measurable laws)
    (v0 v1 eta0 omega : ℝ) (hv : v0 < v1)
    (hEscape0 : pi0.real {p | (v1-v0)/8 < |target p - v0|} ≤ eta0)
    (hEscape1 : pi1.real {p | (v1-v0)/8 < |target p - v1|} ≤ eta0)
    (hTV : Causalean.Stat.tvDist
      ((pi0.bind laws).map (fun w => (w.2.1,w.1)))
      ((pi1.bind laws).map (fun w => (w.2.1,w.1))) ≤ omega)
    (lower upper : ℝ) :
    (∀ T : Estimator Q,
      ENNReal.ofReal (9*(v1-v0)^2/128 * max 0 (1-omega-2*eta0)) ≤
        ⨆ p : {p : Measure Ω // p ∈ M}, squaredRisk (laws p.1) T (target p.1)) ∧
    (∀ I : IntervalDecision Q lower upper,
      (∀ p ∈ M, (0.90 : ℝ) ≤ coverage (laws p) I (target p)) →
      ENNReal.ofReal (3*(v1-v0)/4 * max 0 ((0.80 : ℝ)-2*eta0-omega)) ≤
        ⨆ p : {p : Measure Ω // p ∈ M}, expectedLength (laws p.1) I) := by
  have hFullTV : Causalean.Stat.tvDist (pi0.bind laws) (pi1.bind laws) ≤ omega :=
    (supported_mixture_randomizer_tv Q M laws hLaws hLawProbability hProduct
      pi0 pi1 hSupport0 hSupport1).trans hTV
  constructor
  · intro T
    exact separated_prior_squared_risk Q M target laws hLawProbability pi0 pi1
      hSupport0 hSupport1 hTarget hLaws v0 v1 eta0 omega hv hEscape0 hEscape1 hFullTV T
  · intro I hCoverage
    exact separated_prior_interval_length Q M target laws hLawProbability pi0 pi1
      hSupport0 hSupport1 hTarget hLaws v0 v1 eta0 omega hv hEscape0 hEscape1
      hFullTV I hCoverage

-- @node: lem:separated-value-mixtures
/-- Under [iid sampling and independent randomization](hyp:hIID,hRandom), two priors with
[causal support](hyp:hSupport0,hSupport1), [probability decision mixtures](hyp:hMixture0,hMixture1),
[separated target centers](hyp:hv), [small escape probabilities](hyp:hEscape0,hEscape1), and
[nearby transcript mixtures](hyp:hTV), the causal experiment obeys [squared-risk and connected
honest-length lower bounds](goal). -/
lemma separated_value_mixtures {d : ℕ}
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d))
    (pi0 pi1 : Measure (Measure (FullRecord d)))
    [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 (causalClass d)ᶜ = 0) (hSupport1 : pi1 (causalClass d)ᶜ = 0)
    (hMixture0 : IsProbabilityMeasure (pi0.bind (decisionLaw S Q)))
    (hMixture1 : IsProbabilityMeasure (pi1.bind (decisionLaw S Q)))
    (v0 v1 eta0 omega : ℝ) (hv : v0 < v1)
    (hEscape0 : pi0.real {P | (v1-v0)/8 < |value P - v0|} ≤ eta0)
    (hEscape1 : pi1.real {P | (v1-v0)/8 < |value P - v1|} ≤ eta0)
    (hTV : Causalean.Stat.tvDist
      ((pi0.bind (decisionLaw S Q)).map (fun w => (w.2.1,w.1)))
      ((pi1.bind (decisionLaw S Q)).map (fun w => (w.2.1,w.1))) ≤ omega) :
    (∀ T : Estimator Q,
      ENNReal.ofReal (9*(v1-v0)^2/128 * max 0 (1-omega-2*eta0)) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
    (∀ I : IntervalDecision Q (1/4) (3/4),
      (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
      ENNReal.ofReal (3*(v1-v0)/4 * max 0 ((0.80 : ℝ)-2*eta0-omega)) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          expectedLength (decisionLaw S Q P.1) I) := by
  -- Use a measurable completion of the canonical iid law on the supported causal model.
  obtain ⟨laws, hLaws, hCanonical⟩ :
      ∃ laws : Measure (FullRecord d) → Measure (DecisionSpace Q),
        Measurable laws ∧ ∀ P ∈ causalClass d,
          laws P = decisionLaw (canonicalScheme n d) Q P := by
    refine ⟨completedDecisionLaw Q, measurable_completedDecisionLaw Q, ?_⟩
    intro P hP
    haveI := hP.1
    exact completedDecisionLaw_eq_canonical Q P
  have hEq (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      laws P = decisionLaw S Q P := by
    haveI := hP.1
    rw [hCanonical P hP]
    unfold decisionLaw
    rw [iid_sampling_inputLaw S hIID hRandom Q P hP.2]
    rfl
  have hPriorEq (pi : Measure (Measure (FullRecord d)))
      (hSupport : pi (causalClass d)ᶜ = 0) :
      pi.bind laws = pi.bind (decisionLaw S Q) := by
    apply Measure.bind_congr_right
    filter_upwards [ae_iff.mpr hSupport] with P hP
    exact hEq P hP
  have hProbability (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      IsProbabilityMeasure (decisionLaw S Q P) := by
    haveI := hP.1
    exact sampling_decisionLaw_probability S hIID hRandom Q P hP.2
  have hProduct (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      decisionLaw S Q P =
        (((decisionLaw S Q P).map (fun w => (w.1,w.2.1))).prod uniform01).map
          (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) := by
    haveI := hP.1
    exact sampling_decisionLaw_randomizer S hIID hRandom Q P hP.2
  have hLawsProbability (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      IsProbabilityMeasure (laws P) := by
    rw [hEq P hP]
    exact hProbability P hP
  have hLawsProduct (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
      laws P = (((laws P).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) := by
    rw [hEq P hP]
    exact hProduct P hP
  have hLawsTV : Causalean.Stat.tvDist
      ((pi0.bind laws).map (fun w => (w.2.1,w.1)))
      ((pi1.bind laws).map (fun w => (w.2.1,w.1))) ≤ omega := by
    rw [hPriorEq pi0 hSupport0, hPriorEq pi1 hSupport1]
    exact hTV
  have hReduction := separated_value_mixtures_generic Q (causalClass d) value laws
    hLawsProduct hLawsProbability pi0 pi1 hSupport0 hSupport1 measurable_causal_value hLaws
    v0 v1 eta0 omega hv hEscape0 hEscape1 hLawsTV (1/4) (3/4)
  constructor
  · intro T
    have hRisk : (⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
        squaredRisk (laws P.1) T (value P.1)) =
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          squaredRisk (decisionLaw S Q P.1) T (value P.1) := by
      apply iSup_congr
      intro P
      rw [hEq P.1 P.2]
    rw [← hRisk]
    exact hReduction.1 T
  · intro I hCoverage
    have hLawsCoverage (P : Measure (FullRecord d)) (hP : P ∈ causalClass d) :
        (0.90 : ℝ) ≤ coverage (laws P) I (value P) := by
      rw [hEq P hP]
      exact hCoverage P hP
    have hLength : (⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
        expectedLength (laws P.1) I) =
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          expectedLength (decisionLaw S Q P.1) I := by
      apply iSup_congr
      intro P
      rw [hEq P.1 P.2]
    rw [← hLength]
    exact hReduction.2 I hLawsCoverage


end CausalSmith.Stat.LdpOptvalueUniformFrontier
