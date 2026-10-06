module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PairedProductPrior
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TVUpper

/-!
# A measurable completion of the paired decision experiment

Finite atomic sampling weights extend the canonical experiment to all input
measures. On probability laws this extension is exactly the iid experiment.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Fix [the local protocol Q](hyp:Q) and [the probability law P](hyp:P). [Atomic iid weights followed by the fixed protocol and its independent coins](goal). -/
-- @node: completedPairedDecisionLaw
def completedPairedDecisionLaw (Q : LocalProtocol n (PairedSymbol d))
    (P : Measure (PairedSymbol d)) : Measure (DecisionSpace Q) :=
  Measure.sum fun o : Fin n → PairedSymbol d =>
    (∏ i, P {o i}) •
      (((Measure.dirac o).prod (Q.seedLaw.prod uniform01)).bind (fun w =>
        (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2))))

/-- For every paired protocol, the completed finite atomic decision law is [measurable even off
the probability model](goal). -/
-- @node: measurable_completedPairedDecisionLaw
@[fun_prop] lemma measurable_completedPairedDecisionLaw (Q : LocalProtocol n (PairedSymbol d)) :
    Measurable (completedPairedDecisionLaw Q) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [completedPairedDecisionLaw, Measure.sum_apply _ hE, Measure.smul_apply,
    smul_eq_mul]
  apply Measurable.tsum
  intro o
  apply Measurable.mul _ measurable_const
  apply Finset.measurable_prod
  intro i hi
  exact (Measure.measurable_coe (measurableSet_singleton (o i))).comp
    (measurable_id)

/-- [On probability inputs, atomic sampling is the canonical iid experiment](goal). -/
-- @node: completedPairedDecisionLaw_eq_canonical
lemma completedPairedDecisionLaw_eq_canonical (Q : LocalProtocol n (PairedSymbol d))
    (P : Measure (PairedSymbol d)) [IsProbabilityMeasure P] :
    completedPairedDecisionLaw Q P = canonicalDecisionLaw Q P := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hAtomic : Measure.pi (fun _ : Fin n => P) =
      Measure.sum (fun o : Fin n → PairedSymbol d =>
        (∏ i, P {o i}) • Measure.dirac o) := by
    conv_lhs => rw [← Measure.sum_smul_dirac
      (Measure.pi (fun _ : Fin n => P))]
    simp only [Measure.pi_singleton]
  unfold canonicalDecisionLaw
  rw [hAtomic, Measure.prod_sum_left,
    Measure.bind_sum _ _ (measurable_protocol_decisionRows Q).aemeasurable]
  simp only [Measure.prod_smul_left, Measure.bind_smul, completedPairedDecisionLaw]

/-- [A measurable experiment commutes with pushing its parameter prior forward](goal). -/
-- @node: paired_prior_bind_map
lemma paired_prior_bind_map (nu : Measure (Fin d → ℝ))
    (K : LocalProtocol n (PairedSymbol d)) :
    (nu.map pairedLaw).bind (completedPairedDecisionLaw K) =
      nu.bind (fun theta => completedPairedDecisionLaw K (pairedLaw theta)) := by
  have hm : Measurable (fun theta : Fin d → ℝ =>
      completedPairedDecisionLaw K (pairedLaw theta)) :=
    (measurable_completedPairedDecisionLaw K).comp measurable_pairedLaw_parameter
  ext E hE
  rw [Measure.bind_apply hE (measurable_completedPairedDecisionLaw K).aemeasurable,
    Measure.bind_apply hE hm.aemeasurable]
  exact lintegral_map ((Measure.measurable_coe hE).comp
    (measurable_completedPairedDecisionLaw K)) measurable_pairedLaw_parameter

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The measurable law-space completion has precisely the original product-prior seed/transcript mixture on the supported paired cube](goal). -/
-- @node: paired_prior_completed_marginal
lemma paired_prior_completed_marginal (K : LocalProtocol n (PairedSymbol d))
    (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (((productPrior d nu).map pairedLaw).bind (completedPairedDecisionLaw K)).map
        (fun w => (w.2.1,w.1)) =
      (productPrior d nu).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)) := by
  have hm : Measurable (fun theta : Fin d → ℝ =>
      completedPairedDecisionLaw K (pairedLaw theta)) :=
    (measurable_completedPairedDecisionLaw K).comp measurable_pairedLaw_parameter
  rw [paired_prior_bind_map, map_bind_measurable_rows _ _ hm _ (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta htheta
  haveI : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd ⟨theta, htheta, rfl⟩
  rw [completedPairedDecisionLaw_eq_canonical]
  rfl

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hK), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), and [the stated hmatch condition](hyp:hmatch). [The exact one-hundredth contraction bound now applies to the measurable law-space experiment required by the separated-decision reduction](goal). -/
-- @node: paired_lawspace_resource_contraction
lemma paired_lawspace_resource_contraction (hRN : MeasurableKernelRadonNikodym)
    (K : LocalProtocol n (PairedSymbol d)) (eps : ℝ)
    (hK : SequentialClass K eps) (hAllowed : Allowed n d eps)
    (nu0 nu1 : Measure ℝ)
    (hnu0 : AmplitudePrior (frontierResources n d eps).converseAmp nu0)
    (hnu1 : AmplitudePrior (frontierResources n d eps).converseAmp nu1)
    (hmatch : MatchingMoments (frontierResources n d eps).converseDegree nu0 nu1) :
    Causalean.Stat.tvDist
      ((((productPrior d nu0).map pairedLaw).bind (completedPairedDecisionLaw K)).map
        (fun w => (w.2.1,w.1)))
      ((((productPrior d nu1).map pairedLaw).bind (completedPairedDecisionLaw K)).map
        (fun w => (w.2.1,w.1))) ≤ (1/100 : ℝ) := by
  have hd : 0 < d := by have := hAllowed.2.1; omega
  have ha := (frontier_converse_amplitude_domain n d eps hAllowed).2
  rw [paired_prior_completed_marginal K hd _ ha nu0 hnu0,
    paired_prior_completed_marginal K hd _ ha nu1 hnu1]
  exact paired_productPrior_resource_contraction hRN K eps hK hAllowed
    nu0 nu1 hnu0 hnu1 hmatch

/-- Assume [dimension at least two](hyp:hd) and [the stated hp condition](hyp:hp). [Paired cube laws retain the independent analyst randomizer in the completed experiment](goal). -/
-- @node: completedPairedDecisionLaw_randomizer
lemma completedPairedDecisionLaw_randomizer (K : LocalProtocol n (PairedSymbol d))
    (hd : 2 ≤ d) (p : Measure (PairedSymbol d)) (hp : p ∈ pairedFamily d) :
    completedPairedDecisionLaw K p =
      (((completedPairedDecisionLaw K p).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript K × K.Seed) × ℝ => (w.1.1,w.1.2,w.2)) := by
  rcases hp with ⟨theta, htheta, rfl⟩
  haveI : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex (by omega) ⟨theta, htheta, rfl⟩
  rw [completedPairedDecisionLaw_eq_canonical]
  have hEq := pulledProtocol_decisionLaw (canonicalScheme n d) canonicalScheme_iidPeople
    canonicalScheme_independentRandomness hd K theta htheta
  haveI := symmetricLaw_probability theta htheta (by omega)
  have h := sampling_decisionLaw_randomizer (canonicalScheme n d) canonicalScheme_iidPeople
    canonicalScheme_independentRandomness (pulledProtocol K) (symmetricLaw theta)
    (symmetricLaw_causalModel theta htheta (by omega))
  rw [hEq] at h
  exact h

/-- Assume [positive dimension](hyp:hd). [The paired family is Borel, as can be checked through its finite atomic masses](goal). -/
-- @node: measurableSet_pairedFamily
lemma measurableSet_pairedFamily (hd : 0 < d) : MeasurableSet (pairedFamily d) := by
  let weights : Measure (PairedSymbol d) → PairedSymbol d → ℝ≥0∞ := fun p v => p {v}
  have hw : Measurable weights := by
    apply measurable_pi_lambda
    intro v
    exact Measure.measurable_coe (measurableSet_singleton v)
  have hc : MeasurableSet (parameterCube d) := by
    unfold parameterCube
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j =>
      isClosed_Icc.measurableSet.preimage (measurable_pi_apply j)
  have hinj : Set.InjOn (fun theta : Fin d → ℝ => weights (pairedLaw theta))
      (parameterCube d) := by
    intro theta ht phi hp heq
    have hmass (t : Fin d → ℝ) (ht : t ∈ parameterCube d) (v : PairedSymbol d) :
        0 ≤ (1 + signVal v.2 * t v.1) / (2*d) := by
      apply div_nonneg _ (by positivity)
      have h := ht v.1
      cases v.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;>
        linarith [h.1, h.2]
    funext j
    have h := congrArg (fun w : PairedSymbol d → ℝ≥0∞ => (w (j,true)).toReal) heq
    change (pairedLaw theta).real {(j,true)} = (pairedLaw phi).real {(j,true)} at h
    unfold pairedLaw at h
    rw [atomLaw_real_singleton _ (hmass theta ht),
      atomLaw_real_singleton _ (hmass phi hp)] at h
    simp only [signVal, ↓reduceIte, one_mul] at h
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have h' := (div_left_inj' (by positivity : (2*(d : ℝ)) ≠ 0)).mp h
    linarith
  have himage := hc.image_of_measurable_injOn
    (hw.comp measurable_pairedLaw_parameter) hinj
  have heq : pairedFamily d = weights ⁻¹'
      ((fun theta : Fin d → ℝ => weights (pairedLaw theta)) '' parameterCube d) := by
    ext p
    constructor
    · rintro ⟨theta, ht, rfl⟩
      exact ⟨theta, ht, rfl⟩
    · rintro ⟨theta, ht, heq⟩
      refine ⟨theta, ht, ?_⟩
      apply Measure.ext_of_singleton
      intro v
      exact congrFun heq v
  rw [heq]
  exact himage.preimage hw

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Supported coordinate priors push forward to probability laws in the paired model](goal). -/
-- @node: pairedLaw_productPrior_support
lemma pairedLaw_productPrior_support (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    ((productPrior d nu).map pairedLaw) (pairedFamily d)ᶜ = 0 := by
  rw [Measure.map_apply measurable_pairedLaw_parameter (measurableSet_pairedFamily hd).compl]
  apply measure_mono_null _
    (show (productPrior d nu) (parameterCube d)ᶜ = 0 from
      ae_iff.mp (amplitude_productPrior_ae_cube a ha nu hnu))
  intro theta ht hcube
  exact ht ⟨theta, hcube, rfl⟩

/-- Assume [dimension at least two](hyp:hd), [the stated support condition](hyp:hSupport0), [the stated support condition](hyp:hSupport1), [strict separation of the two target values](hyp:hv), [the stated concentration near the target value](hyp:hEscape0), [the stated concentration near the target value](hyp:hEscape1), and [the stated total-variation bound](hyp:hTV). [The generic testing and connectedness reductions apply to completed paired experiments and yield bounds on the canonical paired decision risks](goal). -/
-- @node: paired_separated_lawspace_decisions
lemma paired_separated_lawspace_decisions
    (K : LocalProtocol n (PairedSymbol d)) (hd : 2 ≤ d)
    (pi0 pi1 : Measure (Measure (PairedSymbol d)))
    [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (hSupport0 : pi0 (pairedFamily d)ᶜ = 0)
    (hSupport1 : pi1 (pairedFamily d)ᶜ = 0)
    (v0 v1 eta omega : ℝ) (hv : v0 < v1)
    (hEscape0 : pi0.real {p | (v1-v0)/8 < |tvFromUniform p-v0|} ≤ eta)
    (hEscape1 : pi1.real {p | (v1-v0)/8 < |tvFromUniform p-v1|} ≤ eta)
    (hTV : Causalean.Stat.tvDist
      ((pi0.bind (completedPairedDecisionLaw K)).map (fun w => (w.2.1,w.1)))
      ((pi1.bind (completedPairedDecisionLaw K)).map (fun w => (w.2.1,w.1))) ≤ omega) :
    (∀ T : Estimator K,
      ENNReal.ofReal (9*(v1-v0)^2/128 * max 0 (1-omega-2*eta)) ≤
        ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
          squaredRisk (canonicalDecisionLaw K p.1) T (tvFromUniform p.1)) ∧
    (∀ J : IntervalDecision K 0 1,
      (∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J
        (tvFromUniform p)) →
      ENNReal.ofReal (3*(v1-v0)/4 * max 0 ((0.80 : ℝ)-2*eta-omega)) ≤
        ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
          expectedLength (canonicalDecisionLaw K p.1) J) := by
  have hEq (p : Measure (PairedSymbol d)) (hp : p ∈ pairedFamily d) :
      completedPairedDecisionLaw K p = canonicalDecisionLaw K p := by
    haveI : IsProbabilityMeasure p := pairedFamily_subset_simplex (by omega) hp
    exact completedPairedDecisionLaw_eq_canonical K p
  have hProb (p : Measure (PairedSymbol d)) (hp : p ∈ pairedFamily d) :
      IsProbabilityMeasure (completedPairedDecisionLaw K p) := by
    haveI : IsProbabilityMeasure p := pairedFamily_subset_simplex (by omega) hp
    rw [hEq p hp]
    exact canonicalDecisionLaw_probability K p
  have hsep := separated_value_mixtures_generic K (pairedFamily d) tvFromUniform
    (completedPairedDecisionLaw K) (completedPairedDecisionLaw_randomizer K hd)
    hProb pi0 pi1 hSupport0 hSupport1 measurable_tvFromUniform
    (measurable_completedPairedDecisionLaw K) v0 v1 eta omega hv hEscape0 hEscape1 hTV 0 1
  constructor
  · intro T
    convert hsep.1 T using 1
    congr 1
    funext p
    rw [hEq p.1 p.2]
  · intro J hCov
    have hCov' : ∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤
        coverage (completedPairedDecisionLaw K p) J (tvFromUniform p) := by
      intro p hp
      rw [hEq p hp]
      exact hCov p hp
    convert hsep.2 J hCov' using 1
    congr 1
    funext p
    rw [hEq p.1 p.2]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
