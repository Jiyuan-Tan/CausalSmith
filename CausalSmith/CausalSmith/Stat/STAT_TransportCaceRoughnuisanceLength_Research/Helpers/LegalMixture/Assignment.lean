module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ArmHolder

/-! # Randomized assignment and independent product sampling

The primitive construction records consistent receipt and outcome values.
A normalized binary assignment kernel preserves the primitive marginal and
provides the conditional event identity in roadmap (13)--(18).
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The assignment overlay draws the instrument and records its consistent observables.  For [the displayed assumptions and inputs](hyp:e,o), [the stated object is defined](goal). -/
-- @node: membershipAssignmentKernel
noncomputable def membershipAssignmentKernel (e : ℝ → ℝ) (o : FullData) : Measure Assigned :=
  ENNReal.ofReal (e (covariate o)) •
    Measure.dirac (o, true, potentialReceipt o true,
      potentialOutcome o (potentialReceipt o true)) +
  ENNReal.ofReal (1 - e (covariate o)) •
    Measure.dirac (o, false, potentialReceipt o false,
      potentialOutcome o (potentialReceipt o false))

/-- If [the assignment propensity is measurable](hyp:he), then [the induced assignment kernel is measurable](goal). -/
-- @node: membershipAssignmentKernel_measurable
@[fun_prop] lemma membershipAssignmentKernel_measurable (e : ℝ → ℝ) (he : Measurable e) :
    Measurable (membershipAssignmentKernel e) := by
  have hc : Measurable covariate := by unfold covariate; fun_prop
  have hr (z : Bool) : Measurable (fun o : FullData =>
      (o, z, potentialReceipt o z, potentialOutcome o (potentialReceipt o z))) := by
    unfold potentialReceipt potentialOutcome receipt0 receipt1 outcome0 outcome1
    cases z <;> simp only [Bool.false_eq_true, if_false, if_true]
    all_goals
      apply Measurable.prodMk measurable_id
      apply Measurable.prodMk measurable_const
      apply Measurable.prodMk (by fun_prop)
      exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
        (by fun_prop) (by fun_prop)
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  simp only [membershipAssignmentKernel, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hB]
  exact ((he.comp hc).ennreal_ofReal.mul
    (measurable_one.indicator (hB.preimage (hr true)))).add
    ((measurable_const.sub (he.comp hc)).ennreal_ofReal.mul
      (measurable_one.indicator (hB.preimage (hr false))))

/-- The assigned overlay is supported on consistent receipt and outcome records.  Under [the displayed assumptions and inputs](hyp:e,he), [the stated conclusion holds](goal). -/
-- @node: assignedFrom_consistency
lemma assignedFrom_consistency (μ : Measure FullData) (e : ℝ → ℝ)
    (he : Measurable e) :
    ∀ᵐ o ∂assignedFrom μ e,
      o.2.2.1 = potentialReceipt o.1 o.2.1 ∧
      o.2.2.2 = potentialOutcome o.1 o.2.2.1 := by
  have hbad : MeasurableSet {o : Assigned | ¬
      (o.2.2.1 = potentialReceipt o.1 o.2.1 ∧
       o.2.2.2 = potentialOutcome o.1 o.2.2.1)} := by
    have hr : Measurable (fun o : Assigned => potentialReceipt o.1 o.2.1) := by
      unfold potentialReceipt receipt0 receipt1
      exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
        (by fun_prop) (by fun_prop)
    have hy : Measurable (fun o : Assigned => potentialOutcome o.1 o.2.2.1) := by
      unfold potentialOutcome outcome0 outcome1
      exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
        (by fun_prop) (by fun_prop)
    exact ((measurableSet_eq_fun (by fun_prop) hr).inter
      (measurableSet_eq_fun (by fun_prop) hy)).compl
  rw [ae_iff]
  change (μ.bind (membershipAssignmentKernel e)) _ = 0
  rw [Measure.bind_apply hbad (membershipAssignmentKernel_measurable e he).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall (fun o => by
    simp [membershipAssignmentKernel, Measure.add_apply, Measure.smul_apply])

/-- Assignment preserves the primitive marginal for unit-interval propensities.  Under [the displayed assumptions and inputs](hyp:e,he,hb), [the stated conclusion holds](goal). -/
-- @node: assignedFrom_map_fst
lemma assignedFrom_map_fst (μ : Measure FullData) (e : ℝ → ℝ)
    (he : Measurable e) (hb : ∀ᵐ o ∂μ, e (covariate o) ∈ Icc (0 : ℝ) 1) :
    (assignedFrom μ e).map Prod.fst = μ := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB]
  change (μ.bind (membershipAssignmentKernel e)) (Prod.fst ⁻¹' B) = μ B
  rw [Measure.bind_apply (hB.preimage measurable_fst)
    (membershipAssignmentKernel_measurable e he).aemeasurable]
  calc
    _ = ∫⁻ o, B.indicator 1 o ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hb] with o ho
      have hw : ENNReal.ofReal (e (covariate o)) +
          ENNReal.ofReal (1 - e (covariate o)) = 1 := by
        rw [← ENNReal.ofReal_add ho.1 (sub_nonneg.mpr ho.2)]
        simp
      simp only [membershipAssignmentKernel, Measure.add_apply, Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ (hB.preimage measurable_fst)]
      by_cases hoB : o ∈ B <;> simp [hoB, Set.indicator, hw]
    _ = μ B := by simp [lintegral_indicator, hB]

/-- A probability primitive marginal gives a probability assigned overlay.  Under [the displayed assumptions and inputs](hyp:e,he,hb), [the stated conclusion holds](goal). -/
-- @node: assignedFrom_isProbability
lemma assignedFrom_isProbability (μ : Measure FullData) [IsProbabilityMeasure μ]
    (e : ℝ → ℝ) (he : Measurable e)
    (hb : ∀ᵐ o ∂μ, e (covariate o) ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (assignedFrom μ e) := by
  constructor
  have h := congrArg (fun ν : Measure FullData => ν univ) (assignedFrom_map_fst μ e he hb)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    preimage_univ, measure_univ] using h

/-- The assignment event probability is the integral of its conditional instrument mass.  Under [the displayed assumptions and inputs](hyp:e,he,hb,B,hB,z), [the stated conclusion holds](goal). -/
-- @node: assignedFrom_instrument_event
lemma assignedFrom_instrument_event (μ : Measure FullData) (e : ℝ → ℝ)
    (he : Measurable e) (hb : ∀ o, e (covariate o) ∈ Icc (0 : ℝ) 1)
    (B : Set FullData) (hB : MeasurableSet B) (z : Bool) :
    (assignedFrom μ e {o | o.1 ∈ B ∧ o.2.1 = z}).toReal =
      ∫ o in B, (if z then e (covariate o) else 1 - e (covariate o)) ∂μ := by
  have hset : MeasurableSet {o : Assigned | o.1 ∈ B ∧ o.2.1 = z} :=
    (hB.preimage measurable_fst).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  have hnonneg : ∀ o : FullData,
      0 ≤ (if z then e (covariate o) else 1 - e (covariate o)) := by
    intro o
    cases z
    · exact sub_nonneg.mpr (hb o).2
    · exact (hb o).1
  change ((μ.bind (membershipAssignmentKernel e)) _).toReal = _
  rw [Measure.bind_apply hset (membershipAssignmentKernel_measurable e he).aemeasurable]
  have heq : (∫⁻ o, membershipAssignmentKernel e o
      {o | o.1 ∈ B ∧ o.2.1 = z} ∂μ) =
      ∫⁻ o in B, ENNReal.ofReal (if z then e (covariate o) else 1 - e (covariate o)) ∂μ := by
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro o
    cases z <;> by_cases ho : o ∈ B <;>
      simp [membershipAssignmentKernel, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hset, Set.indicator, ho]
  rw [heq]
  symm
  apply integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
  have hc : Measurable covariate := by unfold covariate; fun_prop
  cases z
  · exact (measurable_const.sub (he.comp hc)).aestronglyMeasurable
  · exact (he.comp hc).aestronglyMeasurable

/-- Primitive binary outcomes remain bounded after randomized assignment.  Under [the displayed assumptions and inputs](hyp:e,he,hb,hy), [the stated conclusion holds](goal). -/
-- @node: assignedFrom_outcome_bounds
lemma assignedFrom_outcome_bounds (μ : Measure FullData) (e : ℝ → ℝ)
    (he : Measurable e) (hb : ∀ᵐ o ∂μ, e (covariate o) ∈ Icc (0 : ℝ) 1)
    (hy : ∀ᵐ o ∂μ, outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ o ∂assignedFrom μ e, o.2.2.2 ∈ Icc (0 : ℝ) 1 := by
  have hmap := assignedFrom_map_fst μ e he hb
  rw [← hmap] at hy
  have hs := ae_of_ae_map measurable_fst.aemeasurable hy
  filter_upwards [hs, assignedFrom_consistency μ e he] with o ho hc
  rw [hc.2]
  cases hd : o.2.2.1 <;> simp [potentialOutcome, ho.1, ho.2]

/-- The primitive-law assignment construction satisfies consistency and randomization.  Under [the displayed assumptions and inputs](hyp:fS,fT,e,mass,hm,hm0,hsum,hS,he,hb,hpop), [the stated conclusion holds](goal). -/
-- @node: lawFromMass_assignment_conditions
lemma lawFromMass_assignment_conditions (fS fT e : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1)
    (hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (hsum : ∀ x, ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1)
    (hS : ((volume.restrict covariateSpace).withDensity
      (fun x => ENNReal.ofReal (fS x))) univ = 1)
    (he : Measurable e) (hb : ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hpop : populationLaw (lawFromMass fS fT e mass) true =
      primitivePopulation true fS mass) :
    ReceiptConsistency (lawFromMass fS fT e mass) ∧
    OutcomeConsistency (lawFromMass fS fT e mass) ∧
    InstrumentRandomization (lawFromMass fS fT e mass) := by
  let μ := primitivePopulation true fS mass
  have : IsProbabilityMeasure μ := ⟨by
    change primitivePopulation true fS mass univ = 1
    rw [primitivePopulation_univ true fS mass hm hm0 hsum, hS]⟩
  have heμ : ∀ᵐ o ∂μ, e (covariate o) ∈ Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun o => hb (covariate o))
  have hc := assignedFrom_consistency μ e he
  refine ⟨hc.mono (fun _ h => h.1), ⟨hc.mono (fun _ h => h.2), ?_⟩, ?_⟩
  · exact assignedFrom_outcome_bounds μ e he heμ
      (primitivePopulation_outcome_bounds true fS mass hm)
  · refine ⟨assignedFrom_isProbability μ e he heμ, ?_, ?_, ?_⟩
    · exact he.indicator measurableSet_Icc
    · rw [hpop]
      exact assignedFrom_map_fst μ e he heμ
    · intro B hB z
      rw [hpop]
      exact assignedFrom_instrument_event μ e he (fun o => hb (covariate o)) B hB z

/-- Both product-sample marginals and their independence follow from normalized channels.  Under [the displayed assumptions and inputs](hyp:fS,fT,e,mass,nS,nT), [the stated conclusion holds](goal). -/
-- @node: lawFromMass_sampling_conditions
lemma lawFromMass_sampling_conditions (fS fT e : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    [IsProbabilityMeasure (sourceObsLaw (lawFromMass fS fT e mass))]
    [IsProbabilityMeasure (targetXLaw (lawFromMass fS fT e mass))] (nS nT : ℕ) :
    SourceIid (lawFromMass fS fT e mass) nS nT ∧
    TargetIid (lawFromMass fS fT e mass) nS nT ∧
    SampleIndependence (lawFromMass fS fT e mass) nS nT := by
  have hd : dataLaw (lawFromMass fS fT e mass) nS nT =
      (Measure.pi (fun _ : Fin nS => sourceObsLaw (lawFromMass fS fT e mass))).prod
        (Measure.pi (fun _ : Fin nT => targetXLaw (lawFromMass fS fT e mass))) := rfl
  have hS : SourceIid (lawFromMass fS fT e mass) nS nT := by
    rw [SourceIid, hd, Measure.map_fst_prod]
    simp
  have hT : TargetIid (lawFromMass fS fT e mass) nS nT := by
    rw [TargetIid, hd, Measure.map_snd_prod]
    simp
  exact ⟨hS, hT, by rw [SampleIndependence, hS, hT, hd]⟩

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
