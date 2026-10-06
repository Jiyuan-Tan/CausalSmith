module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MidpointBaseline

/-!
# Model-class closure under a treatment-arm recurrence perturbation

This file packages the structural product-construction lemmas from `Basic`
into a reusable model-class closure theorem.  The caller only has to supply
the new recurrence intensity's analytic conditions.
-/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

lemma SubjectLaw.perturbTreatment_congr_base
    (base₁ base₂ : SubjectLaw) (hbase : base₁ = base₂) (lam1 : ℝ → ℝ)
    (hfinite₁ : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base₁ lam1 a))
    (hfinite₂ : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base₂ lam1 a)) :
    SubjectLaw.perturbTreatment base₁ lam1 hfinite₁ =
      SubjectLaw.perturbTreatment base₂ lam1 hfinite₂ := by
  subst base₂
  rfl

/-- A treatment recurrence perturbation preserves censoring retention. -/
lemma SubjectLaw.perturbTreatment_retention_eq
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a))
    (a : Arm) (t : ℝ) :
    retention (SubjectLaw.perturbTreatment base lam1 hfinite) a t =
      retention base a t := by
  let P := SubjectLaw.perturbTreatment base lam1 hfinite
  have hmarg : P.latent.map LatentSubject.censor =
      base.latent.map LatentSubject.censor :=
    (SubjectLaw.perturbTreatment_preserves_marginals base lam1 hfinite).2.2
  have hs : MeasurableSet {q : Arm → ENNReal | ENNReal.ofReal t ≤ q a} :=
    measurableSet_le measurable_const (measurable_pi_apply a)
  have hpert := Measure.map_apply measurable_latentSubject_censorFamily hs
    (μ := P.latent)
  have hbase := Measure.map_apply measurable_latentSubject_censorFamily hs
    (μ := base.latent)
  unfold retention
  simp only [measureReal_def]
  calc
    _ = (P.latent.map LatentSubject.censor
          {q | ENNReal.ofReal t ≤ q a}).toReal :=
      congrArg ENNReal.toReal hpert.symm
    _ = (base.latent.map LatentSubject.censor
          {q | ENNReal.ofReal t ≤ q a}).toReal := by rw [hmarg]
    _ = _ := congrArg ENNReal.toReal hbase

/-- The product perturbation preserves the assignment-law atom. -/
lemma SubjectLaw.perturbTreatment_assignmentLaw
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a))
    (hbase : AssignmentLaw base) :
    AssignmentLaw (SubjectLaw.perturbTreatment base lam1 hfinite) := by
  let P := SubjectLaw.perturbTreatment base lam1 hfinite
  have hmarg : P.latent.map LatentSubject.treatment =
      base.latent.map LatentSubject.treatment :=
    (SubjectLaw.perturbTreatment_preserves_marginals base lam1 hfinite).1
  intro a
  have hs : MeasurableSet ({a} : Set Arm) := measurableSet_singleton a
  have hpert := Measure.map_apply measurable_latentSubject_treatment hs
    (μ := P.latent)
  have hbaseMap := Measure.map_apply measurable_latentSubject_treatment hs
    (μ := base.latent)
  change (P.latent {z | z.treatment = a}).toReal = P.p a
  calc
    _ = (P.latent.map LatentSubject.treatment {a}).toReal :=
      congrArg ENNReal.toReal hpert.symm
    _ = (base.latent.map LatentSubject.treatment {a}).toReal := by rw [hmarg]
    _ = (base.latent {z | z.treatment = a}).toReal :=
      congrArg ENNReal.toReal hbaseMap
    _ = base.p a := hbase a
    _ = P.p a := rfl

/-- Closure of the full model class under the explicit treatment-arm
recurrence perturbation.  All non-recurrence atoms are inherited from the
base law through exact marginal preservation. -/
lemma SubjectLaw.perturbTreatment_modelClass
    (c : ClassConstants) (base : SubjectLaw) (hbase : ModelClass c base)
    (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a))
    (hregular : ∀ a : Arm,
      AEMeasurable (if a then lam1 else base.lam false)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
          0 ≤ (if a then lam1 else base.lam false) t))
    (hbounds : ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c.lambdaMin ≤ (if a then lam1 else base.lam false) t ∧
        (if a then lam1 else base.lam false) t ≤ c.lambdaMax)
    (hholder : ∀ a : Arm,
      HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda
        (if a then lam1 else base.lam false)) :
    ModelClass c (SubjectLaw.perturbTreatment base lam1 hfinite) := by
  let P := SubjectLaw.perturbTreatment base lam1 hfinite
  have hprod := SubjectLaw.perturbTreatment_productIndependence base lam1 hfinite
  have hret : ∀ a t, retention P a t = retention base a t :=
    SubjectLaw.perturbTreatment_retention_eq base lam1 hfinite
  change ModelClass c P
  refine
    { iid := ?_
      randomAssignment := hprod.1
      assignmentLaw := SubjectLaw.perturbTreatment_assignmentLaw base lam1 hfinite
        hbase.assignmentLaw
      treatmentOverlap := ?_
      poissonRecurrence := SubjectLaw.perturbTreatment_poissonRecurrence
        base lam1 hfinite hregular
      deathHazard := SubjectLaw.perturbTreatment_deathHazard base lam1 hfinite
        hbase.deathHazard
      recurrenceDeathIndependence := hprod.2.1
      independentCensoring := hprod.2.2
      recurrenceBounds := ?_
      deathBounds := ?_
      recurrenceHolder := ?_
      deathHolder := ?_
      endpointRetention := ?_
      tailEnvelopeSmall := hbase.tailEnvelopeSmall
      endpointCoefficientBounds := ?_
      interiorRetention := ?_ }
  · intro n
    rfl
  · intro a
    exact hbase.treatmentOverlap a
  · intro a t ht
    change c.lambdaMin ≤ (if a then lam1 else base.lam false) t ∧
      (if a then lam1 else base.lam false) t ≤ c.lambdaMax
    exact hbounds a t ht
  · intro a t ht
    exact hbase.deathBounds a t ht
  · intro a
    change HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda
      (if a then lam1 else base.lam false)
    exact hholder a
  · intro a
    exact hbase.deathHolder a
  · intro a x hx hx0
    rw [hret]
    exact hbase.endpointRetention a x hx hx0
  · intro a
    exact hbase.endpointCoefficientBounds a
  · intro a t ht
    rw [hret]
    exact hbase.interiorRetention a t ht

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
