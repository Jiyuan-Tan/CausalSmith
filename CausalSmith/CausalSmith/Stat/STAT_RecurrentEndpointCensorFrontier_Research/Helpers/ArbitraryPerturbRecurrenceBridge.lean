module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryKLReduction

/-! # Recurrence marginal bridge for arbitrary perturbations -/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Treatment perturbation leaves the assignment probability field unchanged. -/
lemma perturbTreatment_p_eq_base
    (base : SubjectLaw) (g : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base g a)) :
    (SubjectLaw.perturbTreatment base g hfinite).p = base.p := by
  rfl

/-- Treatment perturbation leaves the death hazard field unchanged. -/
lemma perturbTreatment_hazard_eq_base
    (base : SubjectLaw) (g : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base g a)) :
    (SubjectLaw.perturbTreatment base g hfinite).hazard = base.hazard := by
  rfl

private lemma canonicalRecurrenceLawOf_eq_bridge
    (nu mu : Measure ℝ) [hnu : IsFiniteMeasure nu] [hmu : IsFiniteMeasure mu]
    (h : nu = mu) :
    @canonicalRecurrenceLawOf nu hnu = @canonicalRecurrenceLawOf mu hmu := by
  subst mu
  rfl

/-- The explicit treatment perturbation has the required armwise Poisson
recurrence laws when its treatment intensity is measurable and nonnegative. -/
lemma explicitPerturb_poissonRecurrence_of_measurable
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hlambda0 : 0 < lambda0) (g : ℝ → ℝ)
    (hgmeas : Measurable g) (hgpos : ∀ t, 0 ≤ g t)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) g a)) :
    PoissonRecurrence
      (SubjectLaw.perturbTreatment
        (SubjectLaw.baseline reference lambda0 d0 hd0) g hfinite) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let Q := SubjectLaw.perturbTreatment Pbase g hfinite
  apply SubjectLaw.perturbTreatment_poissonRecurrence Pbase g hfinite
  intro a
  cases a
  · have hb := SubjectLaw.baseline_poissonRecurrence reference lambda0 d0
      hlambda0.le hd0 false
    simpa [Q, Pbase, SubjectLaw.perturbTreatment] using
      (And.intro hb.1 hb.2.1)
  · exact ⟨hgmeas.aemeasurable, Filter.Eventually.of_forall hgpos⟩

set_option maxHeartbeats 0 in
/-- Full recurrence-configuration marginals of an admissible perturbation
agree with those of the explicit perturbation built from an a.e.-equal
intensity version. -/
lemma arbitraryPerturb_recurrence_map_eq_explicit
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hlambda0 : 0 < lambda0) (lam1 g : ℝ → ℝ)
    (hgmeas : Measurable g) (hgpos : ∀ t, 0 ≤ g t)
    (hfg : g =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] lam1)
    (Ppert : SubjectLaw) (hPoisson : PoissonRecurrence Ppert)
    (hfalse : Ppert.lam false =
      (SubjectLaw.baseline reference lambda0 d0 hd0).lam false)
    (htrue : Ppert.lam true = lam1)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) g a)) :
    ∀ a : Arm,
      Ppert.latent.map (fun z : LatentSubject => z.recur a) =
        (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) g hfinite).latent.map
            (fun z : LatentSubject => z.recur a) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let Q := SubjectLaw.perturbTreatment Pbase g hfinite
  have hQpois : PoissonRecurrence Q :=
    explicitPerturb_poissonRecurrence_of_measurable reference lambda0 d0 hd0
      hlambda0 g hgmeas hgpos hfinite
  intro a
  rcases (hPoisson a).2.2 with ⟨hfinP, hmapP⟩
  rcases (hQpois a).2.2 with ⟨hfinQ, hmapQ⟩
  rw [hmapP, hmapQ]
  have hi : recurrenceIntensity Ppert a = recurrenceIntensity Q a := by
    cases a
    · change
        (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
            (fun t => ENNReal.ofReal (Ppert.lam false t)) =
          (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
            (fun t => ENNReal.ofReal (Q.lam false t))
      rw [hfalse]
      congr 1
    · apply recurrenceIntensity_eq_of_ae_eq
      filter_upwards [hfg] with t ht
      change Ppert.lam true t = Q.lam true t
      rw [htrue]
      change lam1 t = (if true then g else Pbase.lam false) t
      exact ht.symm
  exact canonicalRecurrenceLawOf_eq_bridge _ _ hi

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
