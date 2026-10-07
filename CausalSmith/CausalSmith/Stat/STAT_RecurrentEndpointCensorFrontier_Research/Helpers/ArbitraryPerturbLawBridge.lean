module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryPerturbRecurrenceBridge
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PerturbModelClass

/-! # Observed-law bridge for an arbitrary admissible perturbation -/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

set_option maxHeartbeats 0 in
/-- An admissible law with the prescribed marginals has the same observed law
as the explicit treatment perturbation built from an a.e.-equal measurable
nonnegative intensity. -/
lemma arbitraryPerturb_observedLaw_eq_explicit
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference) (hlambda0 : 0 < lambda0)
    (lam1 g : ℝ → ℝ)
    (hgmeas : Measurable g) (hgpos : ∀ t, 0 ≤ g t)
    (hfg : g =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] lam1)
    (Ppert : SubjectLaw)
    (hRandom : RandomAssignment Ppert) (hAssign : AssignmentLaw Ppert)
    (hPoisson : PoissonRecurrence Ppert) (hDeath : DeathHazard Ppert)
    (hRecurDeath : RecurrenceDeathIndependence Ppert)
    (hCensor : IndependentCensoring Ppert)
    (hp : Ppert.p = (SubjectLaw.baseline reference lambda0 d0 hd0).p)
    (hhazard : Ppert.hazard =
      (SubjectLaw.baseline reference lambda0 d0 hd0).hazard)
    (hcensor : Ppert.latent.map LatentSubject.censor =
      (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
        LatentSubject.censor)
    (hfalse : Ppert.lam false =
      (SubjectLaw.baseline reference lambda0 d0 hd0).lam false)
    (htrue : Ppert.lam true = lam1)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) g a)) :
    observedLaw Ppert = observedLaw
      (SubjectLaw.perturbTreatment
        (SubjectLaw.baseline reference lambda0 d0 hd0) g hfinite) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let Q := SubjectLaw.perturbTreatment Pbase g hfinite
  have hQprod := SubjectLaw.perturbTreatment_productIndependence Pbase g hfinite
  have hQdeath : DeathHazard Q :=
    SubjectLaw.perturbTreatment_deathHazard Pbase g hfinite
      (SubjectLaw.baseline_deathHazard reference lambda0 d0 hd0)
  have hPbaseAssign : AssignmentLaw Pbase :=
    SubjectLaw.baseline_assignmentLaw reference lambda0 d0 hd0 hAssignment
  have hQassign : AssignmentLaw Q := by
    simpa only [Q] using
      SubjectLaw.perturbTreatment_assignmentLaw Pbase g hfinite hPbaseAssign
  have hrecur : ∀ a : Arm,
      Ppert.latent.map (fun z : LatentSubject => z.recur a) =
        Q.latent.map (fun z : LatentSubject => z.recur a) :=
    arbitraryPerturb_recurrence_map_eq_explicit reference lambda0 d0 hd0
      hlambda0 lam1 g hgmeas hgpos hfg Ppert hPoisson hfalse htrue hfinite
  have hpQ : Ppert.p = Q.p := by
    calc
      Ppert.p = Pbase.p := by simpa [Pbase] using hp
      _ = Q.p := (perturbTreatment_p_eq_base Pbase g hfinite).symm
  have hhazardQ : Ppert.hazard = Q.hazard := by
    calc
      Ppert.hazard = Pbase.hazard := by simpa [Pbase] using hhazard
      _ = Q.hazard := (perturbTreatment_hazard_eq_base Pbase g hfinite).symm
  have hcensorQ : Ppert.latent.map LatentSubject.censor =
      Q.latent.map LatentSubject.censor := by
    calc
      Ppert.latent.map LatentSubject.censor =
          Pbase.latent.map LatentSubject.censor := by simpa [Pbase] using hcensor
      _ = Q.latent.map LatentSubject.censor :=
        (SubjectLaw.perturbTreatment_preserves_marginals Pbase g hfinite).2.2.symm
  exact observedLaw_eq_of_recur_arm_map_eq Ppert Q hRandom hQprod.1 hAssign
    hQassign hrecur hDeath hQdeath hRecurDeath hQprod.2.1 hCensor hQprod.2.2
    hpQ hhazardQ hcensorQ

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
