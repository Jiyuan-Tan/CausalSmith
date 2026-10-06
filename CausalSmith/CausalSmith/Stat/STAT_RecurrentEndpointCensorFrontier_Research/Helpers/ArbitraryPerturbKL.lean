module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryKLReduction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryPerturbLawBridge
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DirectionAnalytics
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # Full-history KL transport for arbitrary admissible perturbations -/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- keep: verified i.i.d. tensorization isolates the unresolved one-subject stopped-history KL bridge
/-- Exact finite-sample tensorization for two recurrent-history laws once the
one-subject observed likelihood ratio is integrable.  This isolates the
point-process calculation needed by the lower-bound construction from the
routine i.i.d. product step. -/
lemma sampleLaw_klDiv_tensorization (P Q : SubjectLaw) (n : ℕ)
    (hac : observedLaw P ≪ observedLaw Q)
    (hint : Integrable
      (llr (observedLaw P) (observedLaw Q))
      (observedLaw P)) :
    InformationTheory.klDiv (sampleLaw P n) (sampleLaw Q n) < ⊤ ∧
      (InformationTheory.klDiv (sampleLaw P n) (sampleLaw Q n)).toReal =
        (n : ℝ) *
          (InformationTheory.klDiv (observedLaw P) (observedLaw Q)).toReal := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure Q.latent := ⟨Q.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map P.observe_aemeasurable
  letI : IsProbabilityMeasure (observedLaw Q) :=
    Measure.isProbabilityMeasure_map Q.observe_aemeasurable
  have hprod := Causalean.Mathlib.InformationTheory.productKL_tensorization
    n (observedLaw P) (observedLaw Q) hac hint
  constructor
  · exact lt_top_iff_ne_top.mpr hprod.product_ne_top
  · simpa only [sampleLaw] using
      Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
        n (observedLaw P) (observedLaw Q) hac hint

/-- Equality of one-subject observed laws propagates to every i.i.d. sample
law.  This is the final transport needed after reducing an arbitrary admissible
perturbation to the explicit product constructor. -/
lemma sampleLaw_eq_of_observedLaw_eq {P Q : SubjectLaw}
    (h : observedLaw P = observedLaw Q) (n : ℕ) :
    sampleLaw P n = sampleLaw Q n := by
  unfold sampleLaw
  rw [h]

/-- Replacing the left law by an observationally equivalent subject law does
not change its sample divergence from a fixed reference law. -/
lemma sampleLaw_klDiv_eq_of_observedLaw_eq_left {P Q R : SubjectLaw}
    (h : observedLaw P = observedLaw Q) (n : ℕ) :
    InformationTheory.klDiv (sampleLaw P n) (sampleLaw R n) =
      InformationTheory.klDiv (sampleLaw Q n) (sampleLaw R n) := by
  rw [sampleLaw_eq_of_observedLaw_eq h n]

/-- The universal KL clause for an arbitrary admissible perturbation of the
explicit constant baseline. -/
lemma arbitraryPerturb_sampleKL_weighted
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference) (hlambda0 : 0 < lambda0)
    (n : ℕ) (lam1 : ℝ → ℝ)
    (hlam1_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < lam1 t)
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
    (hweighted : IntervalIntegrable (fun t : ℝ =>
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
      volume 0 1) :
    InformationTheory.klDiv (sampleLaw Ppert n)
        (sampleLaw (SubjectLaw.baseline reference lambda0 d0 hd0) n) < ⊤ ∧
      (InformationTheory.klDiv (sampleLaw Ppert n)
        (sampleLaw (SubjectLaw.baseline reference lambda0 d0 hd0) n)).toReal =
        (n : ℝ) * (SubjectLaw.baseline reference lambda0 d0 hd0).p true *
          ∫ t in (0 : ℝ)..1,
            survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
              retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
              (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  have hf : AEMeasurable lam1 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    simpa only [htrue] using (hPoisson true).1
  let g := nonnegativeMeasurableVersion lam1 hf
  have hgmeas : Measurable g := measurable_nonnegativeMeasurableVersion lam1 hf
  have hgpos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ g t := fun t _ =>
    nonnegativeMeasurableVersion_nonneg lam1 hf t
  have hfg : g =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] lam1 :=
    nonnegativeMeasurableVersion_ae_eq lam1 hf (by
      simpa only [htrue] using (hPoisson true).2.1)
  have hfinite : ∀ a : Arm, IsFiniteMeasure (treatmentPerturbIntensity Pbase g a) :=
    explicitPerturb_finite_of_poisson Ppert Pbase lam1 g hPoisson hfalse htrue hfg.symm
  let Q := SubjectLaw.perturbTreatment Pbase g hfinite
  have hobs : observedLaw Ppert = observedLaw Q := by
    apply arbitraryPerturb_observedLaw_eq_explicit reference lambda0 d0 hd0
      hAssignment hlambda0 lam1 g hgmeas
      (fun t => nonnegativeMeasurableVersion_nonneg lam1 hf t) hfg Ppert
      hRandom hAssign hPoisson hDeath hRecurDeath hCensor hp hhazard hcensor
      hfalse htrue hfinite
  have hwg : IntervalIntegrable (fun t : ℝ =>
      survival Pbase true t * retention Pbase true t *
        (g t * Real.log (g t / lambda0) - g t + lambda0)) volume 0 1 := by
    have hweightedBase : IntervalIntegrable (fun t : ℝ =>
        survival Pbase true t * retention Pbase true t *
          (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
        volume 0 1 := by simpa only [Pbase] using hweighted
    apply hweightedBase.congr_ae
    have hfgI : g =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) 1)] lam1 := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfg
    filter_upwards [hfgI] with t ht
    simp [ht]
  have hKL := SubjectLaw.baselinePerturb_sampleKL_weighted reference lambda0 d0
    hd0 hAssignment g hgmeas hgpos hlambda0 hfinite hwg n
  rw [sampleLaw_klDiv_eq_of_observedLaw_eq_left hobs n]
  refine ⟨hKL.1, hKL.2.trans ?_⟩
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hfgI : g =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) 1)] lam1 := by
    simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfg
  filter_upwards [hfgI] with t ht
  simp [ht]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
