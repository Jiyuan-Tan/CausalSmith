module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryPerturbKL
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DirectionAnalytics
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.EndpointKLWitness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.TargetSeparationTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DirectionTargetSeparation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedFullIdentification
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Endpoint perturbations of the full recurrent history

Smooth cutoff data give the supercritical bump and critical multiscale
directions. The lower-bound lemma retains the complete observed-history laws.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: lem:full-history-directions
lemma full_history_directions (c : ClassConstants)
    (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) :
    ∃ Pbase : SubjectLaw, ModelClass c Pbase ∧
      Pbase.p = P₀.p ∧
      Pbase.latent.map LatentSubject.censor =
        P₀.latent.map LatentSubject.censor ∧
      (∃ lambda0 d₀ : ℝ,
        c.lambdaMin < lambda0 ∧ lambda0 < c.lambdaMax ∧
        c.dMin < d₀ ∧ d₀ < c.dMax ∧
        (∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Pbase.lam a t = lambda0 ∧ Pbase.hazard a t = d₀) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ lam1 : ℝ → ℝ,
          (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < lam1 t) →
          ∀ Ppert : SubjectLaw,
            RandomAssignment Ppert → AssignmentLaw Ppert →
            PoissonRecurrence Ppert → DeathHazard Ppert →
            RecurrenceDeathIndependence Ppert → IndependentCensoring Ppert →
            Ppert.p = Pbase.p → Ppert.hazard = Pbase.hazard →
            Ppert.latent.map LatentSubject.censor =
              Pbase.latent.map LatentSubject.censor →
            Ppert.lam false = Pbase.lam false → Ppert.lam true = lam1 →
            IntervalIntegrable (fun t : ℝ =>
              survival Pbase true t * retention Pbase true t *
                (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
              volume 0 1 →
            InformationTheory.klDiv (sampleLaw Ppert n)
              (sampleLaw Pbase n) < ⊤ ∧
            (InformationTheory.klDiv (sampleLaw Ppert n)
              (sampleLaw Pbase n)).toReal =
              (n : ℝ) * Pbase.p true *
                ∫ t in (0 : ℝ)..1,
                  survival Pbase true t * retention Pbase true t *
                    (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))) ∧
    ∃ u₀ : ℝ, 0 < u₀ ∧
      ∀ u : ℝ, 0 < u → u ≤ u₀ →
        (c.kappa > 1 → ∃ K δ : ℝ, ∃ N : ℕ,
          0 < K ∧ 0 < δ ∧ 3 ≤ N ∧
          ∀ n : ℕ, N ≤ n →
            ∃ P₁ : SubjectLaw, ModelClass c P₁ ∧
              P₁.p = Pbase.p ∧ P₁.hazard = Pbase.hazard ∧
              P₁.lam false = Pbase.lam false ∧
              P₁.latent.map LatentSubject.censor =
                Pbase.latent.map LatentSubject.censor ∧
              (∀ a t, retention P₁ a t = retention Pbase a t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                P₁.lam true t = Pbase.lam true t +
                  endpointDirection c cut u
                    ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t) ∧
              (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw Pbase n)).toReal =
                (n : ℝ) * Pbase.p true *
                  ∫ t in (0 : ℝ)..1,
                    survival Pbase true t * retention Pbase true t *
                      (P₁.lam true t * Real.log
                        (P₁.lam true t / Pbase.lam true t) -
                        P₁.lam true t + Pbase.lam true t) ∧
              (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw Pbase n)).toReal ≤ K ∧
              δ * (n : ℝ) ^ (-(c.beta + 1) /
                (2 * c.beta + c.kappa + 1)) ≤
                |causalTarget P₁ - causalTarget Pbase|) ∧
        (c.kappa = 1 → ∃ K δ : ℝ, ∃ N : ℕ,
          0 < K ∧ 0 < δ ∧ 3 ≤ N ∧
          ∀ n : ℕ, N ≤ n →
            ∃ P₁ : SubjectLaw, ModelClass c P₁ ∧
              P₁.p = Pbase.p ∧ P₁.hazard = Pbase.hazard ∧
              P₁.lam false = Pbase.lam false ∧
              P₁.latent.map LatentSubject.censor =
                Pbase.latent.map LatentSubject.censor ∧
              (∀ a t, retention P₁ a t = retention Pbase a t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                P₁.lam true t = Pbase.lam true t + criticalDirection c cut u n t) ∧
              (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw Pbase n)).toReal =
                (n : ℝ) * Pbase.p true *
                  ∫ t in (0 : ℝ)..1,
                    survival Pbase true t * retention Pbase true t *
                      (P₁.lam true t * Real.log
                        (P₁.lam true t / Pbase.lam true t) -
                        P₁.lam true t + Pbase.lam true t) ∧
              (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw Pbase n)).toReal ≤ K ∧
              δ * Real.sqrt (Real.log n / n) ≤
                |causalTarget P₁ - causalTarget Pbase|) := by
  let Pbase := midpointBaseline c P₀
  let lambda0 := midpointLambda c
  let d₀ := midpointDeath c
  have hbase := midpointBaseline_spec c P₀ hP₀
  have hbaseModel : ModelClass c Pbase := hbase.1
  have hmeanBase := hbaseModel.causalTarget_eq_survival_intensity_contrast
  have hintBase : IntervalIntegrable (fun t : ℝ =>
      survival Pbase true t * Pbase.lam true t -
        survival Pbase false t * Pbase.lam false t) volume 0 1 :=
    (hbaseModel.armMean_integrand_intervalIntegrable true).sub
      (hbaseModel.armMean_integrand_intervalIntegrable false)
  have hkl : ∀ n : ℕ, 1 ≤ n → ∀ lam1 : ℝ → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < lam1 t) →
      ∀ Ppert : SubjectLaw,
        RandomAssignment Ppert → AssignmentLaw Ppert →
        PoissonRecurrence Ppert → DeathHazard Ppert →
        RecurrenceDeathIndependence Ppert → IndependentCensoring Ppert →
        Ppert.p = Pbase.p → Ppert.hazard = Pbase.hazard →
        Ppert.latent.map LatentSubject.censor =
          Pbase.latent.map LatentSubject.censor →
        Ppert.lam false = Pbase.lam false → Ppert.lam true = lam1 →
        IntervalIntegrable (fun t : ℝ =>
          survival Pbase true t * retention Pbase true t *
            (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
          volume 0 1 →
        InformationTheory.klDiv (sampleLaw Ppert n) (sampleLaw Pbase n) < ⊤ ∧
        (InformationTheory.klDiv (sampleLaw Ppert n)
          (sampleLaw Pbase n)).toReal =
          (n : ℝ) * Pbase.p true *
            ∫ t in (0 : ℝ)..1,
              survival Pbase true t * retention Pbase true t *
                (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0) := by
    intro n hn lam1 hlam Ppert hr ha hp hd hi hc hprob hh hg hf ht hw
    have hbaseeq : Pbase = SubjectLaw.baseline P₀ (midpointLambda c)
        (midpointDeath c) (midpointDeath_pos c) :=
      midpointBaseline_eq_baseline c P₀
    rw [hbaseeq] at hprob hh hg hf hw ⊢
    exact arbitraryPerturb_sampleKL_weighted P₀ (midpointLambda c) (midpointDeath c)
        (midpointDeath_pos c) hP₀.assignmentLaw
        (c.lambdaMin_pos.trans (midpoint_strict_bounds c).1)
        n lam1 hlam Ppert hr ha hp hd hi hc hprob hh hg hf ht hw
  have hendpoint : ∀ u : ℝ, 0 < u → u ≤ endpointModelRadius c cut →
      c.kappa > 1 → ∃ K δ : ℝ, ∃ N : ℕ,
        0 < K ∧ 0 < δ ∧ 3 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          ∃ P₁ : SubjectLaw, ModelClass c P₁ ∧
            P₁.p = Pbase.p ∧ P₁.hazard = Pbase.hazard ∧
            P₁.lam false = Pbase.lam false ∧
            P₁.latent.map LatentSubject.censor =
              Pbase.latent.map LatentSubject.censor ∧
            (∀ a t, retention P₁ a t = retention Pbase a t) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1,
              P₁.lam true t = Pbase.lam true t +
                endpointDirection c cut u
                  ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t) ∧
            (InformationTheory.klDiv (sampleLaw P₁ n)
              (sampleLaw Pbase n)).toReal =
                (n : ℝ) * Pbase.p true *
                  ∫ t in (0 : ℝ)..1,
                    survival Pbase true t * retention Pbase true t *
                      (P₁.lam true t * Real.log
                        (P₁.lam true t / Pbase.lam true t) -
                        P₁.lam true t + Pbase.lam true t) ∧
            (InformationTheory.klDiv (sampleLaw P₁ n)
              (sampleLaw Pbase n)).toReal ≤ K ∧
            δ * (n : ℝ) ^ (-(c.beta + 1) /
              (2 * c.beta + c.kappa + 1)) ≤
              |causalTarget P₁ - causalTarget Pbase| := by
    intro u hu hur _
    obtain ⟨K, N, hK, hN, hwitness⟩ :=
      exists_endpointPerturb_KL_witnesses c P₀ hP₀ cut hu hur
    let δ := midpointSurvivalFloor c P₀ * u * endpointBumpMass c cut
    have hone : 1 ≤ (1 : ℕ) := by omega
    have hδ : 0 < δ :=
      (endpointDirection_integral_rate_lower c P₀ cut hu hone).1
    refine ⟨K, δ, N, hK, hδ, hN, ?_⟩
    intro n hn
    obtain ⟨P₁, hm, hp, hh, hf, hc, hr, ht, hkeq, hkbound⟩ := hwitness n hn
    refine ⟨P₁, hm, hp, hh, hf, hc, hr, ht, hkeq, hkbound, ?_⟩
    have hn1 : 1 ≤ n := by omega
    have htarget := endpoint_causalTarget_sub_eq_integral c P₁ Pbase cut u
      (endpointBandwidth c n)
      hm.causalTarget_eq_survival_intensity_contrast hmeanBase
      ((hm.armMean_integrand_intervalIntegrable true).sub
        (hm.armMean_integrand_intervalIntegrable false)) hintBase hh hf
      (by simpa only [endpointBandwidth_eq] using ht)
    rw [htarget]
    exact (endpointDirection_integral_rate_lower c P₀ cut hu hn1).2.trans
      (le_abs_self _)
  refine ⟨Pbase, hbaseModel, hbase.2.1, hbase.2.2.1,
    ⟨lambda0, d₀, hbase.2.2.2.1, hbase.2.2.2.2.1,
      hbase.2.2.2.2.2.1, hbase.2.2.2.2.2.2.1,
      hbase.2.2.2.2.2.2.2, hkl⟩, ?_⟩
  by_cases hk : c.kappa = 1
  · obtain ⟨ucr, hucr, hcrit⟩ :=
      exists_criticalPerturb_KL_witnesses c P₀ hP₀ cut hk
    let u₀ := min (endpointModelRadius c cut) ucr
    refine ⟨u₀, lt_min (endpointModelRadius_pos c cut) hucr, ?_⟩
    intro u hu hu₀
    constructor
    · exact hendpoint u hu (hu₀.trans (min_le_left _ _))
    · intro _
      obtain ⟨K, N, hK, hN, hwitness⟩ :=
        hcrit u hu (hu₀.trans (min_le_right _ _))
      obtain ⟨δ, Nsep, hδ, hNsep, hsep⟩ :=
        exists_criticalDirection_integral_rate_lower c P₀ cut hu
      refine ⟨K, δ, max N Nsep, hK, hδ, le_trans hN (le_max_left _ _), ?_⟩
      intro n hn
      obtain ⟨P₁, hm, hp, hh, hf, hc, hr, ht, hkeq, hkbound⟩ :=
        hwitness n ((le_max_left _ _).trans hn)
      refine ⟨P₁, hm, hp, hh, hf, hc, hr, ht, hkeq, hkbound, ?_⟩
      have htarget := critical_causalTarget_sub_eq_integral c P₁ Pbase cut u n
        hm.causalTarget_eq_survival_intensity_contrast hmeanBase
        ((hm.armMean_integrand_intervalIntegrable true).sub
          (hm.armMean_integrand_intervalIntegrable false)) hintBase hh hf ht
      rw [htarget]
      exact (hsep n ((le_max_right _ _).trans hn)).trans (le_abs_self _)
  · refine ⟨endpointModelRadius c cut, endpointModelRadius_pos c cut, ?_⟩
    intro u hu hu₀
    exact ⟨hendpoint u hu hu₀, fun h => (hk h).elim⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
