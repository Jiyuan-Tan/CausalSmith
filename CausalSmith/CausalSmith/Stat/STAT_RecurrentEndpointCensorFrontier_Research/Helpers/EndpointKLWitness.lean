module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.EndpointWitness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.WitnessConditions
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryKLReduction

/-! # Endpoint alternatives with uniformly bounded sample KL -/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Every fixed small endpoint amplitude produces rate-tuned alternatives in
the model class whose full-history sample KL is uniformly bounded. -/
-- @node: exists_endpointPerturb_KL_witnesses_quadratic
lemma exists_endpointPerturb_KL_witnesses_quadratic
    (c : ClassConstants) (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ endpointModelRadius c cut) :
    let Pbase := midpointBaseline c P₀
    ∃ K : ℝ, ∃ N : ℕ, 0 < K ∧ K = ((3 / 2 : ℝ) * c.gMax *
        (endpointBumpBound c cut ^ 2 / midpointLambda c)) * u ^ 2 ∧ 3 ≤ N ∧
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
            (sampleLaw Pbase n)).toReal ≤ K := by
  dsimp only
  let lambda0 := midpointLambda c
  let d0 := midpointDeath c
  let Pbase := midpointBaseline c P₀
  let A := (3 / 2 : ℝ) * c.gMax *
    ((|u| * endpointBumpBound c cut) ^ 2 / lambda0)
  have hlambda0 : 0 < lambda0 :=
    lt_trans c.lambdaMin_pos (midpoint_strict_bounds c).1
  have hA : 0 < A := by
    dsimp [A]
    have hg : 0 < c.gMax := lt_trans c.gMin_pos c.gMin_lt
    have huabs : 0 < |u| := abs_pos.mpr hu0.ne'
    have hB : 0 < endpointBumpBound c cut := endpointBumpBound_pos c cut
    have hsq : 0 < (|u| * endpointBumpBound c cut) ^ 2 := by positivity
    exact mul_pos (mul_pos (by norm_num) hg) (div_pos hsq hlambda0)
  rcases exists_endpointBandwidth_eventually_le_x0 c with ⟨N, hN3, hNx0⟩
  have hAeq : A = ((3 / 2 : ℝ) * c.gMax *
      (endpointBumpBound c cut ^ 2 / midpointLambda c)) * u ^ 2 := by
    dsimp [A, lambda0]
    rw [mul_pow, sq_abs]
    ring
  refine ⟨A, N, hA, hAeq, hN3, ?_⟩
  intro n hnN
  have hn1 : 1 ≤ n := le_trans (by omega) hnN
  let h := endpointBandwidth c n
  have hh0 : 0 < h := endpointBandwidth_pos c hn1
  have hh1 : h ≤ 1 := endpointBandwidth_le_one c hn1
  have hhx0 : h ≤ c.x0 := hNx0 n hnN
  have hconditions := endpointDirection_rate_model_conditions c cut hu0 hu hn1
  let lam1 := fun t : ℝ => midpointLambda c + endpointDirection c cut u
    ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t
  have hband : ∀ t : ℝ, c.lambdaMin ≤ lam1 t ∧ lam1 t ≤ c.lambdaMax := by
    intro t
    simpa [lam1] using hconditions.1 t
  have hadd : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < lam1 t := by
    intro t ht
    exact c.lambdaMin_pos.trans_le (hband t).1
  rcases exists_endpointPerturb_modelClass c P₀ hP₀ cut hu0 hu hn1 with
    ⟨hfinite, hmodel, hp, hhazard, hfalse, hcensor, hret, htrue⟩
  have hPbase : Pbase = SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c) := by
    simpa [Pbase, lambda0, d0] using midpointBaseline_eq_baseline c P₀
  have hfiniteLocal : ∀ a : Arm,
      IsFiniteMeasure (treatmentPerturbIntensity Pbase lam1 a) := by
    simpa [Pbase, lam1] using hfinite
  have hfiniteBase : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) lam1 a) := by
    simpa [hPbase] using hfiniteLocal
  let P₁ := SubjectLaw.perturbTreatment (midpointBaseline c P₀) lam1 hfinite
  let Q := SubjectLaw.perturbTreatment
    (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) lam1 hfiniteBase
  have hP₁Q : P₁ = Q := by
    exact SubjectLaw.perturbTreatment_congr_base _ _
      (midpointBaseline_eq_baseline c P₀) lam1 hfinite hfiniteBase
  have hmodel1 : ModelClass c P₁ := by
    simpa [P₁, lam1] using hmodel
  have hlamMeas : Measurable lam1 := by
    change Measurable ((fun _ : ℝ => midpointLambda c) +
      endpointDirection c cut u
        ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))))
    simpa only [h, endpointBandwidth_eq] using
      (continuous_const.add
        (endpointDirection_continuous c cut u h hh0.ne')).measurable
  have hweighted : IntervalIntegrable
      (weightedPoissonCost Pbase true lambda0 (endpointDirection c cut u h))
      volume 0 1 := by
    rw [hPbase]
    exact endpoint_weightedPoissonCost_intervalIntegrable c P₀ lambda0 d0
      (midpointDeath_pos c) cut hlambda0 hh0 (fun t ht => by
        simpa [lam1, h, endpointBandwidth_eq] using hadd t ht)
  have hKL := SubjectLaw.baselinePerturb_sampleKL_weighted
    P₀ lambda0 d0 (midpointDeath_pos c) hP₀.assignmentLaw lam1 hlamMeas
    (fun t ht => (hadd t ⟨ht.1.le, ht.2⟩).le) hlambda0 hfiniteBase (by
      rw [show (fun t : ℝ =>
          survival (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true t *
            retention (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true t *
            (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)) =
          weightedPoissonCost
            (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true lambda0
            (endpointDirection c cut u h) by
        funext t
        rw [weightedPoissonCost_apply]
        simp only [lam1, lambda0, h, endpointBandwidth_eq]]
      simpa only [hPbase] using hweighted) n
  have hI := endpoint_weightedPoissonCost_integral_le c P₀ lambda0 d0
    (midpointDeath_pos c) (by
      simpa [Pbase, midpointBaseline_eq_baseline] using
        (midpointBaseline_modelClass c P₀ hP₀)) cut hlambda0 hh0 hh1 hhx0
    (fun t ht => by simpa [lam1, h, endpointBandwidth_eq] using hadd t ht) (by
      simpa [hPbase, lam1, h, endpointBandwidth_eq] using hweighted)
  have hI' : ∫ t in (0 : ℝ)..1,
      weightedPoissonCost Pbase true lambda0 (endpointDirection c cut u h) t ≤
        A * h ^ (2 * c.beta + c.kappa + 1) := by
    rw [hPbase]
    simpa [A] using hI
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..1,
      weightedPoissonCost Pbase true lambda0 (endpointDirection c cut u h) t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have hw := SubjectLaw.baseline_survival_mul_retention_mem_unitInterval
      P₀ lambda0 d0 (midpointDeath_pos c) (a := true) (t := t) ht.1
    have hc := poissonIntensityCost_nonneg (lam1 t) lambda0
      (hadd t ht).le hlambda0
    rw [weightedPoissonCost_apply]
    exact mul_nonneg (by simpa [hPbase] using hw.1)
      (by simpa [lam1, h, endpointBandwidth_eq] using hc)
  have hp1 : Pbase.p true ≤ 1 := by
    rw [(midpointBaseline_spec c P₀ hP₀).2.1]
    rw [← hP₀.assignmentLaw true]
    calc
      P₀.latent.real {z | z.treatment = true} ≤ P₀.latent.real Set.univ := by
        exact measureReal_mono (Set.subset_univ _) (by
          simpa [P₀.prob] using ENNReal.one_ne_top)
      _ = 1 := by simp [measureReal_def, P₀.prob]
  have hsample : (n : ℝ) * Pbase.p true *
      (∫ t in (0 : ℝ)..1,
        weightedPoissonCost Pbase true lambda0 (endpointDirection c cut u h) t) ≤ A := by
    apply endpoint_sampleKL_factor_le c hn1 hp1 hI0
    simpa [h, endpointBandwidth_eq] using hI'
  refine ⟨P₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hmodel1
  · simpa [P₁, Pbase, lam1] using hp
  · simpa [P₁, Pbase, lam1] using hhazard
  · simpa [P₁, Pbase, lam1] using hfalse
  · simpa [P₁, Pbase, lam1] using hcensor
  · simpa [P₁, Pbase, lam1] using hret
  · simpa [P₁, Pbase, lam1] using htrue
  · rw [hP₁Q, midpointBaseline_eq_baseline c P₀]
    simpa [Q, SubjectLaw.perturbTreatment, SubjectLaw.baseline, lam1,
      lambda0, h, endpointBandwidth_eq] using hKL.2
  · rw [hP₁Q, midpointBaseline_eq_baseline c P₀, hKL.2]
    have hsampleBase : (n : ℝ) *
        (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)).p true *
        (∫ t in (0 : ℝ)..1,
          weightedPoissonCost
            (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true
            lambda0 (endpointDirection c cut u h) t) ≤ A := by
      simpa [hPbase] using hsample
    simpa [lam1, lambda0, h, endpointBandwidth_eq,
      weightedPoissonCost_apply] using hsampleBase

/-- Forget the explicit quadratic coefficient while retaining the original witness interface. -/
-- @node: exists_endpointPerturb_KL_witnesses
lemma exists_endpointPerturb_KL_witnesses
    (c : ClassConstants) (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ endpointModelRadius c cut) :
    let Pbase := midpointBaseline c P₀
    ∃ K : ℝ, ∃ N : ℕ, 0 < K ∧ 3 ≤ N ∧
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
            (sampleLaw Pbase n)).toReal ≤ K := by
  obtain ⟨K, N, hK, _, hN, hw⟩ :=
    exists_endpointPerturb_KL_witnesses_quadratic c P₀ hP₀ cut hu0 hu
  exact ⟨K, N, hK, hN, hw⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
