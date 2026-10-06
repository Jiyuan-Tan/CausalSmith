module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalUniformHolder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalWitness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.WitnessConditions
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryKLReduction

/-! # Critical alternatives with uniformly bounded sample KL -/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- At the critical retention exponent, every fixed sufficiently small
amplitude produces rate-tuned alternatives in the model class whose
full-history sample KL is uniformly bounded. -/
-- @node: exists_criticalPerturb_KL_witnesses_quadratic
lemma exists_criticalPerturb_KL_witnesses_quadratic
    (c : ClassConstants) (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) (hkappa : c.kappa = 1) :
    let Pbase := midpointBaseline c P₀
    ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
      ∃ K : ℝ, ∃ N : ℕ, 0 < K ∧ K = C * u ^ 2 ∧ 3 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          ∃ P₁ : SubjectLaw, ModelClass c P₁ ∧
            P₁.p = Pbase.p ∧ P₁.hazard = Pbase.hazard ∧
            P₁.lam false = Pbase.lam false ∧
            P₁.latent.map LatentSubject.censor =
              Pbase.latent.map LatentSubject.censor ∧
            (∀ a t, retention P₁ a t = retention Pbase a t) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1,
              P₁.lam true t = Pbase.lam true t +
                criticalDirection c cut u n t) ∧
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
  rcases cut.exists_critical_abs_bounds c with
    ⟨Cchi0, Cpsi0, hCchi0, hCpsi0, hchi0, hpsi0⟩
  let Cchi := Cchi0 + 1
  let Cpsi := Cpsi0 + 1
  have hCchi : 0 < Cchi := by dsimp [Cchi]; linarith
  have hCpsi : 0 < Cpsi := by dsimp [Cpsi]; linarith
  have hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi := by
    intro y hy
    exact (hchi0 y hy).trans (by dsimp [Cchi]; linarith)
  have hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi := by
    intro x hx
    exact (hpsi0 x hx).trans (by dsimp [Cpsi]; linarith)
  have hlambda0 : 0 < lambda0 :=
    lt_trans c.lambdaMin_pos (midpoint_strict_bounds c).1
  rcases exists_criticalDirection_midpoint_band_holder_uniform c cut with
    ⟨u₀, hu₀, Nholder, hNholder3, huniform⟩
  rcases exists_criticalBandwidth_small c with
    ⟨Nband, hNband3, hbandwidth⟩
  let N := max Nholder Nband
  have hN3 : 3 ≤ N := hNholder3.trans (le_max_left _ _)
  let C := ((3 / 2 : ℝ) * c.gMax * (Cchi * Cpsi) ^ 2 / lambda0) / (c.beta + 1)
  have hC : 0 < C := by
    have hg := c.gMin_pos.trans c.gMin_lt
    have hb : 0 < c.beta + 1 := by linarith [c.beta_pos]
    dsimp [C]
    positivity
  refine ⟨C, hC, u₀, hu₀, ?_⟩
  intro u hu hu₀
  let A := (3 / 2 : ℝ) * c.gMax * (|u| * Cchi * Cpsi) ^ 2 / lambda0
  let K := A / (c.beta + 1)
  have hA : 0 < A := by
    dsimp [A]
    have hg : 0 < c.gMax := lt_trans c.gMin_pos c.gMin_lt
    have huabs : 0 < |u| := abs_pos.mpr hu.ne'
    have hsq : 0 < (|u| * Cchi * Cpsi) ^ 2 := by positivity
    exact div_pos (mul_pos (mul_pos (by norm_num) hg) hsq) hlambda0
  have hK : 0 < K := by
    exact div_pos hA (by linarith [c.beta_pos])
  have hKeq : K = C * u ^ 2 := by
    dsimp [K, A, C]
    rw [abs_of_pos hu]
    ring
  refine ⟨K, N, hK, hKeq, hN3, ?_⟩
  intro n hnN
  have hn3 : 3 ≤ n := hN3.trans hnN
  have hn2 : 2 ≤ n := by omega
  have hnHolder : Nholder ≤ n := (le_max_left _ _).trans hnN
  have hnBand : Nband ≤ n := (le_max_right _ _).trans hnN
  have hconditions := huniform u hu hu₀ n hnHolder
  have hbandwidthSmall := hbandwidth n hnBand
  let lam1 := fun t : ℝ => midpointLambda c + criticalDirection c cut u n t
  have hband : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c.lambdaMin ≤ lam1 t ∧ lam1 t ≤ c.lambdaMax := by
    intro t ht
    simpa [lam1] using hconditions.1 t ht
  have hadd : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < lam1 t := by
    intro t ht
    exact c.lambdaMin_pos.trans_le (hband t ht).1
  rcases exists_criticalPerturb_modelClass_of_bounds c P₀ hP₀ cut hn2
      hconditions.1 hconditions.2 with
    ⟨hfinite, hmodel, hp, hhazard, hfalse, hcensor, hret, htrue⟩
  have hPbase : Pbase =
      SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c) := by
    simpa [Pbase, lambda0, d0] using midpointBaseline_eq_baseline c P₀
  have hfiniteLocal : ∀ a : Arm,
      IsFiniteMeasure (treatmentPerturbIntensity Pbase lam1 a) := by
    simpa [Pbase, lam1] using hfinite
  have hfiniteBase : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) lam1 a) := by
    simpa [hPbase] using hfiniteLocal
  let P₁ := SubjectLaw.perturbTreatment Pbase lam1 hfiniteLocal
  let Q := SubjectLaw.perturbTreatment
    (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) lam1 hfiniteBase
  have hP₁Q : P₁ = Q := by
    exact SubjectLaw.perturbTreatment_congr_base _ _ hPbase lam1
      hfiniteLocal hfiniteBase
  have hmodel1 : ModelClass c P₁ := by
    simpa [P₁, Pbase, lam1] using hmodel
  have hlamMeas : Measurable lam1 := by
    exact measurable_const.add (criticalDirection_measurable c cut u hn2)
  have hweighted : IntervalIntegrable
      (weightedPoissonCost Pbase true lambda0 (criticalDirection c cut u n))
      volume 0 1 := by
    rw [hPbase]
    exact critical_weightedPoissonCost_intervalIntegrable c P₀ lambda0 d0
      (midpointDeath_pos c) cut hn2 hlambda0 hCchi.le hCpsi.le hchi hpsi
      (fun t ht => by simpa [lam1] using hadd t ht)
  have hKL := SubjectLaw.baselinePerturb_sampleKL_weighted
    P₀ lambda0 d0 (midpointDeath_pos c) hP₀.assignmentLaw lam1 hlamMeas
    (fun t ht => (hadd t ⟨ht.1.le, ht.2⟩).le) hlambda0 hfiniteBase (by
      rw [show (fun t : ℝ =>
          survival (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true t *
            retention (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true t *
            (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)) =
          weightedPoissonCost
            (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true lambda0
            (criticalDirection c cut u n) by
        funext t
        rw [weightedPoissonCost_apply]]
      simpa only [hPbase] using hweighted) n
  have hhx0 : criticalBandwidth c n ≤ c.x0 := by
    exact hbandwidthSmall.2.trans (by linarith [c.x0_pos])
  have hI := critical_weightedPoissonCost_integral_le c P₀ lambda0 d0
    (midpointDeath_pos c) (by
      simpa [Pbase, midpointBaseline_eq_baseline] using
        (midpointBaseline_modelClass c P₀ hP₀)) cut hn2 hkappa hhx0
    hlambda0 hCchi.le hCpsi.le hchi hpsi
    (fun t ht => by simpa [lam1] using hadd t ht) (by
      simpa [hPbase] using hweighted)
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..1,
      weightedPoissonCost Pbase true lambda0 (criticalDirection c cut u n) t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have hw := SubjectLaw.baseline_survival_mul_retention_mem_unitInterval
      P₀ lambda0 d0 (midpointDeath_pos c) (a := true) (t := t) ht.1
    have hc := poissonIntensityCost_nonneg (lam1 t) lambda0
      (hadd t ht).le hlambda0
    rw [weightedPoissonCost_apply]
    exact mul_nonneg (by simpa [hPbase] using hw.1)
      (by simpa [lam1] using hc)
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
        weightedPoissonCost Pbase true lambda0 (criticalDirection c cut u n) t) ≤ K := by
    apply critical_sampleKL_factor_le c hn3 hp1 hI0 hA.le
    simpa [hPbase, A] using hI
  refine ⟨P₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hmodel1
  · simpa [P₁, Pbase, lam1] using hp
  · simpa [P₁, Pbase, lam1] using hhazard
  · simpa [P₁, Pbase, lam1] using hfalse
  · simpa [P₁, Pbase, lam1] using hcensor
  · simpa [P₁, Pbase, lam1] using hret
  · simpa [P₁, Pbase, lam1] using htrue
  · rw [hP₁Q, midpointBaseline_eq_baseline c P₀]
    simpa [Q, SubjectLaw.perturbTreatment, SubjectLaw.baseline, lam1, lambda0]
      using hKL.2
  · rw [hP₁Q, midpointBaseline_eq_baseline c P₀, hKL.2]
    have hsampleBase : (n : ℝ) *
        (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)).p true *
        (∫ t in (0 : ℝ)..1,
          weightedPoissonCost
            (SubjectLaw.baseline P₀ lambda0 d0 (midpointDeath_pos c)) true
            lambda0 (criticalDirection c cut u n) t) ≤ K := by
      simpa [hPbase] using hsample
    simpa [lam1, lambda0, weightedPoissonCost_apply] using hsampleBase

/-- Forget the amplitude coefficient while retaining the original witness interface. -/
-- @node: exists_criticalPerturb_KL_witnesses
lemma exists_criticalPerturb_KL_witnesses
    (c : ClassConstants) (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀)
    (cut : CutoffData c) (hkappa : c.kappa = 1) :
    let Pbase := midpointBaseline c P₀
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
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
                criticalDirection c cut u n t) ∧
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
  obtain ⟨C, hC, u₀, hu₀, hw⟩ :=
    exists_criticalPerturb_KL_witnesses_quadratic c P₀ hP₀ cut hkappa
  refine ⟨u₀, hu₀, ?_⟩
  intro u hu hur
  obtain ⟨K, N, hK, _, hN, hwitness⟩ := hw u hu hur
  exact ⟨K, N, hK, hN, hwitness⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
