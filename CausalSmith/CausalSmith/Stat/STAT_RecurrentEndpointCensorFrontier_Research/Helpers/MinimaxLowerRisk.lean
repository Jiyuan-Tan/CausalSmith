module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerBoundAssembly
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerDirections
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxUpperRisk

/-! # Two-point lower bounds for the real minimax risk

The bounded observable estimator makes the extended minimax value finite.
Le Cam's extended-risk bound can therefore be transported through `toReal`
without imposing integrability on competing estimators. Genuine endpoint and
critical alternatives give the eventual rates; a rescaled smooth interior
bump gives the subcritical rate and covers every remaining finite sample size.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The extended all-estimator minimax risk is finite at every sample size
covered by the explicit upper envelope. -/
-- @node: minimaxValue_sqRisk_ne_top
lemma minimaxValue_sqRisk_ne_top (c : ClassConstants) (n : ℕ) (hn : 3 ≤ n) :
    Causalean.Stat.minimaxValueENNReal
      (fun (f : {f : (Fin n → ObsHistory) → ℝ // Measurable f})
        (P : {P : SubjectLaw // ModelClass c P}) =>
        Causalean.Stat.sqRiskLIntegral (sampleLaw P.1 n) f.1 (causalTarget P.1)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    ⟨observableEstimator c, measurable_observableEstimator c n⟩).trans
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro P
  rw [observableEstimator_sqRiskLIntegral_eq c P.1 P.2 n]
  apply ENNReal.ofReal_le_ofReal
  exact observableEstimator_sqRisk_le_honestConstant c P.1 P.2 n hn 1 (by norm_num)

/-- Two legal models with finite sample KL bound the real all-estimator
minimax risk below by a positive multiple of their squared separation. -/
-- @node: twoPoint_minimaxRisk_lower
lemma twoPoint_minimaxRisk_lower (c : ClassConstants) (n : ℕ) (hn : 3 ≤ n)
    (P₀ P₁ : SubjectLaw) (h₀ : ModelClass c P₀) (h₁ : ModelClass c P₁)
    (K : ℝ) (hK : 0 ≤ K)
    (hKL : InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n) ≤
      ENNReal.ofReal K) :
    Real.exp (-K) / 32 * (causalTarget P₁ - causalTarget P₀) ^ 2 ≤
      minimaxRisk c n := by
  let : IsProbabilityMeasure P₀.latent := ⟨P₀.prob⟩
  let : IsProbabilityMeasure P₁.latent := ⟨P₁.prob⟩
  let : IsProbabilityMeasure (observedLaw P₀) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (observedLaw P₁) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P₀ n) := by unfold sampleLaw; infer_instance
  let : IsProbabilityMeasure (sampleLaw P₁ n) := by unfold sampleLaw; infer_instance
  have hlower : ENNReal.ofReal (Real.exp (-K) / 32) *
      ENNReal.ofReal ((causalTarget P₁ - causalTarget P₀) ^ 2) ≤
      Causalean.Stat.minimaxValueENNReal
        (fun (f : {f : (Fin n → ObsHistory) → ℝ // Measurable f})
          (P : {P : SubjectLaw // ModelClass c P}) =>
          Causalean.Stat.sqRiskLIntegral (sampleLaw P.1 n) f.1 (causalTarget P.1)) := by
    apply Causalean.Stat.le_minimaxValueENNReal_of_two_point
      (⟨P₁, h₁⟩ : {P : SubjectLaw // ModelClass c P}) ⟨P₀, h₀⟩
    intro f
    have hsq : (causalTarget P₀ - causalTarget P₁) ^ 2 =
        (causalTarget P₁ - causalTarget P₀) ^ 2 := by ring
    simpa only [hsq] using
      Causalean.Stat.Minimax.le_cam_two_point_mse_lintegral K hK
        (sampleLaw P₁ n) (sampleLaw P₀ n) (causalTarget P₁) (causalTarget P₀)
        hKL f.1 f.2
  have hreal := ENNReal.toReal_mono (minimaxValue_sqRisk_ne_top c n hn) hlower
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.exp (-K) / 32), ENNReal.toReal_ofReal (sq_nonneg _), minimaxRisk]
    using hreal

/-- Class smoothness and positive recurrence bounds make the weighted
Poisson relative-entropy cost integrable against Lebesgue measure. -/
-- @node: modelClass_weightedPoissonCost_intervalIntegrable
lemma modelClass_weightedPoissonCost_intervalIntegrable
    (c : ClassConstants) (Pbase Ppert : SubjectLaw)
    (hbase : ModelClass c Pbase) (hpert : ModelClass c Ppert)
    (lambda0 : ℝ) (hlambda0 : 0 < lambda0) :
    IntervalIntegrable (fun t : ℝ =>
      survival Pbase true t * retention Pbase true t *
        (Ppert.lam true t * Real.log (Ppert.lam true t / lambda0) -
          Ppert.lam true t + lambda0)) volume 0 1 := by
  have hlam := (hpert.recurrenceHolder true).1.continuousOn
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, Ppert.lam true t / lambda0 ≠ 0 := by
    intro t ht
    exact (div_pos (c.lambdaMin_pos.trans_le (hpert.recurrenceBounds true t ht).1)
      hlambda0).ne'
  have hcont : ContinuousOn (fun t : ℝ => survival Pbase true t *
      (Ppert.lam true t * Real.log (Ppert.lam true t / lambda0) -
        Ppert.lam true t + lambda0)) (Set.Icc (0 : ℝ) 1) :=
    (modelClass_survival_continuousOn c Pbase hbase true).mul
      (((hlam.mul ((hlam.div_const lambda0).log hpos)).sub hlam).add continuousOn_const)
  have hcont' : ContinuousOn (fun t : ℝ => survival Pbase true t *
      (Ppert.lam true t * Real.log (Ppert.lam true t / lambda0) -
        Ppert.lam true t + lambda0)) (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  have hi := hcont'.intervalIntegrable (μ := volume)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hi ⊢
  have hg : AEStronglyMeasurable (retention Pbase true)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact (measurable_retention Pbase true).aestronglyMeasurable
  have hgBound : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ‖retention Pbase true t‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ retention Pbase true t from
        measureReal_nonneg)]
      exact retention_le_one Pbase true t)
  simpa only [IntegrableOn, mul_right_comm] using hi.mul_bdd hg hgBound

/-- A separated legal two-point experiment gives the claimed rate after
squaring its target separation. -/
-- @node: twoPoint_minimaxRisk_lower_of_separation
lemma twoPoint_minimaxRisk_lower_of_separation
    (c : ClassConstants) (n : ℕ) (hn : 3 ≤ n)
    (P₀ P₁ : SubjectLaw) (h₀ : ModelClass c P₀) (h₁ : ModelClass c P₁)
    (K δ q : ℝ) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hq : 0 ≤ q)
    (hfin : InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n) ≠ ⊤)
    (hKL : (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n)).toReal ≤ K)
    (hsep : δ * q ≤ |causalTarget P₁ - causalTarget P₀|) :
    (Real.exp (-K) / 32 * δ ^ 2) * q ^ 2 ≤ minimaxRisk c n := by
  have hKL' : InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n) ≤
      ENNReal.ofReal K :=
    (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hK] using hKL)
  have hs := (sq_le_sq₀ (mul_nonneg hδ hq)
    (abs_nonneg (causalTarget P₁ - causalTarget P₀))).2 hsep
  rw [sq_abs, mul_pow] at hs
  calc
    (Real.exp (-K) / 32 * δ ^ 2) * q ^ 2 ≤
        Real.exp (-K) / 32 * (causalTarget P₁ - causalTarget P₀) ^ 2 := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ minimaxRisk c n := twoPoint_minimaxRisk_lower c n hn P₀ P₁ h₀ h₁ K hK hKL'

/-- Legal perturbations of the explicit midpoint baseline have finite KL
and the exact weighted Poisson likelihood formula. -/
-- @node: midpointPerturb_sampleKL_finite
lemma midpointPerturb_sampleKL_finite
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (P₁ : SubjectLaw) (h₁ : ModelClass c P₁) (n : ℕ)
    (hp : P₁.p = (midpointBaseline c P).p)
    (hh : P₁.hazard = (midpointBaseline c P).hazard)
    (hf : P₁.lam false = (midpointBaseline c P).lam false)
    (hc : P₁.latent.map LatentSubject.censor =
      (midpointBaseline c P).latent.map LatentSubject.censor) :
    InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw (midpointBaseline c P) n) < ⊤ ∧
      (InformationTheory.klDiv (sampleLaw P₁ n)
        (sampleLaw (midpointBaseline c P) n)).toReal =
        (n : ℝ) * (midpointBaseline c P).p true *
          ∫ t in (0 : ℝ)..1,
            survival (midpointBaseline c P) true t * retention (midpointBaseline c P) true t *
              (P₁.lam true t * Real.log (P₁.lam true t / midpointLambda c) -
                P₁.lam true t + midpointLambda c) := by
  have hlambda0 : 0 < midpointLambda c := c.lambdaMin_pos.trans (midpoint_strict_bounds c).1
  have hi := modelClass_weightedPoissonCost_intervalIntegrable c (midpointBaseline c P) P₁
    (midpointBaseline_modelClass c P hP) h₁ (midpointLambda c) hlambda0
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < P₁.lam true t := by
    intro t ht
    exact c.lambdaMin_pos.trans_le (h₁.recurrenceBounds true t ht).1
  rw [midpointBaseline_eq_baseline] at hp hh hf hc hi ⊢
  exact arbitraryPerturb_sampleKL_weighted P (midpointLambda c) (midpointDeath c)
    (midpointDeath_pos c) hP.assignmentLaw hlambda0 n (P₁.lam true) hpos P₁
    h₁.randomAssignment h₁.assignmentLaw h₁.poissonRecurrence h₁.deathHazard
    h₁.recurrenceDeathIndependence h₁.independentCensoring hp hh hc hf rfl hi

/-- The endpoint and critical full-history alternatives yield the minimax
lower rate for all sufficiently large sample sizes when retention is at least
critical. Cutoff data are constructed rather than postulated. -/
-- @node: minimaxRisk_eventual_lower_of_one_le_kappa
lemma minimaxRisk_eventual_lower_of_one_le_kappa (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) (hk : 1 ≤ c.kappa) :
    ∃ c₀ : ℝ, ∃ N : ℕ, 0 < c₀ ∧ 3 ≤ N ∧
      ∀ n : ℕ, N ≤ n → c₀ * riskScale c n ≤ minimaxRisk c n := by
  obtain ⟨P, hP⟩ := hNonempty
  obtain ⟨cut⟩ := nonempty_cutoffData c
  obtain ⟨Pbase, hbase, hpbase, hcbase,
    ⟨lambda0, d0, hl0, hl1, hd0, hd1, hconstant, hkl⟩,
    u₀, hu₀, hdirs⟩ := full_history_directions c P hP cut
  have hlambda0 : 0 < lambda0 := c.lambdaMin_pos.trans hl0
  have hfinite (n : ℕ) (hn : 3 ≤ n) (P₁ : SubjectLaw) (h₁ : ModelClass c P₁)
      (hp : P₁.p = Pbase.p) (hh : P₁.hazard = Pbase.hazard)
      (hf : P₁.lam false = Pbase.lam false)
      (hc : P₁.latent.map LatentSubject.censor = Pbase.latent.map LatentSubject.censor) :
      InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw Pbase n) ≠ ⊤ := by
    have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < P₁.lam true t := by
      intro t ht
      exact c.lambdaMin_pos.trans_le (h₁.recurrenceBounds true t ht).1
    exact (hkl n (by omega) (P₁.lam true) hpos P₁
      h₁.randomAssignment h₁.assignmentLaw h₁.poissonRecurrence h₁.deathHazard
      h₁.recurrenceDeathIndependence h₁.independentCensoring hp hh hc hf rfl
      (modelClass_weightedPoissonCost_intervalIntegrable c Pbase P₁ hbase h₁
        lambda0 hlambda0)).1.ne
  by_cases heq : c.kappa = 1
  · obtain ⟨K, δ, N, hK, hδ, hN, hw⟩ := (hdirs u₀ hu₀ le_rfl).2 heq
    refine ⟨Real.exp (-K) / 32 * δ ^ 2, N, by positivity, hN, ?_⟩
    intro n hn
    have hn3 := hN.trans hn
    obtain ⟨P₁, h₁, hp, hh, hf, hc, hr, ht, hkeq, hbound, hsep⟩ := hw n hn
    have hrate := (riskScale_pos c hn3).le
    have hsq : (Real.sqrt (Real.log n / n)) ^ 2 = riskScale c n := by
      have he : riskScale c n = Real.log n / n := by simp [riskScale, heq]
      rw [← he, Real.sq_sqrt hrate]
    have h := twoPoint_minimaxRisk_lower_of_separation c n hn3 Pbase P₁ hbase h₁
      K δ (Real.sqrt (Real.log n / n)) hK.le hδ.le (Real.sqrt_nonneg _)
      (hfinite n hn3 P₁ h₁ hp hh hf hc) hbound hsep
    rwa [hsq] at h
  · have hgt : 1 < c.kappa := lt_of_le_of_ne hk (Ne.symm heq)
    obtain ⟨K, δ, N, hK, hδ, hN, hw⟩ := (hdirs u₀ hu₀ le_rfl).1 hgt
    refine ⟨Real.exp (-K) / 32 * δ ^ 2, N, by positivity, hN, ?_⟩
    intro n hn
    have hn3 := hN.trans hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    obtain ⟨P₁, h₁, hp, hh, hf, hc, hr, ht, hkeq, hbound, hsep⟩ := hw n hn
    have hsq : ((n : ℝ) ^ (-(c.beta + 1) /
        (2 * c.beta + c.kappa + 1))) ^ 2 = riskScale c n := by
      rw [riskScale, if_neg (not_lt_of_ge hk), if_neg heq,
        ← Real.rpow_mul_natCast hnreal.le]
      congr 1
      ring
    have h := twoPoint_minimaxRisk_lower_of_separation c n hn3 Pbase P₁ hbase h₁
      K δ ((n : ℝ) ^ (-(c.beta + 1) / (2 * c.beta + c.kappa + 1)))
      hK.le hδ.le (Real.rpow_pos_of_pos hnreal _).le
      (hfinite n hn3 P₁ h₁ hp hh hf hc) hbound hsep
    rwa [hsq] at h

/-- Move the bump into endpoint distances strictly above `x0`, retaining
the original critical transition functions. -/
-- @node: interiorCutoffData
noncomputable def interiorCutoffData (c : ClassConstants) (cut : CutoffData c) : CutoffData c := by
  let b : ℝ → ℝ := fun x => cut.bump ((x - c.x0) / (1 - c.x0))
  have hscale : 0 < 1 - c.x0 := by linarith [c.x0_le]
  refine { cut with
    bump := b
    bump_smooth := ?_
    bump_nonneg := ?_
    bump_nonzero := ?_
    bump_support := ?_
    bump_compact_inside := ?_ }
  · exact cut.bump_smooth.comp (by fun_prop)
  · intro x
    exact cut.bump_nonneg _
  · obtain ⟨x, hx⟩ := cut.bump_nonzero
    refine ⟨c.x0 + (1 - c.x0) * x, ?_⟩
    have he : (c.x0 + (1 - c.x0) * x - c.x0) / (1 - c.x0) = x := by
      field_simp
      ring
    simpa only [b, he] using hx
  · intro x hx
    have hs := cut.bump_support _ hx
    have hlo := (lt_div_iff₀ hscale).mp hs.1
    have hhi := (div_lt_iff₀ hscale).mp hs.2
    constructor <;> linarith [c.x0_pos]
  · obtain ⟨lo, hi, hlo, hhi, hsupport⟩ := cut.bump_compact_inside
    refine ⟨c.x0 + (1 - c.x0) * lo, c.x0 + (1 - c.x0) * hi,
      by nlinarith [c.x0_pos, mul_pos hscale hlo],
      by nlinarith [mul_pos hscale (sub_pos.mpr hhi)], ?_⟩
    intro x hx
    have hs := hsupport _ hx
    have hl := (le_div_iff₀ hscale).mp hs.1
    have hh := (div_le_iff₀ hscale).mp hs.2
    constructor <;> linarith

/-- The transformed bump vanishes unless its endpoint distance is strictly
above the endpoint-tail radius. -/
-- @node: interiorCutoffData_bump_support
lemma interiorCutoffData_bump_support (c : ClassConstants) (cut : CutoffData c)
    {x : ℝ} (hx : (interiorCutoffData c cut).bump x ≠ 0) : c.x0 < x := by
  have hs := cut.bump_support ((x - c.x0) / (1 - c.x0)) hx
  have hscale : 0 < 1 - c.x0 := by linarith [c.x0_le]
  have hl := (lt_div_iff₀ hscale).mp hs.1
  linarith

/-- Every admissible positive interior amplitude supplies legal two-point
models at all sample sizes, with quadratic KL cost and linear separation. -/
-- @node: interior_twoPoint_family
lemma interior_twoPoint_family (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (cut : CutoffData c) (u : ℝ) (hu : 0 < u)
    (hur : u ≤ endpointModelRadius c cut) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 3 ≤ n →
      ∃ P₀ P₁ : SubjectLaw, ModelClass c P₀ ∧ ModelClass c P₁ ∧
        InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n) < ⊤ ∧
        (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n)).toReal ≤
          u ^ 2 * endpointBumpBound c cut ^ 2 / midpointLambda c ∧
        δ / Real.sqrt n ≤ |causalTarget P₁ - causalTarget P₀| := by
  let B := endpointBumpBound c cut
  let lambda0 := midpointLambda c
  let δ := midpointSurvivalFloor c P * u * endpointBumpMass c cut
  let K := u ^ 2 * B ^ 2 / lambda0
  have hB : 0 < B := endpointBumpBound_pos c cut
  have hlambda0 : 0 < lambda0 := c.lambdaMin_pos.trans (midpoint_strict_bounds c).1
  have hδ : 0 < δ := by
    exact mul_pos (mul_pos (midpointSurvivalFloor_pos c P) hu)
      (endpointBumpMass_pos c cut)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrt1 : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt hn1
  let v := u / Real.sqrt n
  have hv : 0 < v := div_pos hu hsqrt
  have hvu : v ≤ endpointModelRadius c cut := by
    dsimp [v]
    exact (div_le_self hu.le hsqrt1).trans hur
  have hw := exists_endpointPerturb_modelClass c P hP cut hv hvu (n := 1) le_rfl
  simp only [Nat.cast_one, Real.one_rpow] at hw
  obtain ⟨hfinite, hm, hp, hh, hf, hc, hr, ht⟩ := hw
  let Pbase := midpointBaseline c P
  let P₁ := SubjectLaw.perturbTreatment Pbase
    (fun t => midpointLambda c + endpointDirection c cut v 1 t) hfinite
  have h₁ : ModelClass c P₁ := hm
  have hbase : ModelClass c Pbase := midpointBaseline_modelClass c P hP
  have hkl := midpointPerturb_sampleKL_finite c P hP P₁ h₁ n hp hh hf hc
  have htarget := endpoint_causalTarget_sub_eq_integral c P₁ Pbase cut v 1
    h₁.causalTarget_eq_survival_intensity_contrast hbase.causalTarget_eq_survival_intensity_contrast
    ((h₁.armMean_integrand_intervalIntegrable true).sub
      (h₁.armMean_integrand_intervalIntegrable false))
    ((hbase.armMean_integrand_intervalIntegrable true).sub
      (hbase.armMean_integrand_intervalIntegrable false)) hh hf ht
  have hsep : δ * (1 / Real.sqrt n) ≤ |causalTarget P₁ - causalTarget Pbase| := by
    have h := endpointDirection_integral_lower c P cut hv zero_lt_one le_rfl
    simp only [Real.one_rpow, mul_one] at h
    rw [htarget]
    apply le_trans _ (le_abs_self _)
    have he : δ * (1 / Real.sqrt n) =
        midpointSurvivalFloor c P * v * endpointBumpMass c cut := by
      dsimp only [δ, v]
      ring
    rw [he]
    exact h
  let cost := fun t : ℝ => survival Pbase true t * retention Pbase true t *
    (P₁.lam true t * Real.log (P₁.lam true t / lambda0) - P₁.lam true t + lambda0)
  have hi : IntervalIntegrable cost volume 0 1 :=
    modelClass_weightedPoissonCost_intervalIntegrable c Pbase P₁ hbase h₁ lambda0 hlambda0
  have hcost : ∀ t ∈ Set.Icc (0 : ℝ) 1, cost t ≤ v ^ 2 * B ^ 2 / lambda0 := by
    intro t htmem
    have heq : P₁.lam true t = lambda0 + endpointDirection c cut v 1 t := by
      simpa only [Pbase, midpointBaseline_lam, lambda0] using ht t htmem
    have hpos : 0 < lambda0 + endpointDirection c cut v 1 t := by
      rw [← heq]
      exact c.lambdaMin_pos.trans_le (h₁.recurrenceBounds true t htmem).1
    have hc0 := poissonIntensityCost_nonneg _ lambda0 hpos.le hlambda0
    have hquad := poissonIntensityCost_add_le_sq_div hlambda0 hpos
    have hd : |endpointDirection c cut v 1 t| ≤ v * B := by
      simpa only [Real.one_rpow, mul_one, abs_of_pos hv, B] using
        (abs_endpointDirection_le c cut (u := v) (h := 1) (t := t) zero_le_one)
    have hd2 : endpointDirection c cut v 1 t ^ 2 ≤ v ^ 2 * B ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg _) (mul_pos hv hB).le).2 hd
      simpa only [sq_abs, mul_pow] using hs
    have hweight : survival Pbase true t * retention Pbase true t ≤ 1 :=
      (mul_le_mul (survival_bounds_of_deathBounds c Pbase hbase.deathBounds true htmem).2
        (retention_le_one Pbase true t) (by exact measureReal_nonneg)
        zero_le_one).trans (by norm_num)
    dsimp only [cost]
    rw [heq]
    exact (mul_le_mul hweight hquad hc0 zero_le_one).trans (by
      simpa only [one_mul] using div_le_div_of_nonneg_right hd2 hlambda0.le)
  have hI : (∫ t in (0 : ℝ)..1, cost t) ≤ v ^ 2 * B ^ 2 / lambda0 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hi (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => v ^ 2 * B ^ 2 / lambda0) volume 0 1) hcost
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h
  have hp1 : Pbase.p true ≤ 1 := by
    rw [← hbase.assignmentLaw true]
    exact (measureReal_mono (Set.subset_univ _) (by
      rw [Pbase.prob]; exact ENNReal.one_ne_top)).trans_eq
      (by simp [measureReal_def, Pbase.prob])
  have hcancel : (n : ℝ) * v ^ 2 = u ^ 2 := by
    dsimp [v]
    rw [div_pow]
    rw [Real.sq_sqrt hnpos.le]
    field_simp
  have hbound : (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw Pbase n)).toReal ≤ K := by
    rw [hkl.2]
    change (n : ℝ) * Pbase.p true * (∫ t in (0 : ℝ)..1, cost t) ≤ K
    calc
      _ ≤ (n : ℝ) * Pbase.p true * (v ^ 2 * B ^ 2 / lambda0) :=
        mul_le_mul_of_nonneg_left hI (mul_nonneg hnpos.le
          (c.pMin_pos.le.trans (hbase.treatmentOverlap true)))
      _ ≤ (n : ℝ) * 1 * (v ^ 2 * B ^ 2 / lambda0) := by
        gcongr
      _ = K := by dsimp only [K]; rw [mul_one, ← mul_div_assoc, ← mul_assoc, hcancel]
  refine ⟨Pbase, P₁, hbase, h₁, hkl.1, hbound, ?_⟩
  simpa only [one_div, ← div_eq_mul_inv] using hsep

/-- A fixed smooth interior direction, scaled by `1 / sqrt n`, supplies a
uniform parametric lower bound in every retention regime. -/
-- @node: minimaxRisk_parametric_lower
lemma minimaxRisk_parametric_lower (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 3 ≤ n → a * (n : ℝ)⁻¹ ≤ minimaxRisk c n := by
  obtain ⟨P, hP⟩ := hNonempty
  obtain ⟨cut₀⟩ := nonempty_cutoffData c
  let cut := interiorCutoffData c cut₀
  let u := endpointModelRadius c cut
  let K := u ^ 2 * endpointBumpBound c cut ^ 2 / midpointLambda c
  have hu : 0 < u := endpointModelRadius_pos c cut
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (c.lambdaMin_pos.trans (midpoint_strict_bounds c).1).le
  obtain ⟨δ, hδ, hfamily⟩ := interior_twoPoint_family c P hP cut u hu le_rfl
  refine ⟨Real.exp (-K) / 32 * δ ^ 2, by positivity, ?_⟩
  intro n hn
  obtain ⟨P₀, P₁, h₀, h₁, hfin, hbound, hsep⟩ := hfamily n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : (1 / Real.sqrt n) ^ 2 = (n : ℝ)⁻¹ := by
    rw [div_pow, Real.sq_sqrt hnpos.le, one_pow, one_div]
  have h := twoPoint_minimaxRisk_lower_of_separation c n hn P₀ P₁ h₀ h₁
    K δ (1 / Real.sqrt n) hK hδ.le (by positivity) hfin.ne hbound
    (by simpa only [← div_eq_mul_inv, one_div] using hsep)
  rwa [hsq] at h

/-- The parametric interior pair covers the subcritical regime and the
finite set left by the endpoint and critical asymptotic constructions. -/
-- @node: minimaxRisk_lower_rate
lemma minimaxRisk_lower_rate (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 3 ≤ n →
      c₀ * riskScale c n ≤ minimaxRisk c n := by
  classical
  obtain ⟨a, ha, hparam⟩ := minimaxRisk_parametric_lower c hNonempty
  by_cases hk : c.kappa < 1
  · refine ⟨a, ha, ?_⟩
    intro n hn
    simpa only [riskScale, if_pos hk] using hparam n hn
  · obtain ⟨b, N, hb, hN, hevent⟩ :=
      minimaxRisk_eventual_lower_of_one_le_kappa c hNonempty (le_of_not_gt hk)
    let ratio := fun n : ℕ => a * (n : ℝ)⁻¹ / riskScale c n
    have hratpos (n : ℕ) (hn : 3 ≤ n) : 0 < ratio n := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact div_pos (mul_pos ha (inv_pos.mpr hnpos)) (riskScale_pos c hn)
    have hne : (Finset.Icc 3 N).Nonempty := ⟨N, Finset.mem_Icc.mpr ⟨hN, le_rfl⟩⟩
    obtain ⟨i, hi, hmin⟩ := (Finset.Icc 3 N).exists_min_image ratio hne
    have hi3 := (Finset.mem_Icc.mp hi).1
    refine ⟨min b (ratio i), lt_min hb (hratpos i hi3), ?_⟩
    intro n hn
    by_cases hnN : N ≤ n
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (riskScale_pos c hn).le).trans
        (hevent n hnN)
    · have hnmem : n ∈ Finset.Icc 3 N := Finset.mem_Icc.mpr ⟨hn, by omega⟩
      calc
        min b (ratio i) * riskScale c n ≤ ratio n * riskScale c n :=
          mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (hmin n hnmem))
            (riskScale_pos c hn).le
        _ = a * (n : ℝ)⁻¹ := div_mul_cancel₀ _ (riskScale_pos c hn).ne'
        _ ≤ minimaxRisk c n := hparam n hn

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
