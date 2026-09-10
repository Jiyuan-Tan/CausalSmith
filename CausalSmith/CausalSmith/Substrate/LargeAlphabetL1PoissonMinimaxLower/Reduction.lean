import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.FuzzyConstruction

/-!
# Fuzzy-hypothesis reduction to all-estimator risk

This module contains the reusable decision-theoretic step.  Target
concentration under two priors and total-variation closeness of their induced
experiments force a squared-risk lower bound for every measurable estimator,
which then passes through the estimator infimum defining minimax risk.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

private lemma fuzzyPriorRiskLower {n d : ℕ}
    (π : Measure (TwoUnknownParameter d)) [IsProbabilityMeasure π]
    (hmix : IsProbabilityMeasure (mixtureObservationLaw n d π))
    (est : MeasurableEstimator d) (r : ℝ)
    (A G : Set _) (hA : MeasurableSet A) (hG : MeasurableSet G)
    (hGmass : (15 : ℝ≥0∞) / 16 ≤ π G)
    (hdom : ∀ θ ∈ G, ∀ z ∈ A,
      r ^ 2 ≤ (est.1 z - probabilityVectorL1 θ.1 θ.2) ^ 2)
    (herr : (3 : ℝ) / 8 ≤ (mixtureObservationLaw n d π).real A) :
    ENNReal.ofReal (r ^ 2 / 8) ≤ poissonizedTwoUnknownL1WorstRisk n d est := by
  let κ : TwoUnknownParameter d → Measure (TwoSampleCounts d) :=
    fun θ => poissonizedTwoSampleLaw n θ.1 θ.2
  let R := poissonizedTwoUnknownL1WorstRisk n d est
  let c := ENNReal.ofReal (r ^ 2)
  letI : IsProbabilityMeasure (mixtureObservationLaw n d π) := hmix
  have hκ : AEMeasurable κ π := by
    by_contra h
    have hz : mixtureObservationLaw n d π = 0 := by
      simp [mixtureObservationLaw, κ, Measure.bind, h]
    have hone : (mixtureObservationLaw n d π) Set.univ = 1 := measure_univ
    rw [hz] at hone
    simp at hone
  have hbad : π Gᶜ ≤ (1 : ℝ≥0∞) / 16 := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top π Gᶜ) (by norm_num)]
    have hmassReal := ENNReal.toReal_mono (measure_ne_top π G) hGmass
    have hGle : π G ≤ 1 := by
      calc
        π G ≤ π Set.univ := measure_mono (Set.subset_univ G)
        _ = 1 := measure_univ
    have hcompReal : (π Gᶜ).toReal = 1 - (π G).toReal := by
      rw [measure_compl hG (measure_ne_top π G), measure_univ,
        ENNReal.toReal_sub_of_le hGle (by norm_num)]
      norm_num
    rw [hcompReal]
    norm_num [ENNReal.toReal_div] at hmassReal ⊢
    linarith
  have hpoint (θ : TwoUnknownParameter d) :
      c * κ θ A ≤ poissonizedTwoSampleL1Risk n θ.1 θ.2 est +
        Gᶜ.indicator (fun _ => c) θ := by
    by_cases hθ : θ ∈ G
    · have hnot : θ ∉ Gᶜ := by simpa using hθ
      simp only [Set.indicator_of_notMem hnot, add_zero]
      unfold poissonizedTwoSampleL1Risk poissonizedTwoSampleL1RiskAt
      calc
        c * κ θ A = ∫⁻ z, A.indicator (fun _ => c) z ∂κ θ := by
          simp [hA]
        _ ≤ ∫⁻ z, ENNReal.ofReal
            ((est.1 z - probabilityVectorL1 θ.1 θ.2) ^ 2) ∂κ θ := by
          apply lintegral_mono
          intro z
          by_cases hz : z ∈ A
          · simp only [Set.indicator_of_mem hz]
            exact ENNReal.ofReal_le_ofReal (hdom θ hθ z hz)
          · simp [Set.indicator_of_notMem hz]
    · have hcomp : θ ∈ Gᶜ := by simpa
      rw [Set.indicator_of_mem hcomp]
      letI : IsProbabilityMeasure (κ θ) := by
        dsimp [κ]
        change IsProbabilityMeasure
          (poissonizedTwoSampleLawAt (2 * (n : ℝ≥0)) θ.1 θ.2)
        infer_instance
      have hlaw : κ θ A ≤ 1 := by
        calc
          κ θ A ≤ κ θ Set.univ := measure_mono (Set.subset_univ A)
          _ = 1 := measure_univ
      calc
        c * κ θ A ≤ c := by
          simpa only [mul_one] using
            (mul_le_mul (le_refl c) hlaw bot_le bot_le)
        _ ≤ poissonizedTwoSampleL1Risk n θ.1 θ.2 est + c := by simp
  have hmeasure : AEMeasurable (fun θ => κ θ A) π :=
    (Measure.measurable_coe hA).comp_aemeasurable hκ
  have hpenalty : Measurable (fun θ => Gᶜ.indicator (fun _ => c) θ) :=
    measurable_const.indicator hG.compl
  have hmaster : c * (mixtureObservationLaw n d π) A ≤ R + c * π Gᶜ := by
    calc
      c * (mixtureObservationLaw n d π) A = ∫⁻ θ, c * κ θ A ∂π := by
        rw [lintegral_const_mul'' c hmeasure]
        rw [← Measure.bind_apply hA hκ]
        rfl
      _ ≤ ∫⁻ θ, (poissonizedTwoSampleL1Risk n θ.1 θ.2 est +
          Gᶜ.indicator (fun _ => c) θ) ∂π := lintegral_mono hpoint
      _ = (∫⁻ θ, poissonizedTwoSampleL1Risk n θ.1 θ.2 est ∂π) + c * π Gᶜ := by
        rw [lintegral_add_right _ hpenalty]
        simp [hG.compl]
      _ ≤ R + c * π Gᶜ := by
        gcongr
        apply lintegral_le_const
        filter_upwards with θ
        exact le_iSup (fun θ : TwoUnknownParameter d =>
          poissonizedTwoSampleL1Risk n θ.1 θ.2 est) θ
  have herrE : (3 : ℝ≥0∞) / 8 ≤ (mixtureObservationLaw n d π) A := by
    calc
      (3 : ℝ≥0∞) / 8 = ENNReal.ofReal ((3 : ℝ) / 8) := by
        norm_num [ENNReal.ofReal_div_of_pos]
      _ ≤ ENNReal.ofReal ((mixtureObservationLaw n d π).real A) :=
        ENNReal.ofReal_le_ofReal herr
      _ = (mixtureObservationLaw n d π) A := by
        exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  by_cases hR : R = ∞
  · simp [R, hR]
  have hfinal : c * ((3 : ℝ≥0∞) / 8) ≤ R + c * ((1 : ℝ≥0∞) / 16) := by
    calc
      c * ((3 : ℝ≥0∞) / 8) ≤ c * (mixtureObservationLaw n d π) A :=
        mul_le_mul (le_refl c) herrE bot_le bot_le
      _ ≤ R + c * π Gᶜ := hmaster
      _ ≤ R + c * ((1 : ℝ≥0∞) / 16) := by
        exact add_le_add (le_refl R)
          (mul_le_mul (le_refl c) hbad bot_le bot_le)
  have hright : R + c * ((1 : ℝ≥0∞) / 16) ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact hR
    · apply ENNReal.mul_ne_top
      · simp [c]
      · norm_num
  have hreal := ENNReal.toReal_mono hright hfinal
  rw [ENNReal.ofReal_le_iff_le_toReal hR]
  rw [ENNReal.toReal_add hR (by
    apply ENNReal.mul_ne_top
    · simp [c]
    · norm_num)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (sq_nonneg r), c] at hreal
  norm_num at hreal ⊢
  nlinarith [sq_nonneg r]

/-- Two separated target clouds of prior mass at least `15/16`, whose induced
observation mixtures have total variation at most `1/4`, force every measurable
estimator to have worst-case squared risk at least `radius²/8`.

Proof route: threshold the estimator halfway between the cloud centers.  On a
wrong threshold decision and the corresponding concentration event, squared
loss is at least `radius²`.  Le Cam's testing inequality, two union bounds, and
the `1/4,15/16` constants leave at least `1/8` average error probability; then
Bayes risk is bounded by worst-case risk. -/
theorem fuzzyWitness_allEstimator_lower {n d : ℕ} (W : FuzzyWitness n d)
    (est : MeasurableEstimator d) :
    ENNReal.ofReal (W.radius ^ 2 / 8) ≤
      poissonizedTwoUnknownL1WorstRisk n d est := by
  let midpoint := (W.center0 + W.center1) / 2
  let A : Set (TwoSampleCounts d) := {z | midpoint ≤ est.1 z}
  let G0 : Set (TwoUnknownParameter d) :=
    {θ | |probabilityVectorL1 θ.1 θ.2 - W.center0| ≤ W.radius}
  let G1 : Set (TwoUnknownParameter d) :=
    {θ | |probabilityVectorL1 θ.1 θ.2 - W.center1| ≤ W.radius}
  have hA : MeasurableSet A := by
    dsimp [A, midpoint]
    exact measurableSet_le measurable_const est.2
  have htarget : Measurable (fun θ : TwoUnknownParameter d =>
      probabilityVectorL1 θ.1 θ.2) := by
    unfold probabilityVectorL1
    apply Finset.measurable_sum
    intro i hi
    have hp : Measurable (fun θ : TwoUnknownParameter d => (θ.1.1 i : ℝ)) :=
      NNReal.continuous_coe.measurable.comp
        ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst))
    have hq : Measurable (fun θ : TwoUnknownParameter d => (θ.2.1 i : ℝ)) :=
      NNReal.continuous_coe.measurable.comp
        ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_snd))
    exact continuous_abs.measurable.comp (hp.sub hq)
  have hG0 : MeasurableSet G0 := by
    dsimp [G0]
    exact measurableSet_le
      (continuous_abs.measurable.comp (htarget.sub measurable_const)) measurable_const
  have hG1 : MeasurableSet G1 := by
    dsimp [G1]
    exact measurableSet_le
      (continuous_abs.measurable.comp (htarget.sub measurable_const)) measurable_const
  letI : IsProbabilityMeasure W.prior0 := W.prior0_probability
  letI : IsProbabilityMeasure W.prior1 := W.prior1_probability
  letI : IsProbabilityMeasure (mixtureObservationLaw n d W.prior0) :=
    W.mixture0_probability
  letI : IsProbabilityMeasure (mixtureObservationLaw n d W.prior1) :=
    W.mixture1_probability
  have htest := Causalean.Stat.one_sub_tvDist_le_test
    (μ := mixtureObservationLaw n d W.prior0)
    (ν := mixtureObservationLaw n d W.prior1) hA
  have herrsum : (3 : ℝ) / 4 ≤
      (mixtureObservationLaw n d W.prior0).real A +
      (mixtureObservationLaw n d W.prior1).real Aᶜ := by
    linarith [W.mixture_tv]
  by_cases herr0 : (3 : ℝ) / 8 ≤
      (mixtureObservationLaw n d W.prior0).real A
  · apply fuzzyPriorRiskLower W.prior0 W.mixture0_probability est W.radius
      A G0 hA hG0 W.target0_concentrated (herr := herr0)
    intro θ hθ z hz
    dsimp [G0] at hθ
    have ht : probabilityVectorL1 θ.1 θ.2 ≤ W.center0 + W.radius := by
      rw [abs_le] at hθ
      linarith [hθ.2]
    have hm : W.center0 + 2 * W.radius ≤ midpoint := by
      dsimp [midpoint]
      linarith [W.target_separated]
    have he : midpoint ≤ est.1 z := by
      simpa only [A, Set.mem_setOf_eq] using hz
    nlinarith [W.radius_pos]
  · have herr1 : (3 : ℝ) / 8 ≤
        (mixtureObservationLaw n d W.prior1).real Aᶜ := by
      linarith
    apply fuzzyPriorRiskLower W.prior1 W.mixture1_probability est W.radius
      Aᶜ G1 hA.compl hG1 W.target1_concentrated (herr := herr1)
    intro θ hθ z hz
    dsimp [G1] at hθ
    have ht : W.center1 - W.radius ≤ probabilityVectorL1 θ.1 θ.2 := by
      rw [abs_le] at hθ
      linarith [hθ.1]
    have hm : midpoint ≤ W.center1 - 2 * W.radius := by
      dsimp [midpoint]
      linarith [W.target_separated]
    have he : est.1 z < midpoint := by
      simpa only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hz
    nlinarith [W.radius_pos]

/-- A fuzzy witness lower-bounds the extended minimax risk by
`radius²/8`. -/
theorem fuzzyWitness_minimax_lower_ENNReal {n d : ℕ} (W : FuzzyWitness n d) :
    ENNReal.ofReal (W.radius ^ 2 / 8) ≤
      poissonizedTwoUnknownL1MinimaxRiskENNReal n d := by
  apply le_iInf
  intro est
  exact fuzzyWitness_allEstimator_lower W est

/-- A fuzzy witness lower-bounds the real-valued minimax risk by
`radius²/8`; the conversion is sound because the minimax risk is finite. -/
theorem fuzzyWitness_minimax_lower {n d : ℕ} (W : FuzzyWitness n d) :
    W.radius ^ 2 / 8 ≤ poissonizedTwoUnknownL1MinimaxRisk n d := by
  exact (ENNReal.ofReal_le_iff_le_toReal
    (poissonizedTwoUnknownL1MinimaxRiskENNReal_ne_top n d)).mp
      (fuzzyWitness_minimax_lower_ENNReal W)

/-- In the growing-alphabet regime, every measurable estimator fails on some
pair of unknown probability vectors at squared-risk scale
`min(1,d/(n log(e n)))`. -/
theorem poissonizedTwoUnknownL1_allEstimator_lower (n d : ℕ)
    (hd : 8 ≤ d)
    (hn : (d : ℝ) /
      (100 * Real.log (Real.exp 1 * (d : ℝ))) ≤ (n : ℝ))
    (hlog : Real.log (Real.exp 1 * (n : ℝ)) ≤
      4 * Real.log (Real.exp 1 * (d : ℝ)))
    (est : MeasurableEstimator d) :
    ∃ p q : ProbabilityVector d,
      ENNReal.ofReal ((1 / 100000000 : ℝ) * largeAlphabetL1Rate n d) ≤
        poissonizedTwoSampleL1Risk n p q est := by
  have hdpos : 0 < d := by omega
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hdarg : 1 < Real.exp 1 * (d : ℝ) :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1))
      (by simpa using mul_le_mul_of_nonneg_left hdR (Real.exp_pos 1).le)
  have hlhs : 0 < (d : ℝ) /
      (100 * Real.log (Real.exp 1 * (d : ℝ))) :=
    div_pos (by exact_mod_cast hdpos)
      (mul_pos (by norm_num) (Real.log_pos hdarg))
  have hnR : 0 < (n : ℝ) := lt_of_lt_of_le hlhs hn
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hrate : 0 < largeAlphabetL1Rate n d :=
    largeAlphabetL1Rate_pos hnpos hdpos
  obtain ⟨C, hC⟩ := exists_momentMatchedFuzzyConstruction n d hd hn hlog
  have hsqrt : (Real.sqrt (largeAlphabetL1Rate n d)) ^ 2 =
      largeAlphabetL1Rate n d := Real.sq_sqrt hrate.le
  have hsquare :
      ((1 / 1000 : ℝ) * Real.sqrt (largeAlphabetL1Rate n d)) ^ 2 ≤
        C.witness.radius ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      C.witness.radius_pos.le).2 hC
  have hscaled : (1 / 1000000 : ℝ) * largeAlphabetL1Rate n d ≤
      C.witness.radius ^ 2 := by
    calc
      (1 / 1000000 : ℝ) * largeAlphabetL1Rate n d =
          ((1 / 1000 : ℝ) * Real.sqrt (largeAlphabetL1Rate n d)) ^ 2 := by
        rw [mul_pow, hsqrt]
        norm_num
      _ ≤ C.witness.radius ^ 2 := hsquare
  have hreal : (1 / 100000000 : ℝ) * largeAlphabetL1Rate n d <
      C.witness.radius ^ 2 / 8 := by
    nlinarith
  have hradiusRisk : 0 < C.witness.radius ^ 2 / 8 :=
    div_pos (sq_pos_of_pos C.witness.radius_pos) (by norm_num)
  have hENN : ENNReal.ofReal
      ((1 / 100000000 : ℝ) * largeAlphabetL1Rate n d) <
      ENNReal.ofReal (C.witness.radius ^ 2 / 8) :=
    (ENNReal.ofReal_lt_ofReal_iff hradiusRisk).2 hreal
  have hworst : ENNReal.ofReal
      ((1 / 100000000 : ℝ) * largeAlphabetL1Rate n d) <
      poissonizedTwoUnknownL1WorstRisk n d est :=
    hENN.trans_le (fuzzyWitness_allEstimator_lower C.witness est)
  rw [poissonizedTwoUnknownL1WorstRisk, lt_iSup_iff] at hworst
  obtain ⟨θ, hθ⟩ := hworst
  exact ⟨θ.1, θ.2, hθ.le⟩

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
