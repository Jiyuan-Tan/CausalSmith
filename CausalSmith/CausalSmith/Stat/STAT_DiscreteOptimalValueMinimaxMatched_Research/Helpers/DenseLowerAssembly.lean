import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseObservationRegrouping
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseDepoissonization
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseNumerics

set_option linter.style.longLine false

/-! Assembly of the dense fuzzy-hypothesis and de-Poissonization certificate. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open Filter MeasureTheory
open scoped BigOperators ProbabilityTheory

-- @node: denseObservationKernel_apply
/-- The chosen dense observation kernel is the genuine Poisson sample law at
each contrast. This uses [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseObservationKernel_apply (n d : ℕ) (hd : 2 ≤ d)
    (theta : DenseContrast d) :
    denseObservationKernel n d hd theta =
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (obsLaw (observedMarginal (denseLaw theta)))
        (Real.toNNReal (2 * n)) := by
  exact Classical.choose_spec (denseObservationKernel_exists n d hd) theta

-- @node: denseObservationMixture_eq_priorPredictive
/-- The paper's dense observation mixture is exactly the prior predictive law
of its genuine Poisson observation kernel. This uses [the alphabet size satisfies its stated restriction](hyp:hd), and [the dense construction domain conditions hold](hyp:hdom). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseObservationMixture_eq_priorPredictive (n d : ℕ) (hd : 2 ≤ d)
    (epsilon : ℝ) (hdom : DenseConstructionDomain n d epsilon)
    (nu : Measure ℝ) :
    denseObservationMixture n d hd epsilon hdom nu =
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (denseScaledProductPrior n d epsilon hdom nu)
        (denseObservationKernel n d hd) := by
  rfl

-- @node: denseFuzzyMinimax_lower
/-- The standard two-fuzzy-hypotheses theorem converts the paper's dense
observation-mixture and target-concentration bounds into an ENNReal minimax
lower bound for the dense Poisson experiment. This uses [the dense construction domain conditions hold](hyp:hdom), and [the stated delta condition holds](hyp:hDelta), and [the two experiments have the stated total-variation bound](hyp:htv), and [the stated prior-tail bound holds](hyp:htail). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseFuzzyMinimax_lower {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (priors : DensePriorFamily)
    (hDelta : 0 < densePriorSeparation n d)
    (htv : Causalean.Stat.tvDist
        (denseSubmodel n d epsilon hdom priors).mixture0
        (denseSubmodel n d epsilon hdom priors).mixture1 ≤ 1 / 16)
    (htail : ∀ nu ∈ ({(denseSubmodel n d epsilon hdom priors).nu0,
          (denseSubmodel n d epsilon hdom priors).nu1} : Set (Measure ℝ)),
      denseScaledProductPrior n d epsilon hdom nu
        {theta | |denseTargetAt theta -
          densePriorTargetMean n d epsilon hdom nu| >
            densePriorSeparation n d / 4} ≤ 1 / 8) :
    ENNReal.ofReal (11 * densePriorSeparation n d ^ 2 / 512) ≤
      Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk
        (denseObservationKernel n d hdom.1) denseTargetAt := by
  let C := denseSubmodel n d epsilon hdom priors
  let pi0 := denseScaledProductPrior n d epsilon hdom C.nu0
  let pi1 := denseScaledProductPrior n d epsilon hdom C.nu1
  let K := denseObservationKernel n d hdom.1
  letI : IsProbabilityMeasure C.nu0 := C.priorConditions.1
  letI : IsProbabilityMeasure C.nu1 := C.priorConditions.2.1
  letI : IsProbabilityMeasure pi0 := denseScaledProductPrior_isProbability hdom C.nu0
    C.priorConditions.2.2.1
  letI : IsProbabilityMeasure pi1 := denseScaledProductPrior_isProbability hdom C.nu1
    C.priorConditions.2.2.2.1
  have hK : ∀ theta, IsProbabilityMeasure (K theta) := by
    intro theta
    rw [show K theta =
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n)) by
      exact denseObservationKernel_apply n d hdom.1 theta]
    infer_instance
  have htail0 : pi0.real {theta | densePriorSeparation n d / 4 <
        |denseTargetAt theta - densePriorTargetMean n d epsilon hdom C.nu0|} ≤ 1 / 8 := by
    have hh := htail C.nu0 (by left; rfl)
    have hh' : pi0 {theta | densePriorSeparation n d / 4 <
        |denseTargetAt theta - densePriorTargetMean n d epsilon hdom C.nu0|} ≤
          ENNReal.ofReal (1 / 8 : ℝ) := by
      simpa [pi0, C] using hh
    simpa [Measure.real, ENNReal.toReal_ofReal] using
      ENNReal.toReal_mono (by norm_num) hh'
  have htail1 : pi1.real {theta | densePriorSeparation n d / 4 <
        |denseTargetAt theta - densePriorTargetMean n d epsilon hdom C.nu1|} ≤ 1 / 8 := by
    have hh := htail C.nu1 (by right; rfl)
    have hh' : pi1 {theta | densePriorSeparation n d / 4 <
        |denseTargetAt theta - densePriorTargetMean n d epsilon hdom C.nu1|} ≤
          ENNReal.ofReal (1 / 8 : ℝ) := by
      simpa [pi1, C] using hh
    simpa [Measure.real, ENNReal.toReal_ofReal] using
      ENNReal.toReal_mono (by norm_num) hh'
  apply Causalean.Stat.Minimax.FuzzyHypotheses.twoFuzzyHypotheses_minimax_lower_standard
    pi0 pi1 K denseTargetAt hK measurable_denseTargetAt
    (densePriorTargetMean n d epsilon hdom C.nu0)
    (densePriorTargetMean n d epsilon hdom C.nu1)
    (densePriorSeparation n d) hDelta
  · simpa [C, denseSubmodel] using C.priorMeanSeparation_eq.symm.le
  · exact htail0
  · exact htail1
  · simpa [pi0, pi1, K, C, denseSubmodel, denseObservationMixture,
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive] using htv

-- @node: observedOptimalValue_mem_unitInterval_denseAssembly
/-- Every observed-model target is in the unit interval. This uses [the observed law satisfies the stated model restrictions](hyp:hP). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma observedOptimalValue_mem_unitInterval_denseAssembly {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    observedOptimalValue P hP ∈ Set.Icc (0 : ℝ) 1 := by
  have hj (x : Fin d) (a y : Bool) : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
  have hc (x : Fin d) : 0 ≤ cellMass P x := by
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => hj x a y
  have hm (x : Fin d) (a : Bool) : outcomeMean P a x ∈ Set.Icc (0 : ℝ) 1 := by
    have ha : 0 ≤ armMass P a x := Finset.sum_nonneg fun y _ => hj x a y
    have hle : jointMass P x a true ≤ armMass P a x := by
      simp [armMass]
      exact hj x a false
    exact ⟨div_nonneg (hj x a true) ha, div_le_one_of_le₀ hle ha⟩
  have hsum : ∑ x : Fin d, cellMass P x = 1 := by
    calc
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := by
        simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  rw [observedOptimalValue, observedOptimalValueRaw]
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hc x)
      ((hm x false).1.trans (le_max_left _ _))
  · calc
      ∑ x : Fin d, cellMass P x *
          max (outcomeMean P false x) (outcomeMean P true x) ≤
          ∑ x : Fin d, cellMass P x * 1 := by
        apply Finset.sum_le_sum
        intro x _hx
        exact mul_le_mul_of_nonneg_left
          (max_le (hm x false).2 (hm x true).2) (hc x)
      _ = 1 := by simpa using hsum

-- @node: denseFuzzyMinimax_to_poissonRisk
/-- The dense fuzzy minimax problem is a restriction of the genuine clipped
Poisson observed-law problem.  This also converts its `ENNReal` risk to the
paper's real-valued minimax convention. This uses [the dense construction domain conditions hold](hyp:hdom). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseFuzzyMinimax_to_poissonRisk {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) :
    (Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk
      (denseObservationKernel n d hdom.1) denseTargetAt).toReal ≤
        poissonOptimalValueRisk (2 * n) d epsilon := by
  let K := denseObservationKernel n d hdom.1
  let target := denseTargetAt (d := d)
  have htarget (theta : DenseContrast d) : target theta ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hP, _hcell, _hprop, _hmu1, _hmu0, hvalue⟩ :=
      denseLaw_observed_spec epsilon ⟨hdom.2.1, hdom.2.2.1⟩ theta
    have hvalue' : observedOptimalValue (observedMarginal (denseLaw theta)) hP =
        target theta := by simpa [target, denseTargetAt] using hvalue
    rw [← hvalue']
    exact observedOptimalValue_mem_unitInterval_denseAssembly _ hP
  have hpoisson_bdd (est : DensePoissonEstimator d) :
      BddAbove (Set.range (poissonObservedRisk (2 * n)
        (d := d) (epsilon := epsilon) est)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨P, rfl⟩
    have ht := observedOptimalValue_mem_unitInterval_denseAssembly P.1 P.2
    unfold poissonObservedRisk Causalean.Stat.sqRisk
    have hbound : ∀ s : DensePoissonSample d,
        (max 0 (min 1 (est.1 s)) - observedOptimalValue P.1 P.2) ^ 2 ≤ 1 := by
      intro s
      have hs : max 0 (min 1 (est.1 s)) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact le_max_left _ _
        · exact max_le (by norm_num) (min_le_left _ _)
      have habs : |max 0 (min 1 (est.1 s)) - observedOptimalValue P.1 P.2| ≤ 1 := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      rw [← sq_abs]
      simpa using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
    let mu :=
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (obsLaw P.1) (Real.toNNReal (2 * n))
    have hint : Integrable (fun s : DensePoissonSample d =>
        (max 0 (min 1 (est.1 s)) - observedOptimalValue P.1 P.2) ^ 2) mu := by
      refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun s => ?_)
      · fun_prop
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound s
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    change (∫ s, (max 0 (min 1 (est.1 s)) -
      observedOptimalValue P.1 P.2) ^ 2 ∂mu) ≤ 1
    simpa using integral_mono hint (integrable_const (1 : ℝ)) hbound
  letI : Nonempty (DensePoissonEstimator d) := ⟨⟨0, measurable_const⟩⟩
  apply Causalean.Stat.le_minimaxValue
  intro est
  let clipped : DensePoissonSample d → ℝ := fun s => max 0 (min 1 (est.1 s))
  have hclipped : Measurable clipped := by
    dsimp [clipped]
    fun_prop
  have hmini :
      Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk K target ≤
        Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk K target clipped := by
    unfold Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk
    exact iInf_le_of_le ⟨clipped, hclipped⟩ le_rfl
  have hworst :
      Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk K target clipped ≤
        ENNReal.ofReal (Causalean.Stat.worstCaseRisk
          (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) est) := by
    apply iSup_le
    intro theta
    obtain ⟨hP, _hcell, _hprop, _hmu1, _hmu0, hvalue⟩ :=
      denseLaw_observed_spec epsilon ⟨hdom.2.1, hdom.2.2.1⟩ theta
    let Ptheta : ModelLaw d epsilon := ⟨observedMarginal (denseLaw theta), hP⟩
    have hvalue' : observedOptimalValue Ptheta.1 Ptheta.2 = target theta := by
      simpa [Ptheta, target, denseTargetAt] using hvalue
    have hrisk_le : poissonObservedRisk (2 * n) est Ptheta ≤
        Causalean.Stat.worstCaseRisk
          (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) est :=
      Causalean.Stat.le_worstCaseRisk (hpoisson_bdd est) Ptheta
    calc
      Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk K target clipped theta =
          ENNReal.ofReal (poissonObservedRisk (2 * n) est Ptheta) := by
        unfold Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk poissonObservedRisk
          Causalean.Stat.sqRisk
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        rw [show K theta =
            Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
              (obsLaw Ptheta.1) (Real.toNNReal (2 * n)) by
          simpa [K, Ptheta] using denseObservationKernel_apply n d hdom.1 theta]
        rw [hvalue']
        dsimp [clipped]
        change (∫⁻ x, ENNReal.ofReal ((clipped x - target theta) ^ 2)
            ∂Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
              (obsLaw Ptheta.1) (Real.toNNReal (2 * n))) =
          ENNReal.ofReal (∫ x, (clipped x - target theta) ^ 2
            ∂Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
              (obsLaw Ptheta.1) (Real.toNNReal (2 * n)))
        symm
        apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        · refine (integrable_const (1 : ℝ)).mono'
            (((hclipped.sub measurable_const).pow_const 2).aestronglyMeasurable) ?_
          filter_upwards with s
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hs : clipped s ∈ Set.Icc (0 : ℝ) 1 := by
            dsimp [clipped]
            exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
          have habs : |clipped s - target theta| ≤ 1 := by
            rw [abs_sub_le_iff]
            constructor <;> linarith [hs.1, hs.2, (htarget theta).1, (htarget theta).2]
          rw [← sq_abs]
          simpa using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
        · exact ae_of_all _ fun _ => sq_nonneg _
      _ ≤ ENNReal.ofReal (Causalean.Stat.worstCaseRisk
          (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) est) :=
        ENNReal.ofReal_le_ofReal hrisk_le
  have hfinite : ENNReal.ofReal (Causalean.Stat.worstCaseRisk
      (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) est) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  calc
    (Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk K target).toReal ≤
        (ENNReal.ofReal (Causalean.Stat.worstCaseRisk
          (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) est)).toReal :=
      ENNReal.toReal_mono hfinite (hmini.trans hworst)
    _ = Causalean.Stat.worstCaseRisk
        (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) est := by
      rw [ENNReal.toReal_ofReal]
      exact Causalean.Stat.worstCaseRisk_nonneg (fun _ => by
        unfold poissonObservedRisk Causalean.Stat.sqRisk
        positivity)

-- @node: fuzzyMinimaxSquaredRisk_ne_top_of_unitTarget
/-- A probability experiment with a target in the unit interval has finite
minimax squared risk: the constant-zero estimator has risk at most one. This uses [the approximation degree satisfies its stated restriction](hyp:hK), and [the target lies in the unit interval](hyp:htarget). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma fuzzyMinimaxSquaredRisk_ne_top_of_unitTarget
    {Theta X : Type*} [MeasurableSpace Theta] [MeasurableSpace X]
    (K : ProbabilityTheory.Kernel Theta X) (target : Theta → ℝ)
    (hK : ∀ theta, IsProbabilityMeasure (K theta))
    (htarget : ∀ theta, target theta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk K target ≠ ⊤ := by
  let zeroEstimator : {f : X → ℝ // Measurable f} := ⟨fun _ => 0, measurable_const⟩
  have hworst :
      Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk K target
          zeroEstimator.1 ≤ 1 := by
    unfold Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk
    apply iSup_le
    intro theta
    letI : IsProbabilityMeasure (K theta) := hK theta
    unfold Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk
    calc
      (∫⁻ x, ENNReal.ofReal ((zeroEstimator.1 x - target theta) ^ 2) ∂(K theta)) ≤
          (∫⁻ x : X, (1 : ENNReal) ∂(K theta)) := by
        apply lintegral_mono
        intro x
        apply ENNReal.ofReal_le_one.mpr
        dsimp [zeroEstimator]
        nlinarith [(htarget theta).1, (htarget theta).2]
      _ = 1 := by simp
  apply ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤)
  exact (iInf_le
    (fun estimator : {f : X → ℝ // Measurable f} =>
      Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk K target estimator.1)
    zeroEstimator).trans hworst

-- @node: denseFuzzyLower_to_poissonRisk
/-- The fuzzy-hypothesis lower bound transfers, with its exact numerical
constant, to the paper's genuine Poissonized observed-law minimax risk. This uses [the dense construction domain conditions hold](hyp:hdom), and [the stated delta condition holds](hyp:hDelta), and [the two experiments have the stated total-variation bound](hyp:htv), and [the stated prior-tail bound holds](hyp:htail). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseFuzzyLower_to_poissonRisk {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (priors : DensePriorFamily)
    (hDelta : 0 < densePriorSeparation n d)
    (htv : Causalean.Stat.tvDist
        (denseSubmodel n d epsilon hdom priors).mixture0
        (denseSubmodel n d epsilon hdom priors).mixture1 ≤ 1 / 16)
    (htail : ∀ nu ∈ ({(denseSubmodel n d epsilon hdom priors).nu0,
          (denseSubmodel n d epsilon hdom priors).nu1} : Set (Measure ℝ)),
      denseScaledProductPrior n d epsilon hdom nu
        {theta | |denseTargetAt theta -
          densePriorTargetMean n d epsilon hdom nu| >
            densePriorSeparation n d / 4} ≤ 1 / 8) :
    11 * densePriorSeparation n d ^ 2 / 512 ≤
      poissonOptimalValueRisk (2 * n) d epsilon := by
  let K := denseObservationKernel n d hdom.1
  have hK : ∀ theta, IsProbabilityMeasure (K theta) := by
    intro theta
    rw [show K theta =
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n)) by
      exact denseObservationKernel_apply n d hdom.1 theta]
    infer_instance
  have htarget (theta : DenseContrast d) :
      denseTargetAt theta ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hP, _hcell, _hprop, _hmu1, _hmu0, hvalue⟩ :=
      denseLaw_observed_spec epsilon ⟨hdom.2.1, hdom.2.2.1⟩ theta
    unfold denseTargetAt
    rw [← hvalue]
    exact observedOptimalValue_mem_unitInterval_denseAssembly _ hP
  have hfinite :
      Causalean.Stat.Minimax.FuzzyHypotheses.minimaxSquaredRisk
          K denseTargetAt ≠ ⊤ :=
    fuzzyMinimaxSquaredRisk_ne_top_of_unitTarget K denseTargetAt hK htarget
  have hfuzzy := denseFuzzyMinimax_lower hdom priors hDelta htv htail
  have hreal := ENNReal.toReal_mono hfinite hfuzzy
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal.trans (denseFuzzyMinimax_to_poissonRisk hdom)

/-- The reciprocal-degree Cai--Low bound and logarithmic degree choice make
the product-prior concentration scale valid above a universal alphabet cutoff. This uses [the Cai--Low moment-matching prior result is available](hyp:h_cai_low). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma eventually_densePrior_concentration_scale
    (h_cai_low : CaiLowAbsoluteMomentPriors) :
    ∃ D0 : ℕ, ∀ d : ℕ, D0 ≤ d →
      32 ≤ (d : ℝ) *
        bestEvenApproxError (lowerDegree d) ^ 2 := by
  obtain ⟨c, _C, hc, _hcC, hE⟩ := h_cai_low.2
  have hlog : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)
  have hev : ∀ᶠ x : ℝ in atTop, Real.log x ^ (2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    filter_upwards [hlog.bound (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hf0 : 0 ≤ Real.log x ^ (2 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg hx1) _
    have hg0 : 0 ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg hg0,
      one_mul] using hx
  have hevNat : ∀ᶠ d : ℕ in atTop,
      Real.log (Real.exp 1 * d) ^ 2 ≤ Real.sqrt (Real.exp 1) * Real.sqrt d := by
    have ht : Tendsto (fun d : ℕ => Real.exp 1 * (d : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1)
    filter_upwards [hev.filter_mono ht] with d hd
    rw [← Real.sqrt_mul (Real.exp_nonneg 1)]
    simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hd
  have hsqrt : Tendsto (fun d : ℕ => Real.sqrt d) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ d : ℕ in atTop,
      3200 * Real.sqrt (Real.exp 1) ≤ c ^ 2 * Real.sqrt d := by
    exact (tendsto_atTop.1 (hsqrt.const_mul_atTop (sq_pos_of_pos hc)))
      (3200 * Real.sqrt (Real.exp 1))
  have hall : ∀ᶠ d : ℕ in atTop,
      32 ≤ (d : ℝ) *
        bestEvenApproxError (lowerDegree d) ^ 2 := by
    filter_upwards [hevNat, hlarge, eventually_ge_atTop (2 : ℕ)] with
      d hlogSq hlarge hd
    have hL : 1 ≤ logAlphabet d := by
      rw [logAlphabet]
      calc
        1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ ≤ Real.log (Real.exp 1 * d) := by
          apply Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
            (mul_pos (Real.exp_pos 1) (by positivity))
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (show (1 : ℝ) ≤ d by exact_mod_cast (by omega : 1 ≤ d))
            (Real.exp_nonneg 1)
    have hKpos : (0 : ℝ) < lowerDegree d := by
      exact_mod_cast lowerDegree_pos d hd
    have hKle : (lowerDegree d : ℝ) ≤ 10 * logAlphabet d := by
      have h := (lowerDegree_log_bounds d).2
      linarith
    have hElower := (hE (lowerDegree d) (lowerDegree_even d)
      (lowerDegree_pos d hd)).1
    have hEpos : 0 < bestEvenApproxError (lowerDegree d) := by
      have hcdiv : 0 < c / (lowerDegree d : ℝ) := div_pos hc hKpos
      linarith
    have hroot0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hrootSq : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
    have hKsq : (lowerDegree d : ℝ) ^ 2 ≤
        100 * Real.sqrt (Real.exp 1) * Real.sqrt d := by
      have hk := sq_le_sq₀ (le_of_lt hKpos) (by positivity : 0 ≤ 10 * logAlphabet d)
      have hk' : (lowerDegree d : ℝ) ^ 2 ≤ 100 * logAlphabet d ^ 2 := by
        nlinarith [hk.mpr hKle]
      calc
        (lowerDegree d : ℝ) ^ 2 ≤ 100 * logAlphabet d ^ 2 := hk'
        _ ≤ 100 * (Real.sqrt (Real.exp 1) * Real.sqrt d) :=
          mul_le_mul_of_nonneg_left hlogSq (by norm_num)
        _ = 100 * Real.sqrt (Real.exp 1) * Real.sqrt d := by ring
    have hcprod : c ≤ (lowerDegree d : ℝ) *
        bestEvenApproxError (lowerDegree d) := by
      rw [div_le_iff₀ hKpos] at hElower
      linarith
    have hcSq : c ^ 2 ≤ (lowerDegree d : ℝ) ^ 2 *
        bestEvenApproxError (lowerDegree d) ^ 2 := by
      nlinarith
    have hsqrtExpPos : 0 < Real.sqrt (Real.exp 1) :=
      Real.sqrt_pos.2 (Real.exp_pos 1)
    have hbound : c ^ 2 ≤
        (100 * Real.sqrt (Real.exp 1) * Real.sqrt d) *
          bestEvenApproxError (lowerDegree d) ^ 2 :=
      hcSq.trans (mul_le_mul_of_nonneg_right hKsq (sq_nonneg _))
    have hbound' : c ^ 2 * Real.sqrt d ≤
        100 * Real.sqrt (Real.exp 1) * d *
          bestEvenApproxError (lowerDegree d) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hbound hroot0
      calc
        c ^ 2 * Real.sqrt d ≤
            (100 * Real.sqrt (Real.exp 1) * Real.sqrt d) *
              bestEvenApproxError (lowerDegree d) ^ 2 *
                Real.sqrt d := h
        _ = 100 * Real.sqrt (Real.exp 1) * Real.sqrt d ^ 2 *
              bestEvenApproxError (lowerDegree d) ^ 2 := by ring
        _ = 100 * Real.sqrt (Real.exp 1) * d *
              bestEvenApproxError (lowerDegree d) ^ 2 := by
          rw [hrootSq]
    nlinarith
  rw [eventually_atTop] at hall
  exact hall

/-- The reciprocal Cai--Low approximation bound gives the exact squared
separation scale needed by the fuzzy-hypothesis lower bound. This uses [the Cai--Low moment-matching prior result is available](hyp:h_cai_low). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: densePriorSeparation_sq_lower
lemma densePriorSeparation_sq_lower
    (h_cai_low : CaiLowAbsoluteMomentPriors) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ n d : ℕ, DenseRegime n d →
      c0 * d / (n * lowerDegree d) ≤
        11 * densePriorSeparation n d ^ 2 / 512 := by
  obtain ⟨c, _C, hc, _hcC, hbounds⟩ := h_cai_low.2
  refine ⟨11 * c ^ 2 / (512 * 128), by positivity, ?_⟩
  intro n d hregime
  have hKpos : (0 : ℝ) < lowerDegree d := by
    exact_mod_cast lowerDegree_pos d hregime.1
  have hnpos : (0 : ℝ) < n := by
    have hdpos : 0 < d := lt_trans (by norm_num) hregime.1
    exact_mod_cast (lt_trans (Nat.pow_pos hdpos) hregime.2)
  have hE := (hbounds (lowerDegree d) (lowerDegree_even d)
    (lowerDegree_pos d hregime.1)).1
  have hEsq : c ^ 2 / (lowerDegree d : ℝ) ^ 2 ≤
      bestEvenApproxError (lowerDegree d) ^ 2 := by
    have hcdiv0 : 0 ≤ c / (lowerDegree d : ℝ) := by positivity
    rw [← div_pow]
    exact (sq_le_sq₀ hcdiv0 (hcdiv0.trans hE)).2 hE
  rw [densePriorSeparation, mul_pow, denseAmplitude_sq n d hregime]
  calc
    11 * c ^ 2 / (512 * 128) * d / (n * lowerDegree d) =
        11 / 512 * (lowerDegree d * d / (128 * n)) *
          (c ^ 2 / (lowerDegree d : ℝ) ^ 2) := by field_simp
    _ ≤ 11 / 512 * (lowerDegree d * d / (128 * n)) *
          bestEvenApproxError (lowerDegree d) ^ 2 := by
      gcongr
    _ = 11 * ((lowerDegree d * d / (128 * n)) *
          bestEvenApproxError (lowerDegree d) ^ 2) / 512 := by ring

/-- The complete dense fuzzy-hypothesis certificate: construction identities, moment
matching, likelihood/tensorization control, concentration, and both Poissonized and
fixed-sample risk conclusions. -/
def DenseMomentMatchingCertificate (D0 d n : ℕ) (epsilon cepsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 ∧ D0 ≤ d ∧ d ^ 2 < n ∧
  (8 * logAlphabet d ≤ lowerDegree d ∧ lowerDegree d < 8 * logAlphabet d + 2) ∧
  denseAmplitude n d ^ 2 = lowerDegree d * d / (128 * n) ∧
  denseAmplitude n d ≤ 1 / 2 ∧
  (∀ theta : Fin d → ℝ,
    (∀ x, theta x ∈ Set.Icc (-denseAmplitude n d) (denseAmplitude n d)) →
    ∃ theta' : DenseContrast d, theta'.1 = theta ∧
    ∃ hmodel : ObservedModelClass epsilon (observedMarginal (denseLaw theta')),
      (∀ x, cellMass (observedMarginal (denseLaw theta')) x = 1 / d) ∧
      (∀ x, propensity (observedMarginal (denseLaw theta')) x = 1 / 2) ∧
      (∀ x, outcomeMean (observedMarginal (denseLaw theta')) true x = (1 + theta x) / 2) ∧
      (∀ x, outcomeMean (observedMarginal (denseLaw theta')) false x = (1 - theta x) / 2) ∧
      observedOptimalValue (observedMarginal (denseLaw theta')) hmodel =
        1 / 2 + (∑ x : Fin d, |theta x|) / (2 * d)) ∧
  (∃ hdom : DenseConstructionDomain n d epsilon,
    ∃ priors : DensePriorFamily,
    let C := denseSubmodel n d epsilon hdom priors
    densePriorMeanSeparation C = densePriorSeparation n d ∧
    0 < densePriorMeanSeparation C ∧ densePriorMeanSeparation C ≤ 1 ∧
    Causalean.Stat.tvDist C.mixture0 C.mixture1 ≤
      d * Real.sqrt (denseLikelihoodTail n d) ∧
    d * Real.sqrt (denseLikelihoodTail n d) ≤
      d * Real.sqrt ((Real.exp 1 / 64) ^ (lowerDegree d + 1) /
        (1 - Real.exp 1 / 64)) ∧
    d * Real.sqrt ((Real.exp 1 / 64) ^ (lowerDegree d + 1) /
        (1 - Real.exp 1 / 64)) ≤ 1 / 16 ∧
    (∀ nu ∈ ({C.nu0, C.nu1} : Set (Measure ℝ)),
      ∫ theta, (denseTargetAt theta -
        densePriorTargetMean n d epsilon hdom nu) ^ 2
        ∂denseScaledProductPrior n d epsilon hdom nu ≤ denseAmplitude n d ^ 2 / (4 * d)) ∧
    (∀ nu ∈ ({C.nu0, C.nu1} : Set (Measure ℝ)),
      denseScaledProductPrior n d epsilon hdom nu
        {theta | |denseTargetAt theta -
          densePriorTargetMean n d epsilon hdom nu| > densePriorMeanSeparation C / 4} ≤ 1 / 8)) ∧
  (∀ theta theta' : ℝ,
    (∫ r : DenseSignCounts, oneCellLikelihood (poissonCellIntensity n d) theta r *
        oneCellLikelihood (poissonCellIntensity n d) theta' r
      ∂denseSignBaseline (poissonCellIntensity n d)) =
      Real.exp (poissonCellIntensity n d * theta * theta')) ∧
  densePriorSeparation n d = denseAmplitude n d *
    bestEvenApproxError (lowerDegree d) ∧
  cepsilon * densePriorSeparation n d ^ 2 ≤
    poissonOptimalValueRisk (2 * n) d epsilon ∧
  cepsilon * d / (n * lowerDegree d) ≤
    poissonOptimalValueRisk (2 * n) d epsilon ∧
  minimaxRisk n d epsilon ≥ poissonOptimalValueRisk (2 * n) d epsilon -
    (ProbabilityTheory.poissonMeasure (Real.toNNReal (2 * n)) {k | k < n}).toReal ∧
  cepsilon * d / (n * logAlphabet d) ≤ minimaxRisk n d epsilon

/-- The already-localized analytic ingredients assemble into the complete
construction and supported-prior portion of the dense lower-bound argument.
This isolates the remaining observation-regrouping and minimax-transfer work. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Cai--Low moment-matching prior result is available](hyp:h_cai_low), and [the stated scale inequality holds](hyp:hscale). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseConstructionAndPriorCertificate {n d : ℕ} {epsilon : ℝ}
    (hregime : DenseRegime n d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (h_cai_low : CaiLowAbsoluteMomentPriors)
    (hscale : 32 ≤ (d : ℝ) *
      bestEvenApproxError (lowerDegree d) ^ 2) :
    (8 * logAlphabet d ≤ lowerDegree d ∧
      lowerDegree d < 8 * logAlphabet d + 2) ∧
    denseAmplitude n d ^ 2 = lowerDegree d * d / (128 * n) ∧
    denseAmplitude n d ≤ 1 / 2 ∧
    (∀ theta : Fin d → ℝ,
      (∀ x, theta x ∈ Set.Icc (-denseAmplitude n d) (denseAmplitude n d)) →
      ∃ theta' : DenseContrast d, theta'.1 = theta ∧
      ∃ hmodel : ObservedModelClass epsilon (observedMarginal (denseLaw theta')),
        (∀ x, cellMass (observedMarginal (denseLaw theta')) x = 1 / d) ∧
        (∀ x, propensity (observedMarginal (denseLaw theta')) x = 1 / 2) ∧
        (∀ x, outcomeMean (observedMarginal (denseLaw theta')) true x =
          (1 + theta x) / 2) ∧
        (∀ x, outcomeMean (observedMarginal (denseLaw theta')) false x =
          (1 - theta x) / 2) ∧
        observedOptimalValue (observedMarginal (denseLaw theta')) hmodel =
          1 / 2 + (∑ x : Fin d, |theta x|) / (2 * d)) ∧
    (∃ hdom : DenseConstructionDomain n d epsilon,
      ∃ priors : DensePriorFamily,
      let C := denseSubmodel n d epsilon hdom priors
      densePriorMeanSeparation C = densePriorSeparation n d ∧
      0 < densePriorMeanSeparation C ∧ densePriorMeanSeparation C ≤ 1 ∧
      Causalean.Stat.tvDist
          (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d C.nu0
            (denseSupportedSignKernel n d))
          (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d C.nu1
            (denseSupportedSignKernel n d)) ≤
        d * Real.sqrt (denseLikelihoodTail n d) ∧
      (∀ nu ∈ ({C.nu0, C.nu1} : Set (Measure ℝ)),
        (∫ theta, (denseTargetAt theta -
            densePriorTargetMean n d epsilon hdom nu) ^ 2
            ∂denseScaledProductPrior n d epsilon hdom nu ≤
              denseAmplitude n d ^ 2 / (4 * d)) ∧
        denseScaledProductPrior n d epsilon hdom nu
            {theta | |denseTargetAt theta -
              densePriorTargetMean n d epsilon hdom nu| >
              densePriorSeparation n d / 4} ≤ 1 / 8)) ∧
    (∀ theta theta' : ℝ,
      (∫ r : DenseSignCounts, oneCellLikelihood (poissonCellIntensity n d) theta r *
          oneCellLikelihood (poissonCellIntensity n d) theta' r
        ∂denseSignBaseline (poissonCellIntensity n d)) =
        Real.exp (poissonCellIntensity n d * theta * theta')) ∧
    densePriorSeparation n d = denseAmplitude n d *
      bestEvenApproxError (lowerDegree d) := by
  let hdom := denseConstructionDomain_of_regime n d epsilon hregime hepsilon
  obtain ⟨hdegree, hamplitude, harange, hbox, hgram, hsep⟩ :=
    denseConstructionCertificate hdom hregime.2
  obtain ⟨hdom', priors, hprior⟩ :=
    densePriorSetup hregime hepsilon h_cai_low hscale
  exact ⟨hdegree, hamplitude, harange, hbox,
    ⟨hdom', priors, hprior⟩, hgram, hsep⟩

-- @node: lem:dense-moment-matching-lower
/-- If [the product experiment has the stated independent-sampling law](hyp:h_iid), and [the Cai--Low moment-matching prior result is available](hyp:h_cai_low_of_gate), then [in the dense regime, the minimax risk is bounded below by a positive constant times $d/(nlog(ed))$](goal). -/
lemma dense_moment_matching_lower
    (h_iid : ∀ {d n : ℕ} (P : DiscreteLaw d), IidSampling P (productLaw P n))
    (h_cai_low_of_gate : CaiLowAbsoluteMomentPriors) :
    ∃ (D0 : ℕ) (hD0 : 2 ≤ D0), ∀ epsilon : ℝ,
      0 < epsilon → epsilon < 1 / 2 → ∃ cepsilon : ℝ, 0 < cepsilon ∧
      ∀ (d n : ℕ) (hd : D0 ≤ d) (hn : d ^ 2 < n),
        DenseMomentMatchingCertificate D0 d n epsilon cepsilon := by
  obtain ⟨Dscale, hscale⟩ :=
    eventually_densePrior_concentration_scale h_cai_low_of_gate
  obtain ⟨Dtv, htvGeom⟩ := eventually_denseGeometric_tv_le
  obtain ⟨c0, hc0, hsepRate⟩ :=
    densePriorSeparation_sq_lower h_cai_low_of_gate
  obtain ⟨Dtail, htailAbsorb⟩ :=
    eventually_densePoissonTail_absorbed (c0 / 20) (by positivity)
  let D0 := max 2 (max Dscale (max Dtv Dtail))
  refine ⟨D0, by simp [D0], ?_⟩
  intro epsilon hepsilon0 hepsilonHalf
  let cepsilon : ℝ := min (11 / 512) (min c0 (c0 / 20))
  have hcepsilon : 0 < cepsilon := by
    dsimp [cepsilon]
    positivity
  refine ⟨cepsilon, hcepsilon, ?_⟩
  intro d n hd hn
  have hd2 : 2 ≤ d := le_trans (by simp [D0]) hd
  have hregime : DenseRegime n d := ⟨hd2, hn⟩
  have hscale' : 32 ≤ (d : ℝ) *
      bestEvenApproxError (lowerDegree d) ^ 2 :=
    hscale d (le_trans (by simp [D0]) hd)
  obtain ⟨hdegree, hamplitude, harange, hbox, hprior0, hgram, hsep⟩ :=
    denseConstructionAndPriorCertificate hregime
      ⟨hepsilon0, hepsilonHalf⟩ h_cai_low_of_gate hscale'
  obtain ⟨hdom, priors, hprior⟩ := hprior0
  let C := denseSubmodel n d epsilon hdom priors
  rcases hprior with
    ⟨hmeanSep, hsepPos, hsepOne, hsignTV, hpairTail⟩
  have hgeomTail := denseLikelihoodTail_le_geometric n d hregime
  have hgeomSmall : (d : ℝ) * Real.sqrt
      ((Real.exp 1 / 64) ^ (lowerDegree d + 1) /
        (1 - Real.exp 1 / 64)) ≤ 1 / 16 :=
    htvGeom d (le_trans (by simp [D0]) hd)
  have hfullTail : Causalean.Stat.tvDist C.mixture0 C.mixture1 ≤
      d * Real.sqrt (denseLikelihoodTail n d) := by
    have hp0 : IsProbabilityMeasure C.nu0 := C.priorConditions.1
    have hp1 : IsProbabilityMeasure C.nu1 := C.priorConditions.2.1
    letI : IsProbabilityMeasure C.nu0 := hp0
    letI : IsProbabilityMeasure C.nu1 := hp1
    calc
      Causalean.Stat.tvDist C.mixture0 C.mixture1 ≤
          Causalean.Stat.tvDist
            (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d C.nu0
              (denseSupportedSignKernel n d))
            (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d C.nu1
              (denseSupportedSignKernel n d)) := by
        exact denseObservationMixtures_tv_le_product hregime hdom C.nu0 C.nu1
          C.priorConditions.2.2.1 C.priorConditions.2.2.2.1
      _ ≤ d * Real.sqrt (denseLikelihoodTail n d) := hsignTV
  have hfullTV : Causalean.Stat.tvDist C.mixture0 C.mixture1 ≤ 1 / 16 := by
    calc
      Causalean.Stat.tvDist C.mixture0 C.mixture1 ≤
          d * Real.sqrt (denseLikelihoodTail n d) := hfullTail
      _ ≤ d * Real.sqrt
          ((Real.exp 1 / 64) ^ (lowerDegree d + 1) /
            (1 - Real.exp 1 / 64)) := by gcongr
      _ ≤ 1 / 16 := hgeomSmall
  have htail : ∀ nu ∈ ({C.nu0, C.nu1} : Set (Measure ℝ)),
      denseScaledProductPrior n d epsilon hdom nu
        {theta | |denseTargetAt theta -
          densePriorTargetMean n d epsilon hdom nu| >
            densePriorSeparation n d / 4} ≤ 1 / 8 := fun nu hnu ↦
    (hpairTail nu hnu).2
  have hpoisSep : 11 * densePriorSeparation n d ^ 2 / 512 ≤
      poissonOptimalValueRisk (2 * n) d epsilon :=
    denseFuzzyLower_to_poissonRisk hdom priors (by
      rw [← hmeanSep]
      exact hsepPos)
      (by simpa [C] using hfullTV) (by simpa [C] using htail)
  have hrate0 : c0 * d / (n * lowerDegree d) ≤
      11 * densePriorSeparation n d ^ 2 / 512 := hsepRate n d hregime
  have hpoisRate : cepsilon * d / (n * lowerDegree d) ≤
      poissonOptimalValueRisk (2 * n) d epsilon := by
    have hce0 : cepsilon ≤ c0 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hcmp : cepsilon * d / (n * lowerDegree d) ≤
        c0 * d / (n * lowerDegree d) := by gcongr
    exact hcmp.trans (hrate0.trans hpoisSep)
  obtain ⟨hzeroModel, _hcellZero, _hpropZero, _hmu1Zero, _hmu0Zero, _hvalueZero⟩ :=
    denseLaw_observed_spec epsilon ⟨hepsilon0, hepsilonHalf⟩
      (denseZeroContrast d hd2)
  letI : Nonempty (ModelLaw d epsilon) :=
    ⟨⟨observedMarginal (denseLaw (denseZeroContrast d hd2)), hzeroModel⟩⟩
  have hfixed := minimaxRisk_ge_poissonOptimalValueRisk_sub_lowerTail
    (n := n) (d := d) (epsilon := epsilon)
  have htailSmall := htailAbsorb d n (le_trans (by simp [D0]) hd) hn
  have hLpos : 0 < logAlphabet d := by
    unfold logAlphabet
    apply Real.log_pos
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hegt : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)]
  have hKle : (lowerDegree d : ℝ) ≤ 10 * logAlphabet d := by
    have hL : 1 ≤ logAlphabet d := by
      unfold logAlphabet
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      have harg : Real.exp 1 ≤ Real.exp 1 * (d : ℝ) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)
      have hlog := Real.log_le_log (Real.exp_pos 1) harg
      simpa using hlog
    linarith [(lowerDegree_log_bounds d).2]
  have hpoisLog : (c0 / 10) * d / (n * logAlphabet d) ≤
      poissonOptimalValueRisk (2 * n) d epsilon := by
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (by omega : 0 < n)
    have hKpos : (0 : ℝ) < lowerDegree d := by
      exact_mod_cast lowerDegree_pos d hd2
    calc
      (c0 / 10) * d / (n * logAlphabet d) ≤
          c0 * d / (n * lowerDegree d) := by
        apply (div_le_div_iff₀ (mul_pos hnpos hLpos)
          (mul_pos hnpos hKpos)).2
        calc
          (c0 / 10 * d) * (n * lowerDegree d) =
              (c0 * d * n / 10) * lowerDegree d := by ring
          _ ≤ (c0 * d * n / 10) * (10 * logAlphabet d) := by
            gcongr
          _ = (c0 * d) * (n * logAlphabet d) := by ring
      _ ≤ _ := hrate0.trans hpoisSep
  have hfinal : cepsilon * d / (n * logAlphabet d) ≤
      minimaxRisk n d epsilon := by
    have hce20 : cepsilon ≤ c0 / 20 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hscaleNonneg : 0 ≤ (d : ℝ) / (n * logAlphabet d) := by positivity
    have hhalf : (c0 / 20) * d / (n * logAlphabet d) ≤
        poissonOptimalValueRisk (2 * n) d epsilon -
          (ProbabilityTheory.poissonMeasure (Real.toNNReal (2 * n))
            {k | k < n}).toReal := by
      calc
        (c0 / 20) * d / (n * logAlphabet d) =
            (c0 / 10) * d / (n * logAlphabet d) -
              (c0 / 20) * d / (n * logAlphabet d) := by ring
        _ ≤ _ := sub_le_sub hpoisLog htailSmall
    exact (by
      calc
        cepsilon * d / (n * logAlphabet d) ≤
            (c0 / 20) * d / (n * logAlphabet d) := by
          have hh := mul_le_mul_of_nonneg_right hce20 hscaleNonneg
          simpa [mul_div_assoc] using hh
        _ ≤ _ := hhalf
        _ ≤ _ := hfixed)
  refine ⟨hepsilon0, hepsilonHalf, hd, hn, hdegree, hamplitude, harange,
    hbox, ?_, hgram, hsep, ?_, hpoisRate, ?_, hfinal⟩
  · refine ⟨hdom, priors, ?_⟩
    dsimp only
    refine ⟨hmeanSep, hsepPos, hsepOne, ?_, ?_, hgeomSmall, ?_, ?_⟩
    · exact hfullTail
    · gcongr
    · intro nu hnu
      exact (hpairTail nu hnu).1
    · simpa [C, hmeanSep] using htail
  · have hce : cepsilon ≤ 11 / 512 := min_le_left _ _
    nlinarith [hpoisSep, sq_nonneg (densePriorSeparation n d)]
  · exact hfixed

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
