import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DensePriorConcentration

/-! Assembly of the supported Cai--Low product priors used by the dense lower bound. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory

/-- In the dense regime, the cited Cai--Low pair gives supported product priors
with the required separation, sign-count mixture bound, variance, and target
concentration. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Cai--Low moment-matching prior result is available](hyp:h_cai_low), and [the stated scale inequality holds](hyp:hscale). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePriorSetup {n d : ℕ} {epsilon : ℝ}
    (hregime : DenseRegime n d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (h_cai_low : CaiLowAbsoluteMomentPriors)
    (hscale : 32 ≤ (d : ℝ) *
      bestEvenApproxError (lowerDegree d) ^ 2) :
    ∃ hdom : DenseConstructionDomain n d epsilon,
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
                densePriorSeparation n d / 4} ≤ 1 / 8) := by
  let hdom := denseConstructionDomain_of_regime n d epsilon hregime hepsilon
  let priors := densePriorFamily_of_caiLow h_cai_low
  let C := denseSubmodel n d epsilon hdom priors
  have hpair : DensePriorPairConditions (lowerDegree d) C.nu0 C.nu1 := C.priorConditions
  have hE := bestEvenApproxError_lowerDegree_pos h_cai_low d hregime.1
  have hsep := densePriorSeparation_range n d hregime hE
  refine ⟨hdom, priors, C.priorMeanSeparation_eq, ?_, ?_, ?_, ?_⟩
  · change 0 < C.priorMeanSeparation
    rw [C.priorMeanSeparation_eq]
    exact hsep.1
  · change C.priorMeanSeparation ≤ 1
    rw [C.priorMeanSeparation_eq]
    exact hsep.2
  · exact denseMomentMatchedSignProduct_tv hregime C.nu0 C.nu1 hpair
  · exact densePriorPair_variance_and_concentration hdom C.nu0 C.nu1 hpair hscale

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
