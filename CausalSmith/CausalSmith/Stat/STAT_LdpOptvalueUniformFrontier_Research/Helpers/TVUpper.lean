module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TVCalibration

/-!
# Uniform risk of the paired attaining estimator

Projection closes the bounded-loss branches; the calibrated iid norm blocks
close the remaining branches of the explicit paired polynomial procedure.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [Every input probability law induces a probability decision law](goal). -/
-- @node: canonicalDecisionLaw_probability
lemma canonicalDecisionLaw_probability {n : ℕ} {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) (p : Measure α) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (canonicalDecisionLaw Q p) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  unfold canonicalDecisionLaw
  apply isProbabilityMeasure_bind (measurable_protocol_decisionRows Q).aemeasurable
  exact Filter.Eventually.of_forall (fun w => by
    haveI : IsProbabilityMeasure (fixedTranscriptLaw Q w.1 w.2.1) :=
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_transcriptLaw
        Q.kernels Q.markov (fun i => (w.1 i,w.2.1))
    exact Measure.isProbabilityMeasure_map (by fun_prop))

/-- [The paired projection keeps all estimates in the sharper target interval](goal). -/
-- @node: tvFrontierEstimate_range
lemma tvFrontierEstimate_range (n d : ℕ) (eps : ℝ)
    (w : DecisionSpace (tvFrontierProtocol n d eps)) :
    tvFrontierEstimate n d eps w ∈ Set.Icc (0 : ℝ) (1/4) := by
  unfold tvFrontierEstimate
  split_ifs
  · norm_num
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Assume [the stated hv condition](hyp:hv). [The paired projection gives a uniform one-sixteenth squared-risk bound](goal). -/
-- @node: tvFrontierEstimator_risk_le_sixteenth
lemma tvFrontierEstimator_risk_le_sixteenth (n d : ℕ) (eps : ℝ)
    (L : Measure (DecisionSpace (tvFrontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1/4)) :
    squaredRisk L (tvFrontierEstimator n d eps) v ≤ ENNReal.ofReal (1/16 : ℝ) := by
  unfold squaredRisk
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (1/16 : ℝ) ∂L := by
      apply lintegral_mono
      intro w
      apply ENNReal.ofReal_le_ofReal
      have hw := tvFrontierEstimate_range n d eps w
      have hdist := abs_sub_le_of_le_of_le hw.1 hw.2 hv.1 hv.2
      change (tvFrontierEstimate n d eps w - v)^2 ≤ (1/16 : ℝ)
      nlinarith [sq_abs (tvFrontierEstimate n d eps w - v),
        abs_nonneg (tvFrontierEstimate n d eps w - v)]
    _ = _ := by simp

/-- Assume [dimension at least two](hyp:hd) and [the stated hp condition](hyp:hp). [The paired target ranges over zero to one quarter on the parameter cube](goal). -/
-- @node: tvFromUniform_paired_range
lemma tvFromUniform_paired_range (d : ℕ) (hd : 2 ≤ d)
    (p : Measure (PairedSymbol d)) (hp : p ∈ pairedFamily d) :
    tvFromUniform p ∈ Set.Icc (0 : ℝ) (1/4) := by
  obtain ⟨theta, htheta, rfl⟩ := hp
  rw [tvFromUniform_pairedLaw theta htheta (by omega)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsum : ∑ j : Fin d, |theta j| ≤ (d : ℝ)*(1/2) := by
    calc
      _ ≤ ∑ _j : Fin d, (1/2 : ℝ) :=
        Finset.sum_le_sum (fun j _ => abs_le.mpr (htheta j))
      _ = _ := by simp
  have hlo : 0 ≤ signedNorm theta := by unfold signedNorm; positivity
  have hhi : signedNorm theta ≤ 1/2 := by
    unfold signedNorm
    calc
      _ ≤ (d : ℝ)⁻¹ * ((d : ℝ)*(1/2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by field_simp
  constructor <;> linarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), and [the stated hp condition](hyp:hp). [All finite-resource branches of the explicit paired estimator attain the common upper-risk constant, using the calibrated polynomial blocks](goal). -/
-- @node: tvFrontierEstimator_uniform_rate
lemma tvFrontierEstimator_uniform_rate
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps)
    (p : Measure (PairedSymbol d)) (hp : p ∈ pairedFamily d) :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) p)
      (tvFrontierEstimator n d eps) (tvFromUniform p) ≤
        ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  haveI : IsProbabilityMeasure p := pairedFamily_subset_simplex
    (by have := hAllowed.2.1; omega) hp
  haveI := canonicalDecisionLaw_probability (tvFrontierProtocol n d eps) p
  have hv := tvFromUniform_paired_range d hAllowed.2.1 p hp
  have hbounded := tvFrontierEstimator_risk_le_sixteenth n d eps
    (canonicalDecisionLaw (tvFrontierProtocol n d eps) p) _ hv
  by_cases hn : n = 2
  · subst n
    apply (tvFrontierEstimator_two_risk d eps _ _ hv).trans
    apply ENNReal.ofReal_le_ofReal
    have hr := rateR_twoParticipants_lower d eps hAllowed
    nlinarith
  · by_cases hsaturated : rateR .NI n d eps = 1
    · apply hbounded.trans
      apply ENNReal.ofReal_le_ofReal
      rw [hsaturated]
      norm_num
    · by_cases hf : (frontierResources n d eps).branch = .fallbackQuarter
      · obtain ⟨hn', hdense, hfb⟩ := frontier_fallback_resources n d eps hf
        have hr := frontier_fallback_rate_lower n d eps hAllowed hn' hdense hfb
        apply hbounded.trans
        apply ENNReal.ofReal_le_ofReal
        nlinarith
      · by_cases hL : logDim d < 4096
        · by_cases hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2
          · exact tvFrontierEstimator_absMean_dense_rate n d eps hAllowed hn hL hdense p hp
          · have hr := frontier_smallDim_intermediate_rate_lower n d eps hAllowed hL
              (lt_of_not_ge hdense)
            apply hbounded.trans
            apply ENNReal.ofReal_le_ofReal
            nlinarith
        · obtain ⟨theta, htheta, rfl⟩ := hp
          have hd : 0 < d := by have := hAllowed.2.1; omega
          haveI := symmetricLaw_probability theta htheta hd
          have hmodel := symmetricLaw_causalModel theta htheta hd
          have hcontrast : contrast (symmetricLaw theta) = theta := by
            funext j
            simp only [contrast, symmetricLaw_armMean theta htheta hd, signVal,
              Bool.false_eq_true, ↓reduceIte]
            ring
          by_cases hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2
          · have hr := tvFrontierEstimator_hybrid_dense_rate hMean hCheb n d eps hAllowed
              hn (le_of_not_gt hL) hdense (canonicalScheme n d) canonicalScheme_iidPeople
              (symmetricLaw theta) hmodel
            simpa only [hcontrast] using hr
          · have hr := tvFrontierEstimator_globalPoly_rate hMean hCheb n d eps hAllowed
              hn (le_of_not_gt hL) hdense hsaturated hf
              (canonicalScheme n d) canonicalScheme_iidPeople (symmetricLaw theta) hmodel
            simpa only [hcontrast] using hr

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The explicit sign-vector procedure has finite global coverage and the square-root expected-length rate on the full paired family](goal). -/
-- @node: tvFrontier_concrete_attainment
lemma tvFrontier_concrete_attainment
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps) :
    ConcreteTvAttainment n d eps ((10 : ℝ)^16) := by
  refine ⟨tvFrontierProtocol_noninteractive n d eps hAllowed.2.2.1.le, ?_⟩
  intro p hp
  haveI : IsProbabilityMeasure p := pairedFamily_subset_simplex
    (by have := hAllowed.2.1; omega) hp
  haveI := canonicalDecisionLaw_probability (tvFrontierProtocol n d eps) p
  have hv := tvFromUniform_paired_range d hAllowed.2.1 p hp
  have hr := tvFrontierEstimator_uniform_rate hMean hCheb n d eps hAllowed p hp
  refine ⟨hr, tvFrontierInterval_coverage_of_risk n d eps hAllowed _
    (by positivity) _ _ hv hr, ?_⟩
  apply (tvFrontierInterval_expectedLength_le n d eps ((10 : ℝ)^16)
    (by positivity) _).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (Real.sqrt_le_iff).mpr
  norm_num

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The concrete paired procedure supplies the existential finite sign-vector attainment witness with the same universal constant](goal). -/
-- @node: tvFrontier_attainment
lemma tvFrontier_attainment
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps) :
    TvAttainment n d eps (rateR .NI n d eps) (rateH .NI n d eps) ((10 : ℝ)^16) := by
  have hc := tvFrontier_concrete_attainment hMean hCheb n d eps hAllowed
  refine ⟨tvFrontierProtocol n d eps, hc.1, ?_, tvFrontierEstimator n d eps,
    tvFrontierInterval n d eps ((10 : ℝ)^16), ?_, hc.2⟩
  · intro i
    exact ⟨Equiv.refl _⟩
  · refine ⟨fun z => tvFrontierEstimate n d eps (z, (0 : Fin 1), 0), ?_, ?_⟩
    · exact (tvFrontierEstimate_measurable n d eps).comp (by fun_prop)
    · intro w
      rfl

end CausalSmith.Stat.LdpOptvalueUniformFrontier
