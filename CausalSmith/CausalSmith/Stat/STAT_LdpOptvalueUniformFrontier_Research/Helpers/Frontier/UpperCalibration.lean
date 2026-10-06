module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.GlobalResources
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.NormCalibration
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.BaselineCalibration

/-!
# Bounded-loss branches of the concrete frontier construction

Projection bounds the loss without moment calibration in the saturated regime.
The two-participant constant procedure also satisfies the prescribed risk rate.
Resource comparisons also close the insufficient-degree fallback and both
bounded-logarithmic-dimension branches. The dense absolute-mean and hybrid proofs combine
the actual transcript component MSEs. The intermediate global-polynomial proof
uses the selected degree and finite-block resource comparisons.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [Every branch of the concrete estimate lies in the causal target domain](goal). -/
-- @node: frontierEstimate_range
lemma frontierEstimate_range (n d : ℕ) (eps : ℝ)
    (w : DecisionSpace (frontierProtocol n d eps)) :
    frontierEstimate n d eps w ∈ Set.Icc (1/4 : ℝ) (3/4) := by
  unfold frontierEstimate
  split_ifs
  · norm_num
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Assume [the stated hv condition](hyp:hv). [Projection bounds squared risk uniformly, under any probability decision law](goal). -/
-- @node: frontierEstimator_risk_le_quarter
lemma frontierEstimator_risk_le_quarter (n d : ℕ) (eps : ℝ)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (frontierEstimator n d eps) v ≤ ENNReal.ofReal (1/4 : ℝ) := by
  unfold squaredRisk
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (1/4 : ℝ) ∂L := by
      apply lintegral_mono
      intro w
      apply ENNReal.ofReal_le_ofReal
      have hw := frontierEstimate_range n d eps w
      have hdist := abs_sub_le_of_le_of_le hw.1 hw.2 hv.1 hv.2
      change (frontierEstimate n d eps w - v)^2 ≤ (1/4 : ℝ)
      nlinarith [sq_abs (frontierEstimate n d eps w - v),
        abs_nonneg (frontierEstimate n d eps w - v)]
    _ = _ := by simp

/-- Assume [the stated hv condition](hyp:hv). [The two-participant constant estimate has worst-case squared risk at most 1/16](goal). -/
-- @node: frontierEstimator_twoParticipants_risk
lemma frontierEstimator_twoParticipants_risk (d : ℕ) (eps : ℝ)
    (L : Measure (DecisionSpace (frontierProtocol 2 d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (frontierEstimator 2 d eps) v ≤ ENNReal.ofReal (1/16 : ℝ) := by
  have hloss : (1/2 - v)^2 ≤ (1/16 : ℝ) := by
    nlinarith [hv.1, hv.2, mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)]
  unfold squaredRisk
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (1/16 : ℝ) ∂L := by
      apply lintegral_mono
      intro w
      apply ENNReal.ofReal_le_ofReal
      simpa only [frontierEstimator, frontierEstimate, ↓reduceIte] using hloss
    _ = _ := by simp

/-- Assume [the stated allowed condition](hyp:hAllowed). [With two participants the elementary lower comparison keeps the rate above 1/2](goal). -/
-- @node: rateR_twoParticipants_lower
lemma rateR_twoParticipants_lower (d : ℕ) (eps : ℝ) (hAllowed : Allowed 2 d eps) :
    (1/2 : ℝ) ≤ rateR .NI 2 d eps := by
  have ht : 0 < (2 : ℝ) * eps^2 := mul_pos (by norm_num) (sq_pos_of_pos hAllowed.2.2.1)
  have htUpper : (2 : ℝ) * eps^2 ≤ 2 := by
    nlinarith [hAllowed.2.2.1, hAllowed.2.2.2]
  have hinv : (1/2 : ℝ) ≤ 1 / ((2 : ℝ) * eps^2) := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  exact (le_min (by norm_num) hinv).trans
    (rho_elementary_comparisons 2 d eps hAllowed).1

/-- Assume [the stated allowed condition](hyp:hAllowed) and [the stated hv condition](hyp:hv). [The constant branch attains the same universal upper-risk constant](goal). -/
-- @node: frontierEstimator_twoParticipants_rate
lemma frontierEstimator_twoParticipants_rate (d : ℕ) (eps : ℝ)
    (hAllowed : Allowed 2 d eps)
    (L : Measure (DecisionSpace (frontierProtocol 2 d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (frontierEstimator 2 d eps) v ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI 2 d eps) := by
  apply (frontierEstimator_twoParticipants_risk d eps L v hv).trans
  apply ENNReal.ofReal_le_ofReal
  have hr := rateR_twoParticipants_lower d eps hAllowed
  nlinarith

/-- Assume [the protocol-class label](hyp:hsaturated) and [the stated hv condition](hyp:hv). [At saturation, projection alone attains the prescribed upper-risk bound](goal). -/
-- @node: frontierEstimator_saturated_rate
lemma frontierEstimator_saturated_rate (n d : ℕ) (eps : ℝ)
    (hsaturated : rateR .NI n d eps = 1)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (frontierEstimator n d eps) v ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  apply (frontierEstimator_risk_le_quarter n d eps L v hv).trans
  apply ENNReal.ofReal_le_ofReal
  rw [hsaturated]
  norm_num

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hb condition](hyp:hb), and [the stated hv condition](hyp:hv). [The insufficient-degree fallback satisfies the fixed final risk constant](goal). -/
-- @node: frontierEstimator_fallback_rate
lemma frontierEstimator_fallback_rate (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps)
    (hb : (frontierResources n d eps).branch = .fallbackQuarter)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (frontierEstimator n d eps) v ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  obtain ⟨hn, hdense, hf⟩ := frontier_fallback_resources n d eps hb
  have hr := frontier_fallback_rate_lower n d eps hAllowed hn hdense hf
  apply (frontierEstimator_risk_le_quarter n d eps L v hv).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated l condition](hyp:hL), [the stated hbranch condition](hyp:hbranch), and [the stated hv condition](hyp:hv). [In bounded logarithmic dimension the intermediate branch needs only projection](goal). -/
-- @node: frontierEstimator_smallDim_intermediate_rate
lemma frontierEstimator_smallDim_intermediate_rate (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hL : logDim d < 4096)
    (hbranch : (n : ℝ) * eps ^ 2 < (d : ℝ)^2 * logDim d)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (frontierEstimator n d eps) v ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  have hr := frontier_smallDim_intermediate_rate_lower n d eps hAllowed hL hbranch
  apply (frontierEstimator_risk_le_quarter n d eps L v hv).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith

/-- Assume [the stated allowed condition](hyp:hAllowed). [The two-participant interval is the full target domain, as prescribed by the roadmap](goal). -/
-- @node: frontierInterval_twoParticipants_full
lemma frontierInterval_twoParticipants_full (d : ℕ) (eps : ℝ)
    (hAllowed : Allowed 2 d eps)
    (w : DecisionSpace (frontierProtocol 2 d eps)) :
    (frontierInterval 2 d eps).lo w = (1/4 : ℝ) ∧
      (frontierInterval 2 d eps).hi w = (3/4 : ℝ) := by
  have hr := rateR_twoParticipants_lower d eps hAllowed
  have hqnonneg : 0 ≤ frontierHonestyRadius 2 d eps := Real.sqrt_nonneg _
  have hq2 : (frontierHonestyRadius 2 d eps)^2 =
      (10 : ℝ)^17 * rateR .NI 2 d eps := by
    apply Real.sq_sqrt
    exact mul_nonneg (by positivity) (le_trans (by norm_num) hr)
  have hq : (1/4 : ℝ) ≤ frontierHonestyRadius 2 d eps := by
    nlinarith
  change max (1/4) (frontierEstimate 2 d eps w - frontierHonestyRadius 2 d eps) = _ ∧
    min (3/4) (frontierEstimate 2 d eps w + frontierHonestyRadius 2 d eps) = _
  simp only [frontierEstimate, ↓reduceIte]
  exact ⟨max_eq_left (by linarith), min_eq_left (by linarith)⟩

/-- Assume [the stated hn condition](hyp:hn) and [the stated l condition](hyp:hL). [Small logarithmic dimension selects the absolute evaluation means](goal). -/
-- @node: frontier_absMean_resources
lemma frontier_absMean_resources (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (hL : logDim d < 4096) :
    (frontierResources n d eps).branch = .absMean := by
  simp only [frontierResources, if_neg hn, if_pos hL]

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), and [the stated hdense condition](hyp:hdense). [The dense small-dimension comparison absorbs baseline and vector noise, with the constant stated in the constructive proof roadmap](goal). -/
-- @node: frontier_absMean_dense_resource_bound
lemma frontier_absMean_dense_resource_bound (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) (hL : logDim d < 4096)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2) :
    24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) * sigmaSquared d (n / 3) eps ≤
      (64 * 4096 : ℝ) * rateR .NI n d eps := by
  have ht : 0 < (n : ℝ) * eps^2 := by
    have hnp : (0 : ℝ) < n := by
      exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
    exact mul_pos hnp (sq_pos_of_pos hAllowed.2.2.1)
  have hLp := logDim_pos d hAllowed.2.1
  have hd : (2 : ℝ) ≤ d := by exact_mod_cast hAllowed.2.1
  have hnoise := frontier_sigmaSquared_upper n d eps hAllowed hn
  have hinv : 1 / ((n : ℝ) * eps^2) ≤ (d : ℝ)^2 / ((n : ℝ) * eps^2) :=
    div_le_div_of_nonneg_right (by nlinarith) ht.le
  have hr : rateR .NI n d eps =
      (d : ℝ)^2 / (((n : ℝ) * eps^2) * logDim d) := by
    simp only [rateR, rho, if_pos hdense]
  have hr0 : 0 ≤ rateR .NI n d eps := by rw [hr]; positivity
  have hscale : (d : ℝ)^2 / ((n : ℝ) * eps^2) =
      logDim d * rateR .NI n d eps := by
    rw [hr]
    field_simp
  calc
    _ ≤ 24 * (1 / ((n : ℝ) * eps^2)) +
        (1/2 : ℝ) * (80 * ((d : ℝ)^2 / ((n : ℝ) * eps^2))) := by
      apply add_le_add
      · exact le_of_eq (by ring)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [mul_div_assoc] using hnoise
    _ ≤ 64 * ((d : ℝ)^2 / ((n : ℝ) * eps^2)) := by linarith
    _ = 64 * logDim d * rateR .NI n d eps := by rw [hscale]; ring
    _ ≤ _ := by nlinarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The concrete absolute-mean branch attains the dense small-dimension risk bound by combining its calibrated norm MSE with the binary baseline MSE](goal). -/
-- @node: frontierEstimator_absMean_dense_rate
lemma frontierEstimator_absMean_dense_rate (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) (hL : logDim d < 4096)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    squaredRisk (decisionLaw S (frontierProtocol n d eps) P)
      (frontierEstimator n d eps) (value P) ≤
        ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  haveI := sampling_decisionLaw_probability S hIID hRandom (frontierProtocol n d eps) P hP
  have hm : 0 < n / 3 := by have := hAllowed.1; omega
  haveI : IsProbabilityMeasure
      (Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) := by
    rw [← frontier_sampling_transcript_product n d eps S hIID hRandom P hP]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  rw [frontierEstimator_risk_product n d eps S hIID hRandom P hP]
  apply (frontier_product_risk_le_components n d eps hn P hP hAllowed.2.1 _).trans
  apply ENNReal.ofReal_le_ofReal
  have hBaseline := frontierBaselineEstimate_mse_rate n d eps hAllowed hn P
  have hNorm := frontierNormEstimate_absMean_mse n d eps hn
    (frontier_absMean_resources n d eps hn hL) P hP hAllowed.2.2.1 hAllowed.2.1 hm
  have hResource := frontier_absMean_dense_resource_bound n d eps hAllowed hn hL hdense
  have hLp := logDim_pos d hAllowed.2.1
  have hr0 : 0 ≤ rateR .NI n d eps := by
    simp only [rateR, rho, if_pos hdense]
    positivity
  calc
    _ ≤ 24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) * sigmaSquared d (n / 3) eps := by
      apply add_le_add
      · convert mul_le_mul_of_nonneg_left hBaseline
          (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
      · exact mul_le_mul_of_nonneg_left hNorm (by norm_num)
    _ ≤ (64 * 4096 : ℝ) * rateR .NI n d eps := hResource
    _ ≤ _ := by nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [The dense hybrid branch combines actual component calibration with the resource comparisons, using the same public design as the roadmap](goal). -/
-- @node: frontierEstimator_hybrid_dense_rate
lemma frontierEstimator_hybrid_dense_rate
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (hL : 4096 ≤ logDim d)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    squaredRisk (decisionLaw S (frontierProtocol n d eps) P)
      (frontierEstimator n d eps) (value P) ≤
        ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  haveI := sampling_decisionLaw_probability S hIID hRandom (frontierProtocol n d eps) P hP
  have hm : 0 < n / 3 := by have := hAllowed.1; omega
  obtain ⟨hb, hD, hmD⟩ := frontier_hybrid_resources n d eps hAllowed hn hL hdense
  haveI : IsProbabilityMeasure
      (Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) := by
    rw [← frontier_sampling_transcript_product n d eps S hIID hRandom P hP]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  rw [frontierEstimator_risk_product n d eps S hIID hRandom P hP]
  apply (frontier_product_risk_le_components n d eps hn P hP hAllowed.2.1 _).trans
  apply ENNReal.ofReal_le_ofReal
  have hBaseline := frontierBaselineEstimate_mse_rate n d eps hAllowed hn P
  have hNorm := frontierNormEstimate_hybrid_mse hMean hCheb n d eps hn hb S hIID
    P hP hAllowed hm hL hD hmD
  calc
    _ ≤ 24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) *
        (500000000 * sigmaSquared d (n / 3) eps / logDim d) := by
      apply add_le_add
      · convert mul_le_mul_of_nonneg_left hBaseline
          (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
      · exact mul_le_mul_of_nonneg_left hNorm (by norm_num)
    _ ≤ _ := frontier_hybrid_dense_resource_bound n d eps hAllowed hn hdense

variable {n d : ℕ} {eps : ℝ}

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb_of_gate) and [the bounded-mean concentration inequality](hyp:hMean_of_gate). [Upper orders attained by the explicit original-input construction](goal). -/
-- @node: frontier_upper_of_gate
lemma frontier_upper_of_gate (hCheb_of_gate : CaiLowChebyshevApproximation)
    (hMean_of_gate : BoundedMeanConcentration) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ (S : SamplingScheme n d), IidPeople S → IndependentRandomness S →
      NoninteractiveClass (frontierProtocol n d eps) eps ∧
      ∀ P ∈ causalClass d,
        squaredRisk (decisionLaw S (frontierProtocol n d eps) P) (frontierEstimator n d eps)
          (value P) ≤
          ENNReal.ofReal (C0*rateR .NI n d eps) ∧
        (0.90 : ℝ) ≤ coverage (decisionLaw S (frontierProtocol n d eps) P)
          (frontierInterval n d eps) (value P) ∧
        expectedLength (decisionLaw S (frontierProtocol n d eps) P) (frontierInterval n d eps) ≤
          ENNReal.ofReal (Real.sqrt (40*C0)*rateH .NI n d eps) := by
  refine ⟨(10 : ℝ)^16, by positivity, ?_⟩
  intro n d eps hAllowed S hIID hRandom
  refine ⟨frontierProtocol_noninteractive n d eps hAllowed.2.2.1.le, ?_⟩
  intro P hP
  letI := hP.1
  haveI := sampling_decisionLaw_probability S hIID hRandom (frontierProtocol n d eps) P hP.2
  have hRisk : squaredRisk (decisionLaw S (frontierProtocol n d eps) P)
      (frontierEstimator n d eps) (value P) ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
    by_cases hn : n = 2
    · subst n
      exact frontierEstimator_twoParticipants_rate d eps hAllowed _ (value P)
        (causal_value_range P hP.2 (by have := hAllowed.2.1; omega))
    · by_cases hsaturated : rateR .NI n d eps = 1
      · exact frontierEstimator_saturated_rate n d eps hsaturated _ (value P)
          (causal_value_range P hP.2 (by have := hAllowed.2.1; omega))
      · by_cases hf : (frontierResources n d eps).branch = .fallbackQuarter
        · exact frontierEstimator_fallback_rate n d eps hAllowed hf _ (value P)
            (causal_value_range P hP.2 (by have := hAllowed.2.1; omega))
        · by_cases hSmall : logDim d < 4096 ∧
              (n : ℝ) * eps ^ 2 < (d : ℝ)^2 * logDim d
          · exact frontierEstimator_smallDim_intermediate_rate n d eps hAllowed
              hSmall.1 hSmall.2 _ (value P)
              (causal_value_range P hP.2 (by have := hAllowed.2.1; omega))
          · by_cases hL : logDim d < 4096
            · exact frontierEstimator_absMean_dense_rate n d eps hAllowed hn hL
                (by by_contra hdense; exact hSmall ⟨hL, lt_of_not_ge hdense⟩)
                S hIID hRandom P hP.2
            · by_cases hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2
              · exact frontierEstimator_hybrid_dense_rate hMean_of_gate hCheb_of_gate
                  n d eps hAllowed hn (le_of_not_gt hL) hdense S hIID hRandom P hP.2
              · haveI : IsProbabilityMeasure
                    (Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) := by
                  rw [← frontier_sampling_transcript_product n d eps S hIID hRandom P hP.2]
                  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                rw [frontierEstimator_risk_product n d eps S hIID hRandom P hP.2]
                apply (frontier_product_risk_le_components n d eps hn P hP.2
                  (by have := hAllowed.2.1; omega) _).trans
                apply ENNReal.ofReal_le_ofReal
                have hBaseline := frontierBaselineEstimate_mse_rate n d eps hAllowed hn P
                calc
                  _ ≤ 24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) *
                      (∫ z, (frontierNormEstimate n d eps z - signedNorm (contrast P))^2
                        ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) := by
                    apply add_le_add
                    · convert mul_le_mul_of_nonneg_left hBaseline
                        (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> first | rfl | ring
                    · exact le_rfl
                  _ ≤ _ := by
                    have hm : 0 < n / 3 := by have := hAllowed.1; omega
                    obtain ⟨hb, hEven, hD, hDegree, hLower⟩ := frontier_global_rounding
                      n d eps hAllowed hn (le_of_not_gt hL) hdense hf
                    have hmD := frontier_global_moment_fit n d eps hAllowed hn hD hDegree
                    have hDegree' : ((frontierResources n d eps).degree : ℝ) ≤
                        (1/1024 : ℝ) * logDim d /
                          Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d) := by
                      convert hDegree using 1 <;> first | rfl | ring
                    have hNorm := frontierNormEstimate_globalPoly_mse hMean_of_gate
                      hCheb_of_gate n d eps hn hb S hIID P hP.2 hAllowed hm
                      hEven hD hmD hDegree'
                    calc
                      _ ≤ 24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) *
                          (Real.exp (9*(frontierResources n d eps).degree *
                            Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d))/(2*d) +
                            (1/((frontierResources n d eps).degree+1 : ℝ))^2) := by
                        apply add_le_add
                        · exact le_rfl
                        · exact mul_le_mul_of_nonneg_left hNorm (by norm_num)
                      _ ≤ _ := frontier_global_resource_bound n d eps hAllowed hn
                        (le_of_not_gt hL) hdense hsaturated hDegree hLower
  exact ⟨hRisk, frontierInterval_coverage_of_risk n d eps hAllowed _ (value P)
    (causal_value_range P hP.2 (by have := hAllowed.2.1; omega)) hRisk,
    frontierInterval_rate_length n d eps _⟩


end CausalSmith.Stat.LdpOptvalueUniformFrontier
