module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TVSampling
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.UpperCalibration

/-!
# Calibration of the paired transcript norm

The paired releases omit the baseline block. Shifting them into the common norm
computation preserves the evaluation block law and its absolute-mean calibration.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the causal-model conditions for the data law](hyp:hP), [positive dimension](hyp:hd), and [the stated hend condition](hyp:hend). [Either shifted norm block selects the corresponding active paired participants](goal). -/
-- @node: tvToNormTranscript_block_law
lemma tvToNormTranscript_block_law (n d : ℕ) (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d)
    (offset : ℕ) (hend : offset + n / 3 ≤ 2*(n / 3)) :
    (canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))).map
      (fun w => frontierBlock n d eps ((frontierResources n d eps).m0 + offset)
        (tvToNormTranscript n d eps w.1)) = vectorBlockLaw P eps (n / 3) := by
  let g : Fin (n / 3) → Fin n := fun i => ⟨offset + i.val, by
    have := i.isLt
    omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [g] at this
    omega
  have hfun : (fun w : DecisionSpace (tvFrontierProtocol n d eps) =>
      frontierBlock n d eps ((frontierResources n d eps).m0 + offset)
        (tvToNormTranscript n d eps w.1)) = (fun w i => w.1 (g i)) := by
    funext w i
    have hi : (frontierResources n d eps).m0 + offset + i.val < n := by
      have := i.isLt
      simp only [frontierResources]
      omega
    have hlo : ¬(frontierDesign n d eps).resources.m0 + offset + i.val <
        (frontierDesign n d eps).resources.m0 := by omega
    have hidx : (frontierDesign n d eps).resources.m0 + offset + i.val -
        (frontierDesign n d eps).resources.m0 < n := by
      have := i.isLt
      simp only [frontierDesign, frontierResources]
      omega
    simp only [frontierBlock, messageAt, hi, ↓reduceDIte, tvToNormTranscript,
      show (frontierResources n d eps).m0 = (frontierDesign n d eps).resources.m0 from rfl,
      hlo, ↓reduceIte, hidx,
      show (frontierDesign n d eps).resources.m0 + offset + i.val < n from hi,
      Nat.add_sub_cancel_left]
    apply congrArg w.1
    apply Fin.ext
    simp [g, frontierDesign, Nat.add_assoc]
  rw [hfun]
  exact tvFrontier_vector_selection_law eps P hP hd g hg (fun i => by
    have := i.isLt
    dsimp [g]
    change offset + i.val < 2*(n / 3)
    omega)

/-- Assume [the causal-model conditions for the data law](hyp:hP), [positive dimension](hyp:hd), and [the stated hend condition](hyp:hend). [Expectations of shifted evaluation statistics are their iid calibration expectations](goal). -/
-- @node: tvToNormTranscript_block_integral
lemma tvToNormTranscript_block_integral (n d : ℕ) (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d)
    (offset : ℕ) (hend : offset + n / 3 ≤ 2*(n / 3))
    (f : (Fin (n / 3) → Fin d → Bool) → ℝ) :
    (∫ w, f (frontierBlock n d eps ((frontierResources n d eps).m0 + offset)
      (tvToNormTranscript n d eps w.1))
      ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) =
        blockMean P eps f := by
  unfold blockMean
  rw [← tvToNormTranscript_block_law n d eps P hP hd offset hend]
  have hmeas : Measurable (fun w : DecisionSpace (tvFrontierProtocol n d eps) =>
      frontierBlock n d eps ((frontierResources n d eps).m0 + offset)
        (tvToNormTranscript n d eps w.1)) := by
    letI : Countable (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
      change Countable (Fin n → Fin d → Bool)
      infer_instance
    letI : MeasurableSingletonClass (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
      change MeasurableSingletonClass (Fin n → Fin d → Bool)
      infer_instance
    exact (measurable_of_countable (fun z => frontierBlock n d eps
      ((frontierResources n d eps).m0 + offset) (tvToNormTranscript n d eps z))).comp
        measurable_fst
  exact (integral_map hmeas.aemeasurable (by fun_prop)).symm

/-- Assume [the stated hb condition](hyp:hb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hm condition](hyp:hm). [The paired absolute evaluation means inherit the finite signed-norm MSE](goal). -/
-- @node: tvFrontierNormEstimate_absMean_mse
lemma tvFrontierNormEstimate_absMean_mse (n d : ℕ) (eps : ℝ)
    (hb : (frontierResources n d eps).branch = .absMean)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < n / 3) :
    (∫ w, (frontierNormEstimate n d eps (tvToNormTranscript n d eps w.1) -
      signedNorm (contrast P))^2
      ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) ≤
        sigmaSquared d (n / 3) eps := by
  simp_rw [frontierNormEstimate_absMean n d eps hb]
  have htransfer := tvToNormTranscript_block_integral n d eps P hP (by omega)
    (n / 3) (by omega)
    (fun z => ((d : ℝ)⁻¹ * ∑ j, |scaledColumnMean eps j z| -
      signedNorm (contrast P))^2)
  change (∫ w, ((d : ℝ)⁻¹ * ∑ j, |scaledColumnMean eps j
    (frontierBlock n d eps ((frontierResources n d eps).m0 + n / 3)
      (tvToNormTranscript n d eps w.1))| - signedNorm (contrast P))^2
    ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) ≤ _
  exact htransfer.le.trans (absolute_column_average_mse_bound P hP eps heps hd hm)

/-- Assume [the stated hn condition](hyp:hn), [the causal-model conditions for the data law](hyp:hP), [dimension at least two](hyp:hd), and [the protocol decision](hyp:hMSE). [Projecting the norm statistic divided by two costs one quarter of its MSE](goal). -/
-- @node: tvFrontierEstimator_risk_le_norm_mse
lemma tvFrontierEstimator_risk_le_norm_mse (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hd : 2 ≤ d) (B : ℝ)
    (hMSE : (∫ w, (frontierNormEstimate n d eps (tvToNormTranscript n d eps w.1) -
      signedNorm (contrast P))^2
      ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) ≤ B) :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P)))
      (tvFrontierEstimator n d eps) (tvFromUniform (pairedLaw (contrast P))) ≤
        ENNReal.ofReal (B / 4) := by
  have htheta := contrast_mem_parameterCube P hP
  haveI : IsProbabilityMeasure (pairedLaw (contrast P)) :=
    pairedFamily_subset_simplex (by omega)
      (Set.mem_image_of_mem pairedLaw htheta)
  haveI : ∀ i, IsMarkovKernel (tvFrontierKernel n d eps i) := by
    intro i
    exact ⟨fun v => (tvFrontierStage_markov n d eps i).isProbabilityMeasure
      ((v,(0 : Fin 1)), fun _ => fun _ => false)⟩
  haveI : ∀ i, IsProbabilityMeasure
      ((pairedLaw (contrast P)).bind (tvFrontierKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  let L := Measure.pi (fun i => (pairedLaw (contrast P)).bind (tvFrontierKernel n d eps i))
  let f : (Fin n → Fin d → Bool) → ℝ := fun z =>
    (frontierNormEstimate n d eps (tvToNormTranscript n d eps z) - signedNorm (contrast P))^2
  have hf : Measurable f := measurable_of_countable f
  have htransfer : (∫ z, f z ∂L) =
      ∫ w, f w.1 ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P)) := by
    dsimp only [L]
    erw [← tvFrontier_sampling_transcript_product n d eps (pairedLaw (contrast P))]
    exact integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable
  have hnorm : (∫ z, f z ∂L) ≤ B := by
    rw [htransfer]
    exact hMSE
  have htarget : signedNorm (contrast P)/2 ∈ Set.Icc (0 : ℝ) (1/4) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hsum : ∑ j : Fin d, |contrast P j| ≤ (d : ℝ)*(1/2) := by
      calc
        _ ≤ ∑ _j : Fin d, (1/2 : ℝ) := Finset.sum_le_sum (fun j _ =>
          abs_le.mpr (htheta j))
        _ = _ := by simp
    have hnonneg : 0 ≤ signedNorm (contrast P) := by unfold signedNorm; positivity
    have hupper : signedNorm (contrast P) ≤ 1/2 := by
      unfold signedNorm
      calc
        _ ≤ (d : ℝ)⁻¹ * ((d : ℝ)*(1/2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by field_simp
    constructor <;> linarith
  rw [tvFrontierEstimator_risk_product n d eps (pairedLaw (contrast P)),
    tvFromUniform_pairedLaw _ htheta (by omega)]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (f z / 4) ∂L := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      change (tvFrontierEstimate n d eps (z,(0 : Fin 1),0) -
        signedNorm (contrast P)/2)^2 ≤ f z / 4
      simp only [tvFrontierEstimate, hn, ↓reduceIte]
      let x := frontierNormEstimate n d eps (tvToNormTranscript n d eps z)/2
      have hproj : (max 0 (min (1/4 : ℝ) x) - signedNorm (contrast P)/2)^2 ≤
          (x - signedNorm (contrast P)/2)^2 := by
        by_cases hlo : x ≤ 0
        · rw [min_eq_right (by linarith), max_eq_left hlo]
          nlinarith [htarget.1]
        · by_cases hhi : 1/4 ≤ x
          · rw [min_eq_left hhi, max_eq_right (by norm_num)]
            nlinarith [htarget.2]
          · rw [min_eq_right (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo)]
      exact hproj.trans_eq (by dsimp [x, f]; ring)
    _ = ENNReal.ofReal ((∫ z, f z ∂L)/4) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
        (Filter.Eventually.of_forall (fun z => by dsimp [f]; positivity))]
      congr 1
      integral_linearity
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hnorm (by norm_num))

/-- Assume [the stated hn condition](hyp:hn), [the stated hb condition](hyp:hb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hm condition](hyp:hm). [Projecting the norm statistic divided by two costs one quarter of its MSE](goal). -/
-- @node: tvFrontierEstimator_absMean_risk
lemma tvFrontierEstimator_absMean_risk (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (hb : (frontierResources n d eps).branch = .absMean)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < n / 3) :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P)))
      (tvFrontierEstimator n d eps) (tvFromUniform (pairedLaw (contrast P))) ≤
        ENNReal.ofReal (sigmaSquared d (n / 3) eps / 4) := by
  exact tvFrontierEstimator_risk_le_norm_mse n d eps hn P hP hd _
    (tvFrontierNormEstimate_absMean_mse n d eps hb P hP heps hd hm)

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), and [the stated hp condition](hyp:hp). [The dense bounded-logarithmic branch attains the paired TV risk rate on every law in the paired family, with the specified common upper constant](goal). -/
-- @node: tvFrontierEstimator_absMean_dense_rate
lemma tvFrontierEstimator_absMean_dense_rate (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) (hL : logDim d < 4096)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2)
    (p : Measure (PairedSymbol d)) (hp : p ∈ pairedFamily d) :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) p)
      (tvFrontierEstimator n d eps) (tvFromUniform p) ≤
        ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  obtain ⟨theta, htheta, rfl⟩ := hp
  have hd : 0 < d := by have := hAllowed.2.1; omega
  haveI := symmetricLaw_probability theta htheta hd
  have hmodel := symmetricLaw_causalModel theta htheta hd
  have hcontrast : contrast (symmetricLaw theta) = theta := by
    funext j
    simp only [contrast, symmetricLaw_armMean theta htheta hd, signVal,
      Bool.false_eq_true, ↓reduceIte]
    ring
  have hm : 0 < n / 3 := by have := hAllowed.1; omega
  have hrisk := tvFrontierEstimator_absMean_risk n d eps hn
    (frontier_absMean_resources n d eps hn hL) (symmetricLaw theta) hmodel
    hAllowed.2.2.1 hAllowed.2.1 hm
  rw [hcontrast] at hrisk
  apply hrisk.trans
  apply ENNReal.ofReal_le_ofReal
  have hresource := frontier_absMean_dense_resource_bound n d eps hAllowed hn hL hdense
  have ht : 0 < (n : ℝ)*eps^2 := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
    exact mul_pos hnp (sq_pos_of_pos hAllowed.2.2.1)
  have hLp := logDim_pos d hAllowed.2.1
  have hrate : 0 ≤ rateR .NI n d eps := by
    simp only [rateR, rho, if_pos hdense]
    positivity
  have hnoise : 0 ≤ sigmaSquared d (n / 3) eps := by unfold sigmaSquared; positivity
  have hbase : 0 ≤ 24 / ((n : ℝ)*eps^2) := by positivity
  nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the stated hn condition](hyp:hn), [the stated hb condition](hyp:hb), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hm condition](hyp:hm), [the stated even condition](hyp:hEven), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated degree condition](hyp:hDegree). [The shifted paired evaluation block inherits the global polynomial MSE, including its finite-degree variance and approximation terms](goal). -/
-- @node: tvFrontierNormEstimate_globalPoly_mse
lemma tvFrontierNormEstimate_globalPoly_mse
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (hb : (frontierResources n d eps).branch = .globalPoly)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hAllowed : Allowed n d eps) (hm : 0 < n / 3)
    (hEven : Even (frontierResources n d eps).degree)
    (hD : 2 ≤ (frontierResources n d eps).degree)
    (hmD : 2*(frontierResources n d eps).degree ≤ n / 3)
    (hDegree : ((frontierResources n d eps).degree : ℝ) ≤
      (1/1024 : ℝ) * logDim d /
        Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) :
    (∫ w, (frontierNormEstimate n d eps (tvToNormTranscript n d eps w.1) -
      signedNorm (contrast P))^2
      ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) ≤
      Real.exp (9*(frontierResources n d eps).degree*
        Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d))/(2*d) +
        (1/((frontierResources n d eps).degree+1 : ℝ))^2 := by
  have hradius : (frontierResources n d eps).radius = (1/2 : ℝ) := by
    by_cases hsmall : logDim d < 4096
    · simp [frontierResources, hn, hsmall] at hb
    · by_cases hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2
      · simp [frontierResources, hn, hsmall, hdense] at hb
      · simp [frontierResources, hdense]
  simp_rw [frontierNormEstimate_globalPoly n d eps hb, hradius,
    ← frontierPolynomialEstimate_eq_polynomialEstimate]
  have htransfer := tvToNormTranscript_block_integral n d eps P hP
    (by have := hAllowed.2.1; omega) (n / 3) (by omega)
    (fun z => ((d : ℝ)⁻¹ * ∑ j, frontierPolynomialEstimate eps (1/2)
      (frontierResources n d eps).degree j z - signedNorm (contrast P))^2)
  simp only [frontierResources] at htransfer ⊢
  exact htransfer.le.trans (frontierPolynomial_average_mse_bound hMean hCheb S hIID P hP
    eps hAllowed hm (by omega) _ hEven hD hmD hDegree)

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), [the protocol-class label](hyp:hsaturated), [the stated hf condition](hyp:hf), [independent and identically distributed participant records](hyp:hIID), and [the causal-model conditions for the data law](hyp:hP). [The concrete paired global-polynomial branch attains the finite-resource risk rate after projection, using the same selected degree as the causal norm](goal). -/
-- @node: tvFrontierEstimator_globalPoly_rate
lemma tvFrontierEstimator_globalPoly_rate
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (hL : 4096 ≤ logDim d)
    (hdense : ¬ (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2)
    (hsaturated : rateR .NI n d eps ≠ 1)
    (hf : (frontierResources n d eps).branch ≠ .fallbackQuarter)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P)))
      (tvFrontierEstimator n d eps) (tvFromUniform (pairedLaw (contrast P))) ≤
        ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  have hm : 0 < n / 3 := by have := hAllowed.1; omega
  obtain ⟨hb, hEven, hD, hDegree, hLower⟩ := frontier_global_rounding
    n d eps hAllowed hn hL hdense hf
  have hmD := frontier_global_moment_fit n d eps hAllowed hn hD hDegree
  have hDegree' : ((frontierResources n d eps).degree : ℝ) ≤
      (1/1024 : ℝ) * logDim d /
        Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d) := by
    convert hDegree using 1 <;> first | rfl | ring
  have hNorm := tvFrontierNormEstimate_globalPoly_mse hMean hCheb n d eps hn hb
    S hIID P hP hAllowed hm hEven hD hmD hDegree'
  apply (tvFrontierEstimator_risk_le_norm_mse n d eps hn P hP hAllowed.2.1 _ hNorm).trans
  apply ENNReal.ofReal_le_ofReal
  have hresource := frontier_global_resource_bound n d eps hAllowed hn hL hdense
    hsaturated hDegree hLower
  have hnoise : 0 ≤ Real.exp (9*(frontierResources n d eps).degree *
      Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d))/(2*d) +
      (1/((frontierResources n d eps).degree+1 : ℝ))^2 := by positivity
  have hbase : 0 ≤ 24 / ((n : ℝ)*eps^2) := by positivity
  nlinarith

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [positive dimension](hyp:hd). [The two shifted paired blocks have the calibrated independent hybrid expectation](goal). -/
-- @node: tvToNormTranscript_blocks_integral
lemma tvToNormTranscript_blocks_integral (n d : ℕ) (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d)
    (f : ((Fin (n / 3) → Fin d → Bool) × (Fin (n / 3) → Fin d → Bool)) → ℝ) :
    (∫ w, f (frontierBlock n d eps (frontierResources n d eps).m0
        (tvToNormTranscript n d eps w.1),
      frontierBlock n d eps ((frontierResources n d eps).m0 +
        (frontierResources n d eps).m) (tvToNormTranscript n d eps w.1))
      ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) =
        hybridMean P eps f := by
  let g : Fin (n / 3 + n / 3) → Fin n := fun i => ⟨i.val, by
    have := i.isLt
    omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    exact h
  have hlaw := tvFrontier_vector_selection_law eps P hP hd g hg
    (fun i => by have := i.isLt; dsimp [g]; simp only [frontierDesign, frontierResources]; omega)
  have htransfer :
      (∫ w, f (splitHybridRows (fun i => w.1 (g i)))
        ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) =
      blockMean P eps (fun z => f (splitHybridRows z)) := by
    unfold blockMean
    rw [← hlaw]
    exact (integral_map (μ := canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P)))
      (φ := fun w : DecisionSpace (tvFrontierProtocol n d eps) =>
        (fun i => w.1 (g i) : Fin (n / 3 + n / 3) → Fin d → Bool))
      (f := fun z => f (splitHybridRows z)) (by fun_prop)
      (by
        change AEStronglyMeasurable
          (fun z : Fin (n / 3 + n / 3) → Fin d → Bool => f (splitHybridRows z)) _
        exact (measurable_of_countable _).aestronglyMeasurable)).symm
  have hblock (z : ProtocolTranscript (tvFrontierProtocol n d eps))
      (offset : ℕ) (hend : offset + n / 3 ≤ 2*(n / 3)) (i : Fin (n / 3)) :
      frontierBlock n d eps ((frontierResources n d eps).m0 + offset)
        (tvToNormTranscript n d eps z) i =
      z ⟨offset + i.val, by have := i.isLt; omega⟩ := by
    have hi : (frontierResources n d eps).m0 + offset + i.val < n := by
      have := i.isLt
      simp only [frontierResources]
      omega
    have hlo : ¬(frontierDesign n d eps).resources.m0 + offset + i.val <
        (frontierDesign n d eps).resources.m0 := by omega
    have hidx : (frontierDesign n d eps).resources.m0 + offset + i.val -
        (frontierDesign n d eps).resources.m0 < n := by
      have := i.isLt
      simp only [frontierDesign, frontierResources]
      omega
    simp only [frontierBlock, messageAt, hi, ↓reduceDIte, tvToNormTranscript,
      show (frontierResources n d eps).m0 = (frontierDesign n d eps).resources.m0 from rfl,
      hlo, ↓reduceIte, hidx,
      show (frontierDesign n d eps).resources.m0 + offset + i.val < n from hi,
      Nat.add_sub_cancel_left]
    apply congrArg z
    apply Fin.ext
    simp [frontierDesign, Nat.add_assoc]
  have hpair (w : DecisionSpace (tvFrontierProtocol n d eps)) :
      (frontierBlock n d eps (frontierResources n d eps).m0 (tvToNormTranscript n d eps w.1),
        frontierBlock n d eps ((frontierResources n d eps).m0 +
          (frontierResources n d eps).m) (tvToNormTranscript n d eps w.1)) =
      splitHybridRows (fun i => w.1 (g i)) := by
    apply Prod.ext
    · funext i
      have h := hblock w.1 0 (by omega) i
      change frontierBlock n d eps (frontierResources n d eps).m0
        (tvToNormTranscript n d eps w.1) i = w.1 (g (Fin.castAdd (n / 3) i))
      simpa only [Nat.add_zero] using h.trans (congrArg w.1 (by
        apply Fin.ext
        simp [g]))
    · funext i
      simpa only [frontierResources, splitHybridRows, g, Nat.add_comm, Fin.val_natAdd] using
        hblock w.1 (n / 3) (by omega) i
  simp_rw [hpair]
  exact htransfer.trans (hybridMean_eq_combined_blockMean P eps f).symm

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the stated hb condition](hyp:hb), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hm condition](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), and [the stated hm d condition](hyp:hmD). [The paired hybrid statistic inherits the finite pilot/evaluation norm calibration](goal). -/
-- @node: tvFrontierNormEstimate_hybrid_mse
lemma tvFrontierNormEstimate_hybrid_mse
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ)
    (hb : (frontierResources n d eps).branch = .hybrid)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hAllowed : Allowed n d eps) (hm : 0 < n / 3) (hL : 4096 ≤ logDim d)
    (hD : (frontierResources n d eps).degree = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊)
    (hmD : 2*(frontierResources n d eps).degree ≤ n / 3) :
    (∫ w, (frontierNormEstimate n d eps (tvToNormTranscript n d eps w.1) -
      signedNorm (contrast P))^2
      ∂canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P))) ≤
        500000000 * sigmaSquared d (n / 3) eps / logDim d := by
  have hstat (w : DecisionSpace (tvFrontierProtocol n d eps)) :=
    frontierNormEstimate_hybrid n d eps hb (tvToNormTranscript n d eps w.1)
  simp_rw [hstat]
  have htransfer := tvToNormTranscript_blocks_integral n d eps P hP
    (by have := hAllowed.2.1; omega)
    (fun z => ((d : ℝ)⁻¹ * ∑ j, hybridColumn eps
      (frontierResources n d eps).degree j z - signedNorm (contrast P))^2)
  exact htransfer.le.trans (hybrid_average_mse_bound hMean hCheb S hIID P hP eps
    hAllowed hm _ hL hD hmD (by omega))

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), [independent and identically distributed participant records](hyp:hIID), and [the causal-model conditions for the data law](hyp:hP). [Projection of the paired hybrid norm attains the dense large-dimension TV rate](goal). -/
-- @node: tvFrontierEstimator_hybrid_dense_rate
lemma tvFrontierEstimator_hybrid_dense_rate
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (hL : 4096 ≤ logDim d)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P) :
    squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) (pairedLaw (contrast P)))
      (tvFrontierEstimator n d eps) (tvFromUniform (pairedLaw (contrast P))) ≤
        ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := by
  have hm : 0 < n / 3 := by have := hAllowed.1; omega
  obtain ⟨hb, hD, hmD⟩ := frontier_hybrid_resources n d eps hAllowed hn hL hdense
  have hNorm := tvFrontierNormEstimate_hybrid_mse hMean hCheb n d eps hb S hIID
    P hP hAllowed hm hL hD hmD
  apply (tvFrontierEstimator_risk_le_norm_mse n d eps hn P hP hAllowed.2.1 _ hNorm).trans
  apply ENNReal.ofReal_le_ofReal
  have hresource := frontier_hybrid_dense_resource_bound n d eps hAllowed hn hdense
  have hnoise : 0 ≤ 500000000 * sigmaSquared d (n / 3) eps / logDim d := by
    have := logDim_pos d hAllowed.2.1
    unfold sigmaSquared
    positivity
  have hbase : 0 ≤ 24 / ((n : ℝ)*eps^2) := by positivity
  nlinarith

end CausalSmith.Stat.LdpOptvalueUniformFrontier
