module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellProtocol
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellAttainment
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.NormCalibration

/-!
# MSEs for the half-block protocol

Independent participant rows yield the binary baseline MSE, and extraction of
the remaining vector rows transfers the existing coordinate mean and variance
calculation. These estimates provide the two-cell attainment certificate.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [Every attaining row is a probability kernel, in the binary or vector branch](goal). -/
-- @node: twoCellKernel_markov
lemma twoCellKernel_markov (n d : ℕ) (eps : ℝ) (i : Fin n) :
    IsMarkovKernel (twoCellKernel n d eps i) := by
  exact ⟨fun o => (twoCellStage_markov n d eps i).isProbabilityMeasure
    ((o, (0 : Fin 1)), fun _ => (false, fun _ => false))⟩

/-- Assume [the stated hi condition](hyp:hi). [A baseline row releases a sign with the randomized-response conditional mean](goal). -/
-- @node: twoCellKernel_baseline_sign_mean
lemma twoCellKernel_baseline_sign_mean (n d : ℕ) (eps : ℝ)
    (i : Fin n) (hi : i.val < (n / 2)) (o : ObsRecord d) :
    (∫ z, signVal z.1 ∂twoCellKernel n d eps i o) =
      privacyDelta eps * signVal o.2.2 := by
  classical
  letI := twoCellKernel_markov n d eps i
  rw [integral_fintype Integrable.of_finite]
  change (∑ z, (atomLaw (twoCellMass n d eps i o)).real {z} * signVal z.1) = _
  have hm : ∀ z, 0 ≤ twoCellMass n d eps i o z := by
    intro z
    simp only [twoCellMass, hi, ↓reduceIte]
    exact mul_nonneg (binaryOutcomeMass_nonneg eps o.2.2 z.1) (by split <;> positivity)
  simp only [measureReal_def, atomLaw_singleton, ENNReal.toReal_ofReal (hm _)]
  simp only [twoCellMass, hi, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [signVal]
  ring

/-- Assume [the stated hi condition](hyp:hi). [Averaging original records gives the baseline row's unconditional mean](goal). -/
-- @node: twoCell_baseline_row_mean
lemma twoCell_baseline_row_mean (n d : ℕ) (eps : ℝ)
    (i : Fin n) (hi : i.val < (n / 2))
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    (∫ z, signVal z.1 ∂(observedLaw P).bind (twoCellKernel n d eps i)) =
      privacyDelta eps * (2 * baseline P - 1) := by
  letI := twoCellKernel_markov n d eps i
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  change (∫ z, signVal z.1
    ∂((twoCellKernel n d eps i) ∘ₖ Kernel.const Unit (observedLaw P)) ()) = _
  rw [Kernel.integral_comp Integrable.of_finite]
  simp_rw [twoCellKernel_baseline_sign_mean n d eps i hi]
  rw [integral_const_mul]
  change privacyDelta eps * (∫ o, signVal o.2.2 ∂observedLaw P) = _
  rw [observed_outcome_sign_mean]

/-- [Averaging any attaining row over a probability input law preserves mass one](goal). -/
-- @node: twoCell_averaged_row_probability
lemma twoCell_averaged_row_probability (n d : ℕ) (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (i : Fin n) :
    IsProbabilityMeasure ((observedLaw P).bind (twoCellKernel n d eps i)) := by
  letI := twoCellKernel_markov n d eps i
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
    (Filter.Eventually.of_forall (fun _ => inferInstance))

/-- Assume [the stated hg condition](hyp:hg) and [the stated hbase condition](hyp:hbase). [Distinct baseline rows have additive variances and the prescribed total mean](goal). -/
-- @node: twoCell_baseline_sum_moments
lemma twoCell_baseline_sum_moments {n d k : ℕ} (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hbase : ∀ i, (g i).val < (n / 2)) :
    let L := Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))
    (∫ z, ∑ i, signVal (z (g i)).1 ∂L) =
        (k : ℝ) * (privacyDelta eps * (2 * baseline P - 1)) ∧
      variance (fun z => ∑ i, signVal (z (g i)).1) L ≤ k := by
  classical
  let μ := fun i => (observedLaw P).bind (twoCellKernel n d eps i)
  letI : ∀ i, IsProbabilityMeasure (μ i) :=
    fun i => twoCell_averaged_row_probability n d eps P i
  change (∫ z, ∑ i, signVal (z (g i)).1 ∂Measure.pi μ) = _ ∧ _
  have hmean : ∀ i, (∫ z, signVal (z (g i)).1 ∂Measure.pi μ) =
      privacyDelta eps * (2 * baseline P - 1) := by
    intro i
    rw [integral_comp_eval (μ := μ) (i := g i)
      (f := fun z : FrontierMessage d => signVal z.1) (by fun_prop)]
    exact twoCell_baseline_row_mean n d eps (g i) (hbase i) P
  have hind := (iIndepFun_pi (μ := μ)
    (X := fun (_ : Fin n) (z : FrontierMessage d) => signVal z.1)
    (fun _ => (by fun_prop))).precomp hg
  have hvar : ∀ i, variance (fun z => signVal (z (g i)).1) (Measure.pi μ) ≤ 1 := by
    intro i
    have h := variance_le_expectation_sq
      (μ := Measure.pi μ) (X := fun z => signVal (z (g i)).1)
      ((show MemLp (fun z => signVal (z (g i)).1) 2 (Measure.pi μ)
        from MemLp.of_discrete).aestronglyMeasurable)
    have hs : ∀ z : Fin n → FrontierMessage d, (signVal (z (g i)).1)^2 = 1 := by
      intro z
      cases h : (z (g i)).1 <;> norm_num [signVal, h]
    simpa [Pi.pow_apply, hs] using h
  constructor
  · rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have hv := IndepFun.variance_sum (s := Finset.univ)
      (X := fun i z => signVal (z (g i)).1) (μ := Measure.pi μ)
      (fun _ _ => MemLp.of_discrete) (fun i _ j _ hij => hind.indepFun hij)
    change variance (fun z => ∑ i, signVal (z (g i)).1) (Measure.pi μ) ≤ _
    have hv' : variance (fun z => ∑ i, signVal (z (g i)).1) (Measure.pi μ) =
        ∑ i, variance (fun z => signVal (z (g i)).1) (Measure.pi μ) := by
      convert hv using 1
      congr 1
      funext z
      simp
    rw [hv']
    calc
      _ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hvar i)
      _ = _ := by simp

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol transcript](hyp:z). [First-half binary randomized-response estimate of the baseline](goal). -/
-- @node: twoCellBaselineEstimate
def twoCellBaselineEstimate (n d : ℕ) (eps : ℝ)
    (z : ProtocolTranscript (twoCellProtocol n d eps)) : ℝ :=
  1/2 + ((n / 2 : ℕ) : ℝ)⁻¹ *
    (∑ i : Fin (n / 2), signVal (z (Fin.castLE (Nat.div_le_self n 2) i)).1) /
      (2 * privacyDelta eps)

/-- Assume [sample size at least two](hyp:hn2) and [a privacy budget in the interval from zero to one](hyp:heps). [The actual binary baseline estimate has the roadmap's finite-block MSE](goal). -/
-- @node: twoCellBaselineEstimate_mse
lemma twoCellBaselineEstimate_mse (n d : ℕ) (eps : ℝ)
    (hn2 : 2 ≤ n) (heps : eps ∈ Set.Ioc 0 1)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    (∫ z, (twoCellBaselineEstimate n d eps z - baseline P)^2
      ∂Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))) ≤
        1 / (4 * (n / 2 : ℕ) * (privacyDelta eps)^2) := by
  classical
  let m0 := (n / 2)
  have hm0 : 0 < m0 := by dsimp [m0]; omega
  have hm0r : (0 : ℝ) < m0 := by exact_mod_cast hm0
  have hdelta : 0 < privacyDelta eps := by
    have h := privacyDelta_lower_quarter eps heps
    linarith [heps.1]
  let g : Fin m0 → Fin n := Fin.castLE (Nat.div_le_self n 2)
  let f : (Fin n → FrontierMessage d) → ℝ := fun z => ∑ i, signVal (z (g i)).1
  let L := Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))
  let c : ℝ := (m0 : ℝ)⁻¹ / (2 * privacyDelta eps)
  letI : ∀ i, IsProbabilityMeasure ((observedLaw P).bind (twoCellKernel n d eps i)) :=
    fun i => twoCell_averaged_row_probability n d eps P i
  obtain ⟨hmean, hvar⟩ := twoCell_baseline_sum_moments eps P g
    (by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin n => x.val) h)
    (fun i => i.isLt)
  change (∫ z, f z ∂L) = (m0 : ℝ) * (privacyDelta eps * (2 * baseline P - 1)) at hmean
  change variance f L ≤ (m0 : ℝ) at hvar
  have hrepr : ∀ z : Fin n → FrontierMessage d,
      twoCellBaselineEstimate n d eps z - baseline P = c * (f z - ∫ w, f w ∂L) := by
    intro z
    dsimp only [twoCellBaselineEstimate]
    rw [hmean]
    dsimp [c, f, g]
    change 1/2 + (m0 : ℝ)⁻¹ * (∑ i : Fin m0, signVal (z (Fin.castLE _ i)).1) /
      (2 * privacyDelta eps) - baseline P = _
    field_simp
    <;> ring
  have hv : (∫ z, (twoCellBaselineEstimate n d eps z - baseline P)^2 ∂L) =
      c^2 * variance f L := by
    simp_rw [hrepr, mul_pow]
    rw [integral_const_mul, variance_eq_integral (by fun_prop)]
  change (∫ z, (twoCellBaselineEstimate n d eps z - baseline P)^2 ∂L) ≤ _
  rw [hv]
  calc
    _ ≤ c^2 * m0 := mul_le_mul_of_nonneg_left hvar (sq_nonneg c)
    _ = _ := by
      dsimp [c]
      change ((m0 : ℝ)⁻¹ / (2 * privacyDelta eps))^2 * m0 =
        1 / (4 * m0 * (privacyDelta eps)^2)
      field_simp
      <;> ring

/-- Assume [the stated hi condition](hyp:hi). [A vector-release row has exactly the signed-vector marginal](goal). -/
-- @node: twoCellKernel_vector_marginal
lemma twoCellKernel_vector_marginal (n d : ℕ) (eps : ℝ)
    (i : Fin n) (hi : (n / 2) ≤ i.val) (o : ObsRecord d) :
    (twoCellKernel n d eps i o).map Prod.snd = vectorKernel d eps o := by
  classical
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply measurable_snd hE]
  change atomLaw (twoCellMass n d eps i o) (Prod.snd ⁻¹' E) =
    atomLaw (vectorMass eps o) E
  simp only [twoCellMass, not_lt.mpr hi, ↓reduceIte, atomLaw,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurable_snd hE),
    Measure.dirac_apply' _ hE]
  rw [Fintype.sum_prod_type]
  simp [Set.indicator, Set.mem_preimage]

/-- Assume [the stated hi condition](hyp:hi). [Averaging inputs preserves the vector marginal of every vector-release row](goal). -/
-- @node: twoCell_averaged_vector_marginal
lemma twoCell_averaged_vector_marginal (n d : ℕ) (eps : ℝ)
    (i : Fin n) (hi : (n / 2) ≤ i.val)
    (P : Measure (FullRecord d)) :
    ((observedLaw P).bind (twoCellKernel n d eps i)).map Prod.snd =
      vectorMessageLaw P eps := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply measurable_snd hE]
  unfold vectorMessageLaw
  rw [Measure.bind_apply (measurable_snd hE) (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hE (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro o
  have h := congrArg (fun L => L E) (twoCellKernel_vector_marginal n d eps i hi o)
  rw [Measure.map_apply measurable_snd hE] at h
  exact h

/-- Assume [the stated hg condition](hyp:hg) and [the stated hvec condition](hyp:hvec). [Selecting distinct vector-release rows yields independent vector messages](goal). -/
-- @node: twoCell_vector_selection_law
lemma twoCell_vector_selection_law {n d k : ℕ} (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hvec : ∀ i, (n / 2) ≤ (g i).val) :
    (Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))).map
      (fun z i => (z (g i)).2) = vectorBlockLaw P eps k := by
  have : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  have : ∀ i, IsMarkovKernel (twoCellKernel n d eps i) := by
    intro i
    exact ⟨fun o => (twoCellStage_markov n d eps i).isProbabilityMeasure
      ((o,(0 : Fin 1)), fun _ => (false,fun _ => false))⟩
  have : ∀ i, IsProbabilityMeasure ((observedLaw P).bind (twoCellKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  have hind := (iIndepFun_pi
    (μ := fun i => (observedLaw P).bind (twoCellKernel n d eps i))
    (X := fun (_ : Fin n) (z : FrontierMessage d) => z.2)
    (fun _ => measurable_snd.aemeasurable)).precomp hg
  have hlaw := hind.map_fun_eq_pi_map
    (fun i => (measurable_snd.comp (measurable_pi_apply (g i))).aemeasurable)
  refine hlaw.trans ?_
  unfold vectorBlockLaw
  congr 1
  funext i
  have hmap := (measurePreserving_eval
    (fun i => (observedLaw P).bind (twoCellKernel n d eps i)) (g i)).map_eq
  rw [← Measure.map_map measurable_snd (measurable_pi_apply (g i)), hmap]
  exact twoCell_averaged_vector_marginal n d eps (g i) (hvec i) P

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol transcript](hyp:z). [The remaining vector rows, indexed without unused messages](goal). -/
-- @node: twoCellVectorBlock
def twoCellVectorBlock (n d : ℕ) (eps : ℝ)
    (z : ProtocolTranscript (twoCellProtocol n d eps)) : Fin (n - n / 2) → Fin d → Bool :=
  fun i => (z ⟨n / 2 + i.val, by have := Nat.div_le_self n 2; omega⟩).2

/-- [The remaining people have the calibrated iid vector-block law](goal). -/
-- @node: twoCellVectorBlock_law
lemma twoCellVectorBlock_law (n d : ℕ) (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    (Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))).map
      (twoCellVectorBlock n d eps) = vectorBlockLaw P eps (n - n / 2) := by
  let g : Fin (n - n / 2) → Fin n := fun i =>
    ⟨n / 2 + i.val, by have := Nat.div_le_self n 2; omega⟩
  exact twoCell_vector_selection_law eps P g
    (by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [g] at this; omega)
    (fun i => by dsimp [g]; omega)

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), [the coordinate index](hyp:j), and [the protocol transcript](hyp:z). [Each estimated contrast uses the mean of the last block's scaled coordinate](goal). -/
-- @node: twoCellContrastEstimate
def twoCellContrastEstimate (n d : ℕ) (eps : ℝ) (j : Fin d)
    (z : ProtocolTranscript (twoCellProtocol n d eps)) : ℝ :=
  scaledColumnMean eps j (twoCellVectorBlock n d eps z)

/-- Assume [the stated allowed condition](hyp:hAllowed) and [the causal-model conditions for the data law](hyp:hP). [The two vector coordinates have the exact finite-block MSE order in the roadmap](goal). -/
-- @node: twoCellContrastEstimate_mse
lemma twoCellContrastEstimate_mse (n : ℕ) (eps : ℝ) (hAllowed : Allowed n 2 eps)
    (P : Measure (FullRecord 2)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (j : Fin 2) :
    (∫ z, (twoCellContrastEstimate n 2 eps j z - contrast P j)^2
      ∂Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n 2 eps i))) ≤
        4 / ((n - n / 2 : ℕ) * (privacyDelta eps)^2) := by
  have hm : 0 < n - n / 2 := by have := hAllowed.1; omega
  have hcol : blockMean (m := n - n / 2) P eps
      (fun z => (scaledColumnMean eps j z - contrast P j)^2) ≤
        sigmaSquared 2 (n - n / 2) eps := by
    rw [blockMean_sq_error_eq_variance_add_bias,
      blockMean_scaledColumnMean P hP eps hAllowed.2.2.1 (by norm_num) hm]
    simpa using blockVar_scaledColumnMean_le P hP eps hAllowed.2.2.1 (by norm_num) hm j
  have heq := integral_map (μ := Measure.pi
    (fun i => (observedLaw P).bind (twoCellKernel n 2 eps i)))
    (φ := twoCellVectorBlock n 2 eps)
    (f := fun z => (scaledColumnMean eps j z - contrast P j)^2)
    (by fun_prop) (by fun_prop)
  erw [twoCellVectorBlock_law n 2 eps P] at heq
  change (∫ z, (twoCellContrastEstimate n 2 eps j z - contrast P j)^2 ∂_) ≤ _
  erw [← heq]
  exact hcol.trans (by dsimp [sigmaSquared, noiseScale]; field_simp; norm_num)

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the function f](hyp:f). [Lift any finite transcript statistic to a Borel transcript-only decision](goal). -/
-- @node: twoCellTranscriptEstimator
def twoCellTranscriptEstimator (n d : ℕ) (eps : ℝ)
    (f : ProtocolTranscript (twoCellProtocol n d eps) → ℝ) :
    Estimator (twoCellProtocol n d eps) :=
  ⟨fun w => f w.1, by
    letI : Countable (ProtocolTranscript (twoCellProtocol n d eps)) := by
      change Countable (Fin n → FrontierMessage d)
      infer_instance
    letI : MeasurableSingletonClass (ProtocolTranscript (twoCellProtocol n d eps)) := by
      change MeasurableSingletonClass (Fin n → FrontierMessage d)
      infer_instance
    have hf : Measurable f := measurable_of_countable f
    exact hf.comp measurable_fst⟩

/-- [The lifted decision uses only the finite transcript](goal). -/
-- @node: twoCellTranscriptEstimator_transcriptOnly
lemma twoCellTranscriptEstimator_transcriptOnly (n d : ℕ) (eps : ℝ)
    (f : ProtocolTranscript (twoCellProtocol n d eps) → ℝ) :
    TranscriptOnly (twoCellProtocol n d eps) (twoCellTranscriptEstimator n d eps f) := by
  letI : Countable (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → FrontierMessage d)
    infer_instance
  exact ⟨f, measurable_of_countable f, fun _ => rfl⟩

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the causal-model conditions for the data law](hyp:hP). [Sampling MSEs of finite transcript statistics equal their product-law MSEs](goal). -/
-- @node: twoCellTranscriptEstimator_risk_product
lemma twoCellTranscriptEstimator_risk_product (n d : ℕ) (eps : ℝ)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (f : ProtocolTranscript (twoCellProtocol n d eps) → ℝ) (v : ℝ) :
    squaredRisk (decisionLaw S (twoCellProtocol n d eps) P)
      (twoCellTranscriptEstimator n d eps f) v =
      ENNReal.ofReal (∫ z, (f z - v)^2
        ∂Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))) := by
  let L := Measure.pi (fun i => (observedLaw P).bind (twoCellKernel n d eps i))
  letI : ∀ i, IsProbabilityMeasure ((observedLaw P).bind (twoCellKernel n d eps i)) :=
    fun i => twoCell_averaged_row_probability n d eps P i
  letI : Countable (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (twoCellProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → FrontierMessage d)
    infer_instance
  have hf : Measurable (fun z => ENNReal.ofReal ((f z - v)^2)) :=
    measurable_of_countable _
  have htrans := twoCell_sampling_transcript_product n d eps S hIID hRandom P hP
  rw [ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  rw [← htrans]
  erw [lintegral_map hf measurable_fst]
  rfl

/-- Assume [the stated allowed condition](hyp:hAllowed), [independent and identically distributed participant records](hyp:hIID), and [independent protocol randomness](hyp:hRandom). [The explicit binary/vector half-block construction supplies all three MSEs](goal). -/
-- @node: twoCellComponents_of_sampling
lemma twoCellComponents_of_sampling (n : ℕ) (eps : ℝ) (hAllowed : Allowed n 2 eps)
    (S : SamplingScheme n 2) (hIID : IidPeople S) (hRandom : IndependentRandomness S) :
    TwoCellComponents S eps := by
  refine ⟨twoCellProtocol n 2 eps,
    twoCellProtocol_noninteractive n 2 eps hAllowed.2.2.1.le,
    ?_, twoCellTranscriptEstimator n 2 eps (twoCellBaselineEstimate n 2 eps),
    twoCellTranscriptEstimator n 2 eps (twoCellContrastEstimate n 2 eps 0),
    twoCellTranscriptEstimator n 2 eps (twoCellContrastEstimate n 2 eps 1),
    twoCellTranscriptEstimator_transcriptOnly n 2 eps _,
    twoCellTranscriptEstimator_transcriptOnly n 2 eps _,
    twoCellTranscriptEstimator_transcriptOnly n 2 eps _, ?_⟩
  · intro i
    change Finite (FrontierMessage 2)
    infer_instance
  · intro P hP
    letI := hP.1
    simp only [twoCellTranscriptEstimator_risk_product n 2 eps S hIID hRandom P hP.2]
    exact ⟨ENNReal.ofReal_le_ofReal
      (twoCellBaselineEstimate_mse n 2 eps hAllowed.1 hAllowed.2.2 P),
      ENNReal.ofReal_le_ofReal (twoCellContrastEstimate_mse n eps hAllowed P hP.2 0),
      ENNReal.ofReal_le_ofReal (twoCellContrastEstimate_mse n eps hAllowed P hP.2 1)⟩

end CausalSmith.Stat.LdpOptvalueUniformFrontier
