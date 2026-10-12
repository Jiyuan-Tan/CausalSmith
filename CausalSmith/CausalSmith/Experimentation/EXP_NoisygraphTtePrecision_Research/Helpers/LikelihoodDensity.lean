module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.GraphBayes
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ResponseProduct

/-!
# Radon–Nikodym density of the full numerical sign laws

Conditional posterior response mixtures have the declared full-record density.
Finite Bayes weights identify their report-mass-weighted laws, including null reports.
The remaining assembly integrates these identities over the design and prior.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hfit), [Evaluating the complete-record polynomial on the reference embedding gives the
posterior average of the conditional recipient products.](goal) -/
-- @node: likelihoodDensity_reference_product
lemma likelihoodDensity_reference_product (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (σ : Bool) (H : Acq (Fin n)) (z : Assign (Fin n))
    (y : Fin m → ℝ) :
    likelihoodPoly n m hfit q r δ σ (referenceRecordOf n m hfit (H,z,y)) =
      ∑ M : Matching m, matchingPosterior n m hfit q r H M *
        ∏ c, matchingResponseFactor n m hfit M z σ δ c (y c) := by
  unfold likelihoodPoly
  apply Finset.sum_congr rfl
  intro M _
  rw [matchingResponseFactor_product]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  simp [referenceRecordOf, (recipientOf_injective n m hfit).eq_iff]

/-- Given [the stated assumptions](hyp:hfit,hqr), [The posterior mixture of conditional response laws is the balanced response
product tilted by the complete-record likelihood, at every fixed report and assignment.](goal) -/
-- @node: likelihoodDensity_posterior_response
lemma likelihoodDensity_posterior_response (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool)
    (H : Acq (Fin n)) (z : Assign (Fin n)) :
    (∑ M : Matching m, ENNReal.ofReal (matchingPosterior n m hfit q r H M) •
      Measure.pi (matchingResponseLaw n m hfit M z σ δ)) =
    (Measure.pi (fun _ : Fin m => volume.withDensity
      (fun y => ENNReal.ofReal (balancedDensity δ y)))).withDensity
        (fun y => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ
          (referenceRecordOf n m hfit (H,z,y)))) := by
  simp_rw [matchingResponseProduct_eq_withDensity]
  ext s hs
  rw [Measure.finsetSum_apply, withDensity_apply _ hs]
  simp_rw [Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]
  simp_rw [likelihoodDensity_reference_product]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun M _ => mul_nonneg
    (matchingPosterior_nonneg n m hfit q r hqr H M)
    (Finset.prod_nonneg (fun c _ =>
      (matchingResponseFactor_mem_Icc n m hfit M z σ δ c _).1)))]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro M _
    simp_rw [ENNReal.ofReal_mul (matchingPosterior_nonneg n m hfit q r hqr H M)]
    rw [lintegral_const_mul]
    fun_prop
  · intro M _
    fun_prop

/-- Given [the stated assumptions](hyp:hfit,hqr), [Weighting the conditional posterior response mixture by the actual report
mass recovers the prior-weighted graph and response law, including null reports.](goal) -/
-- @node: likelihoodDensity_joint_response
lemma likelihoodDensity_joint_response (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool)
    (H : Acq (Fin n)) (z : Assign (Fin n)) :
    plantedGraphLaw n m hfit q r {H} •
      (∑ M : Matching m, ENNReal.ofReal (matchingPosterior n m hfit q r H M) •
        Measure.pi (matchingResponseLaw n m hfit M z σ δ)) =
    ∑ M : Matching m, (ENNReal.ofReal (matchingPriorMass m M) *
      acquisitionLaw (matchingGraphSchedule n m hfit M) q r {H}) •
        Measure.pi (matchingResponseLaw n m hfit M z σ δ) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro M _
  rw [smul_smul, mul_comm, matchingPosterior_graphBayes n m hfit q r hqr H M]

/-- Given [the stated assumptions](hyp:hf,hd,d), [A density that factors through a measurable recording map can be transported
without discarding any coordinate of that record.](goal) -/
-- @node: likelihoodDensity_map_withDensity
lemma likelihoodDensity_map_withDensity {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (f : α → β) (d : β → ℝ≥0∞)
    (hf : Measurable f) (hd : Measurable d) :
    (μ.withDensity (fun x => d (f x))).map f = (μ.map f).withDensity d := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hd hf]

/-- Given [the stated assumptions](hyp:hfit), [The complete-record likelihood is Borel before any integration or restriction
to the reference support.](goal) -/
-- @node: likelihoodDensity_polynomial_measurable
@[fun_prop] lemma likelihoodDensity_polynomial_measurable (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (σ : Bool) : Measurable (likelihoodPoly n m hfit q r δ σ) := by
  unfold likelihoodPoly
  apply Finset.measurable_sum
  intro M _
  apply Measurable.mul
  · exact (Measurable.of_discrete : Measurable
      (fun H => matchingPosterior n m hfit q r H M)).comp measurable_fst
  · apply Finset.measurable_prod
    intro e _
    fun_prop

/-- Given [the stated assumptions](hyp:hfit,hqr), [Embedding the conditional posterior response mixture into the full record
preserves its declared likelihood density, including the zero padding coordinates.](goal) -/
-- @node: likelihoodDensity_posterior_record
lemma likelihoodDensity_posterior_record (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool)
    (H : Acq (Fin n)) (z : Assign (Fin n)) :
    (∑ M : Matching m, ENNReal.ofReal (matchingPosterior n m hfit q r H M) •
      Measure.pi (matchingResponseLaw n m hfit M z σ δ)).map
        (fun y => referenceRecordOf n m hfit (H,z,y)) =
    ((Measure.pi (fun _ : Fin m => volume.withDensity
      (fun y => ENNReal.ofReal (balancedDensity δ y)))).map
        (fun y => referenceRecordOf n m hfit (H,z,y))).withDensity
          (fun o => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ o)) := by
  rw [likelihoodDensity_posterior_response n m hfit q r δ hqr σ H z]
  have hf : Measurable (fun y : Fin m → ℝ => referenceRecordOf n m hfit (H,z,y)) :=
    (referenceRecordOf_measurable n m hfit).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs
      (likelihoodDensity_polynomial_measurable n m hfit q r δ σ).ennreal_ofReal hf]

/-- Given [the stated assumptions](hyp:hfit,hqr), [The actual report mass times the conditional full-record density equals the
finite prior-weighted mixture of all matching-specific response records.](goal) -/
-- @node: likelihoodDensity_joint_record
lemma likelihoodDensity_joint_record (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool)
    (H : Acq (Fin n)) (z : Assign (Fin n)) :
    plantedGraphLaw n m hfit q r {H} •
      (((Measure.pi (fun _ : Fin m => volume.withDensity
        (fun y => ENNReal.ofReal (balancedDensity δ y)))).map
          (fun y => referenceRecordOf n m hfit (H,z,y))).withDensity
            (fun o => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ o))) =
    (∑ M : Matching m, (ENNReal.ofReal (matchingPriorMass m M) *
      acquisitionLaw (matchingGraphSchedule n m hfit M) q r {H}) •
        Measure.pi (matchingResponseLaw n m hfit M z σ δ)).map
          (fun y => referenceRecordOf n m hfit (H,z,y)) := by
  rw [← likelihoodDensity_posterior_record n m hfit q r δ hqr σ H z,
    ← Measure.map_smul, likelihoodDensity_joint_response n m hfit q r δ hqr σ H z]

/-- Given [the stated assumptions](hyp:hf), [A finite observed coordinate can be summed out of a product pushforward using
its actual singleton masses, without changing the output record.](goal) -/
-- @node: likelihoodDensity_finite_prod_map
lemma likelihoodDensity_finite_prod_map {α β γ : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (f : α × β → γ) (hf : Measurable f) :
    (μ.prod ν).map f = ∑ a, μ {a} • ν.map (fun b => f (a,b)) := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs), lintegral_fintype,
    Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.smul_apply, Measure.map_apply (show Measurable (fun b => f (a,b)) from
      hf.comp measurable_prodMk_left) hs]
  exact mul_comm _ _

/-- Given [the stated assumptions](hyp:hfit), [The full reference is the finite sum over all reports and assignments of
its embedded balanced response law, weighted by their actual design masses.](goal) -/
-- @node: likelihoodDensity_reference_finite
lemma likelihoodDensity_reference_finite (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) :
    referenceLaw n m hfit q r δ =
      ∑ H : Acq (Fin n), ∑ z : Assign (Fin n),
        (plantedGraphLaw n m hfit q r {H} *
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli (Fin n) {z}) •
        (Measure.pi (fun _ : Fin m => volume.withDensity
          (fun y => ENNReal.ofReal (balancedDensity δ y)))).map
            (fun y => referenceRecordOf n m hfit (H,z,y)) := by
  let := balancedResponseLaw_probability δ
  let : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  unfold referenceLaw
  rw [likelihoodDensity_finite_prod_map _ _ _ (by fun_prop)]
  apply Finset.sum_congr rfl
  intro H _
  rw [likelihoodDensity_finite_prod_map _ _ _ (by fun_prop), Finset.smul_sum]
  simp only [smul_smul]

/-- Given [the stated assumptions](hyp:f), [Tilting a finite measure sum is the sum of its tilted components.](goal) -/
-- @node: likelihoodDensity_withDensity_finsetSum
lemma likelihoodDensity_withDensity_finsetSum {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (μ : ι → Measure α) (f : α → ℝ≥0∞) :
    (∑ i ∈ s, μ i).withDensity f = ∑ i ∈ s, (μ i).withDensity f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, withDensity_add_measure, ih]

/-- Given [the stated assumptions](hyp:hfit,hqr), [Summing the full-record Bayes identity over the complete graph and assignment
coordinates gives the declared tilted reference as a finite prior-weighted response mixture.](goal) -/
-- @node: likelihoodDensity_reference_tilt_finite
lemma likelihoodDensity_reference_tilt_finite (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool) :
    (referenceLaw n m hfit q r δ).withDensity
      (fun o => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ o)) =
      ∑ H : Acq (Fin n), ∑ z : Assign (Fin n),
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli (Fin n) {z} •
          (∑ M : Matching m, (ENNReal.ofReal (matchingPriorMass m M) *
            acquisitionLaw (matchingGraphSchedule n m hfit M) q r {H}) •
              Measure.pi (matchingResponseLaw n m hfit M z σ δ)).map
                (fun y => referenceRecordOf n m hfit (H,z,y)) := by
  rw [likelihoodDensity_reference_finite]
  simp_rw [likelihoodDensity_withDensity_finsetSum, withDensity_smul_measure]
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.sum_congr rfl
  intro z _
  rw [mul_comm, ← smul_smul, likelihoodDensity_joint_record n m hfit q r δ hqr σ H z]

/-- Given [the stated assumptions](hyp:hf), [Summing out a finite second coordinate retains the complete pushforward record.](goal) -/
-- @node: likelihoodDensity_prod_finite_map
lemma likelihoodDensity_prod_finite_map {α β γ : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (f : β × α → γ) (hf : Measurable f) :
    (ν.prod μ).map f = ∑ a, μ {a} • ν.map (fun b => f (b,a)) := by
  rw [← Measure.prod_swap, Measure.map_map hf measurable_swap]
  exact likelihoodDensity_finite_prod_map μ ν (fun p => f p.swap)
    (hf.comp measurable_swap)

/-- [The normalized finite matching prior has its declared singleton mass.](goal) -/
-- @node: likelihoodDensity_prior_singleton
lemma likelihoodDensity_prior_singleton (m : ℕ) (M : Matching m) :
    matchingPrior m {M} = ENNReal.ofReal (matchingPriorMass m M) := by
  simp [matchingPrior, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply', smul_eq_mul, Pi.single_apply]

/-- Given [the stated assumptions](hyp:hfit,hqr), [Integrating the pre-experiment parameter prior first gives a finite mixture
of matching-specific joint baseline and complete-design records.](goal) -/
-- @node: likelihoodDensity_sign_matching_finite
lemma likelihoodDensity_sign_matching_finite (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool) :
    signLaw n m hfit (noisyDesign q r) σ δ =
      ∑ M : Matching m, matchingPrior m {M} •
        (((Measure.pi (fun _ : Fin m => volume.withDensity
          (fun w => ENNReal.ofReal (baselineDensity w)))).prod
          (Measure.pi (fun _ : Fin m =>
            CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)))).prod
          (noisyDesign q r (matchingGraphSchedule n m hfit M))).map
            (fun p => recordOf (balancedSchedule n m hfit σ δ (M,p.1)) p.2) := by
  letI := balancedParamLaw_probability m
  letI : IsProbabilityMeasure
      (volume.withDensity (fun w => ENNReal.ofReal (baselineDensity w))) :=
by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_integrable_normalized.1
        (Filter.Eventually.of_forall
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg),
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_integrable_normalized.2]
    exact ENNReal.ofReal_one
  letI : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  have hk := balancedRecord_kernel_measurable n m hfit q r δ hqr σ
  ext s hs
  rw [signLaw, Measure.bind_apply hs hk.aemeasurable]
  change (∫⁻ ξ, ((noisyDesign q r (balancedSchedule n m hfit σ δ ξ)).map
    (recordOf (balancedSchedule n m hfit σ δ ξ))) s ∂
      (matchingPrior m).prod _) = _
  have hme := (Measure.measurable_coe hs).comp hk
  simp only [Function.comp_def] at hme
  rw [lintegral_prod _ hme.aemeasurable,
    lintegral_fintype, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro M _
  letI := noisyDesign_probability q r hqr (matchingGraphSchedule n m hfit M)
  rw [Measure.smul_apply, Measure.map_apply
    (balancedRecord_fixedMatching_measurable n m hfit σ δ M) hs,
    Measure.prod_apply ((balancedRecord_fixedMatching_measurable n m hfit σ δ M) hs)]
  rw [mul_comm]
  congr 1
  apply lintegral_congr
  intro p
  rw [Measure.map_apply (recordOf_measurable _) hs]
  rfl

/-- Given [the stated assumptions](hyp:hfit,hqr), [Each matching-specific full record law is the finite mixture of the
conditional response records under the actual assignment and report masses.](goal) -/
-- @node: likelihoodDensity_matching_record_finite
lemma likelihoodDensity_matching_record_finite (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool) (M : Matching m) :
    (((Measure.pi (fun _ : Fin m => volume.withDensity
      (fun w => ENNReal.ofReal (baselineDensity w)))).prod
      (Measure.pi (fun _ : Fin m =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)))).prod
      (noisyDesign q r (matchingGraphSchedule n m hfit M))).map
        (fun p => recordOf (balancedSchedule n m hfit σ δ (M,p.1)) p.2) =
      ∑ z : Assign (Fin n), ∑ H : Acq (Fin n),
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli (Fin n) {z} *
          acquisitionLaw (matchingGraphSchedule n m hfit M) q r {H}) •
        (Measure.pi (matchingResponseLaw n m hfit M z σ δ)).map
          (fun y => referenceRecordOf n m hfit (H,z,y)) := by
  rw [likelihoodDensity_prod_finite_map _ _ _
    (balancedRecord_fixedMatching_measurable n m hfit σ δ M), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro H _
  rw [balancedRecord_fixedDesign_law]
  congr 1
  letI := acquisitionLaw_probability q r hqr (matchingGraphSchedule n m hfit M)
  unfold noisyDesign
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

/-- Given [the stated assumptions](hyp:hfit), [Embedding a finite response mixture commutes with its matching sum.](goal) -/
-- @node: likelihoodDensity_map_response_sum
lemma likelihoodDensity_map_response_sum (n m : ℕ) (hfit : 2*m ≤ n)
    (H : Acq (Fin n)) (z : Assign (Fin n))
    (μ : Matching m → Measure (Fin m → ℝ)) :
    (∑ M, μ M).map (fun y => referenceRecordOf n m hfit (H,z,y)) =
      ∑ M, (μ M).map (fun y => referenceRecordOf n m hfit (H,z,y)) := by
  apply Measure.map_finset_sum'
  fun_prop

/-- Given [the stated assumptions](hyp:hfit,hqr), [Integrating the original prior and full design produces exactly the reference
tilt identified by the conditional Bayes identities.](goal) -/
-- @node: likelihoodDensity_sign_eq_withDensity
lemma likelihoodDensity_sign_eq_withDensity (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool) :
    signLaw n m hfit (noisyDesign q r) σ δ =
      (referenceLaw n m hfit q r δ).withDensity
        (fun o => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ o)) := by
  rw [likelihoodDensity_sign_matching_finite n m hfit q r δ hqr σ,
    likelihoodDensity_reference_tilt_finite n m hfit q r δ hqr σ]
  simp_rw [likelihoodDensity_matching_record_finite n m hfit q r δ hqr σ,
    likelihoodDensity_prior_singleton, Finset.smul_sum, smul_smul,
    likelihoodDensity_map_response_sum, Measure.map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext z
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro M _
  congr 1
  ac_rfl

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hδ,hδu,ha,hH,hi), [The original-record sign law is absolutely continuous with the declared polynomial density.](goal) -/
lemma likelihood_density (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hδ : 0 < δ) (hδu : δ ≤ 1/12)
    (D : Design (Fin n)) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) (σ : Bool) :
    signLaw n m hfit D σ δ ≪ referenceLaw n m hfit q r δ ∧
    (signLaw n m hfit D σ δ).rnDeriv (referenceLaw n m hfit q r δ) =ᵐ[referenceLaw n m hfit q r δ]
      fun o => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ o) := by
  have hqr : ChannelDomain q r := ⟨hr.le, hrq, hq⟩
  letI := referenceLaw_probability n m hfit q r δ hqr
  rw [design_eq_noisyDesign D q r ha hH hi,
    likelihoodDensity_sign_eq_withDensity n m hfit q r δ hqr σ]
  exact ⟨withDensity_absolutelyContinuous _ _,
    Measure.rnDeriv_withDensity _
      (likelihoodDensity_polynomial_measurable n m hfit q r δ σ).ennreal_ofReal⟩

end CausalSmith.Experimentation.NoisygraphTtePrecision
