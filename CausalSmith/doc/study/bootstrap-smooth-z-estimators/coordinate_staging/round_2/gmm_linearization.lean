module

public import Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMM.Expansion

/-!
# Conditional bootstrap linearization for smooth feasible GMM

This module derives the vector bootstrap influence-function expansion for a feasible GMM
estimator with smooth observationwise moments and a general estimated weight.
-/

public section

namespace Causalean.Stat

open ContinuousLinearMap Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators RealInnerProductSpace Topology

noncomputable section

variable {Omega X E F : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
  {mu : Measure Omega} {P : Measure X}

/-- For [a GMM problem](hyp:prob), [smooth moment regularity](hyp:reg), [an iid sample](hyp:S),
[a sample-function parameter estimator](hyp:est), [a sample-function weight estimator](hyp:weightEst),
[data parameter consistency](hyp:hConsistent), [data weight consistency](hyp:hWeight), [a negligible
data first-order-condition residual](hyp:hApproxFOC), [bootstrap parameter consistency](hyp:hBootConsistent),
[bootstrap weight consistency](hyp:hBootWeight), and [a negligible bootstrap first-order-condition
residual](hyp:hBootFOC), [the centered feasible-GMM bootstrap estimator has the GMM
influence-function linearization in outer probability](goal). -/
theorem feasibleGMM_bootstrapLinearization_of_smoothMoment
    [IsProbabilityMeasure mu]
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (weightEst : (n : ℕ) → (Fin n → X) → (F →L[ℝ] F))
    (hConsistent : ∀ epsilon > 0,
      Tendsto (fun n ↦ mu {omega |
        epsilon < ‖est n (S.sampleVector n omega) - prob.θ₀‖}) atTop (nhds 0))
    (hWeight : Tendsto_inProb
      (fun n omega ↦ ‖weightEst n (S.sampleVector n omega) - prob.W‖)
      (fun _ ↦ 0) mu)
    (hApproxFOC : IsLittleOp
      (fun n omega ↦ ‖feasibleGMMFOCResidualFn prob reg
        (est n (S.sampleVector n omega))
        (weightEst n (S.sampleVector n omega)) (S.sampleVector n omega)‖)
      (fun _ ↦ (1 : ℝ)) mu)
    (hBootConsistent : BootstrapEstimatorConsistent S est prob.θ₀)
    (hBootWeight : BootstrapTendstoInProbability S
      (fun n _ xstar ↦ weightEst n xstar) (fun _ _ ↦ prob.W))
    (hBootFOC : BootstrapTendstoInProbability S
      (fun n _ xstar ↦ feasibleGMMFOCResidualFn prob reg
        (est n xstar) (weightEst n xstar) xstar)
      (fun _ _ ↦ 0)) :
    BootstrapTendstoInProbability S
      (zEstimatorBootstrapRemainder est prob.influence)
      (fun _ _ ↦ 0) := by
  classical
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  rcases reg.deriv_lipschitz with ⟨L, hLmeas, hLint, hLnonneg, hLbound⟩
  let eJ := toEuclidean (E := E →L[ℝ] F)
  let eG := toEuclidean (E := F)
  let gJ : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ (E →L[ℝ] F))) :=
    fun x ↦ eJ (reg.deriv prob.θ₀ x)
  let gG : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    fun x ↦ eG (prob.g prob.θ₀ x)
  have hgJ : Measurable gJ := eJ.continuous.measurable.comp reg.deriv_at_target_meas
  have hgJint : Integrable gJ P :=
    eJ.toContinuousLinearMap.integrable_comp reg.deriv_at_target_integrable
  have hgG : Measurable gG := eG.continuous.measurable.comp prob.g_meas
  have hgG2 : Integrable (fun x ↦ ‖gG x‖ ^ 2) P := by
    have hbound : ∀ x, ‖gG x‖ ^ 2 ≤
        ‖eG.toContinuousLinearMap‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by
      intro x
      have hop := eG.toContinuousLinearMap.le_opNorm (prob.g prob.θ₀ x)
      have hleft : 0 ≤ ‖gG x‖ := norm_nonneg _
      have hright : 0 ≤ ‖eG.toContinuousLinearMap‖ * ‖prob.g prob.θ₀ x‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      dsimp [gG] at hleft ⊢
      calc
        ‖eG (prob.g prob.θ₀ x)‖ ^ 2 ≤
            (‖eG.toContinuousLinearMap‖ * ‖prob.g prob.θ₀ x‖) ^ 2 :=
          (sq_le_sq₀ hleft hright).2 hop
        _ = ‖eG.toContinuousLinearMap‖ ^ 2 * ‖prob.g prob.θ₀ x‖ ^ 2 := by ring
    refine (prob.finite_var.const_mul (‖eG.toContinuousLinearMap‖ ^ 2)).mono' ?_ ?_
    · exact hgG.norm.pow_const 2 |>.aestronglyMeasurable
    · filter_upwards with x
      have hx : 0 ≤ ‖gG x‖ ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hbound x
  have hgmem : MemLp (prob.g prob.θ₀) 2 P :=
    (memLp_two_iff_integrable_sq_norm prob.g_meas.aestronglyMeasurable).2 prob.finite_var
  let U : ℕ → Omega → F :=
    IsAsymLinearVec.normalizedSum S (prob.g prob.θ₀) (fun m ↦ Finset.range m)
  have hUmean : ∀ n omega, U n omega =
      Real.sqrt (n : ℝ) • S.sampleMeanVec (prob.g prob.θ₀) n omega := by
    intro n omega
    unfold U IIDSample.sampleMeanVec IsAsymLinearVec.normalizedSum
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      rw [smul_smul]
      congr 1
      simp only [Finset.card_range]
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hnpos.le]
  have hUmeas : ∀ n, AEMeasurable (U n) mu := by
    intro n
    rw [show U n = fun omega ↦ (Real.sqrt (n : ℝ))⁻¹ •
      ∑ i ∈ Finset.range n, prob.g prob.θ₀ (S.Z i omega) by
        funext omega
        simp [U, IsAsymLinearVec.normalizedSum_def]]
    exact ((Finset.measurable_sum _
      (fun i _ ↦ prob.g_meas.comp (S.meas i))).const_smul _).aemeasurable
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit prob.g_meas prob.finite_var) mu hUmeas := by
    simpa only [U] using
      S.clt_normalizedSum_vec prob.g_meas prob.finite_var prob.identification
  have hNormUclt := Tendsto_dist_vec.map_continuous continuous_norm hUmeas hUclt
  have hUbig : IsBigOp (fun n omega ↦ ‖U n omega‖)
      (fun _ ↦ (1 : ℝ)) mu := by
    let _ : IsProbabilityMeasure
        ((gaussianLimit prob.g_meas prob.finite_var).map norm) :=
      Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
    exact Tendsto_dist.tightness
      (fun n ↦ continuous_norm.measurable.comp_aemeasurable (hUmeas n)) hNormUclt
  have hjac (n : ℕ) (omega : Omega) (theta : E) :
      gmmSampleJacobianFn reg theta (S.sampleVector n omega) =
        gmmSampleJacobian reg S theta n omega := by
    unfold gmmSampleJacobianFn gmmSampleJacobian Causalean.Stat.finMean
      IIDSample.sampleVector
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ reg.deriv theta (S.Z i omega)) n]
  have hmom (n : ℕ) (omega : Omega) (theta : E) :
      gmmNormalizedMomentFn prob theta (S.sampleVector n omega) =
        gmmNormalizedMoment S prob.g theta n omega := by
    unfold gmmNormalizedMomentFn gmmNormalizedMoment IIDSample.sampleVector
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ prob.g theta (S.Z i omega)) n]
  have hAL := feasibleGMM_asymLinear_of_smoothMoment_of_sampleFn
    prob reg S est (fun n omega ↦ weightEst n (S.sampleVector n omega))
    hConsistent hWeight (by
      simpa only [feasibleGMMFOCResidualFn, hjac, hmom] using hApproxFOC)
  have hSampling : Tendsto_inProb
      (fun n omega ↦ ‖zEstimatorSamplingRemainder
        S est prob.θ₀ prob.influence n omega‖) (fun _ ↦ 0) mu := by
    apply Tendsto_inProb.of_isLittleOp_one
    simpa [zEstimatorSamplingRemainder, IsAsymLinearVec.normalizedSum] using
      hAL.remainder
  have hJdata : Tendsto_inProb
      (fun n omega ↦
        ‖S.sampleMeanVec (reg.deriv prob.θ₀) n omega - prob.G‖)
      (fun _ ↦ 0) mu := by
    apply Tendsto_inProb.of_isLittleOp_one
    simpa [reg.jacobian_eq] using
      S.sampleMeanVec_norm_sub_isLittleOp reg.deriv_at_target_meas
        reg.deriv_at_target_integrable
  have hLdata := S.sampleMean_tendsto_inProb hLmeas hLint
  have hJbootAE := bootstrapMeanVec_sub_dataMean_tendsto_zero_ae S gJ hgJ hgJint
  have hLbootAE := bootstrapMean_sub_dataMean_tendsto_zero_ae S L hLmeas hLint
  intro epsilon hepsilon delta hdelta
  rw [Metric.tendsto_atTop]
  intro eta heta
  let alpha : ℝ := eta / 12
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  let inner : ℝ := delta / 6
  have hinner : 0 < inner := by dsimp [inner]; linarith
  rcases hUbig alpha halpha with ⟨M0raw, hM0raw⟩
  let M0 : ℝ := max M0raw 1
  have hM0 : 0 < M0 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM0lim : Filter.limsup
      (fun n ↦ mu {omega | M0 < ‖U n omega‖}) atTop ≤ ENNReal.ofReal alpha := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0raw
    intro n
    apply measure_mono
    intro omega homega
    simpa [abs_of_nonneg (norm_nonneg _)] using
      (le_max_left M0raw 1).trans_lt homega
  have halpha2 : ENNReal.ofReal alpha < ENNReal.ofReal (2 * alpha) := by
    rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
  have hUdataENN := Filter.eventually_lt_of_limsup_lt
    (lt_of_le_of_lt hM0lim halpha2)
  have hUdata : ∀ᶠ n : ℕ in atTop,
      mu.real {omega | M0 < ‖U n omega‖} < 2 * alpha := by
    filter_upwards [hUdataENN] with n hn
    rw [Measure.real_def]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hn |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  rcases scaledBootstrapMeanDifferenceVec_outer_tight S gG hgG hgG2
      inner hinner alpha halpha with ⟨M1, hM1, hScoreBoot⟩
  let kG : ℝ := ‖eG.symm.toContinuousLinearMap‖ + 1
  have hkG : 0 < kG := by dsimp [kG]; linarith [norm_nonneg eG.symm.toContinuousLinearMap]
  let K : ℝ := max (M0 + kG * M1) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let kJ : ℝ := ‖eJ.symm.toContinuousLinearMap‖ + 1
  have hkJ : 0 < kJ := by dsimp [kJ]; linarith [norm_nonneg eJ.symm.toContinuousLinearMap]
  let ML : ℝ := |∫ x, L x ∂P| + 2
  have hML : 0 < ML := by dsimp [ML]; linarith [abs_nonneg (∫ x, L x ∂P)]
  let A0 : F →L[ℝ] E := adjoint prob.G ∘L prob.W
  let D0 : ℝ := 3 * (‖prob.W‖ + 1) + ‖prob.G‖
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  let p : ℝ := ‖prob.breadInv‖ + 1
  have hp : 0 < p := by dsimp [p]; linarith [norm_nonneg prob.breadInv]
  let B : ℝ := ‖A0‖
  have hB : 0 ≤ B := norm_nonneg _
  let M : ℝ := 2 * p * (D0 * K + 1 + B * K)
  have hM : 0 < M := by dsimp [M]; positivity
  let H : ℝ := D0 * (K + (‖prob.G‖ + 3) * M) + 1 + 3 * B * M + 1
  have hH : 0 < H := by dsimp [H]; positivity
  let R : ℝ := D0 * (‖prob.G‖ + 3) + 3 * B + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let a : ℝ := min 1 (min (1 / (2 * p * R)) (epsilon / (2 * p * H)))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := min_le_left _ _
  let qJ : ℕ → Omega → ℝ := fun n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | a / kJ < ‖Causalean.Stat.finMean (fun i ↦ gJ (xstar i)) -
        Causalean.Stat.finMean (fun i ↦ gJ (S.sampleVector n omega i))‖}
  let qL : ℕ → Omega → ℝ := fun n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | 1 < |Causalean.Stat.finMean (fun i ↦ L (xstar i)) -
        Causalean.Stat.finMean (fun i ↦ L (S.sampleVector n omega i))|}
  have qJmeas (n : ℕ) : Measurable (qJ n) := by
    let A : Set ((Fin n → X) × (Fin n → X)) := {z |
      a / kJ < ‖Causalean.Stat.finMean (fun i ↦ gJ (z.2 i)) -
        Causalean.Stat.finMean (fun i ↦ gJ (z.1 i))‖}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold Causalean.Stat.finMean
      fun_prop
    have hsamp : Measurable (fun omega ↦ S.sampleVector n omega) := by
      apply measurable_pi_iff.mpr
      intro i
      exact S.meas i
    change Measurable ((fun x : Fin n → X ↦
      (bootstrapResample x).real {xstar | (x, xstar) ∈ A}) ∘
        fun omega ↦ S.sampleVector n omega)
    exact (measurable_bootstrapResample_real_of_measurableSet A hA).comp hsamp
  have qLmeas (n : ℕ) : Measurable (qL n) := by
    let A : Set ((Fin n → X) × (Fin n → X)) := {z |
      1 < |Causalean.Stat.finMean (fun i ↦ L (z.2 i)) -
        Causalean.Stat.finMean (fun i ↦ L (z.1 i))|}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold Causalean.Stat.finMean
      fun_prop
    have hsamp : Measurable (fun omega ↦ S.sampleVector n omega) := by
      apply measurable_pi_iff.mpr
      intro i
      exact S.meas i
    change Measurable ((fun x : Fin n → X ↦
      (bootstrapResample x).real {xstar | (x, xstar) ∈ A}) ∘
        fun omega ↦ S.sampleVector n omega)
    exact (measurable_bootstrapResample_real_of_measurableSet A hA).comp hsamp
  have qJae : ∀ᵐ omega ∂mu, Tendsto (fun n ↦ qJ n omega) atTop (nhds 0) := by
    filter_upwards [hJbootAE] with omega homega
    simpa [qJ] using homega (a / kJ) (div_pos ha hkJ)
  have qLae : ∀ᵐ omega ∂mu, Tendsto (fun n ↦ qL n omega) atTop (nhds 0) := by
    filter_upwards [hLbootAE] with omega homega
    simpa [qL] using homega 1 zero_lt_one
  have hqJ := (measureReal_gt_tendsto_zero_of_ae_tendsto qJmeas qJae inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hqL := (measureReal_gt_tendsto_zero_of_ae_tendsto qLmeas qLae inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hweight := (hBootWeight a ha inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hfoc := (hBootFOC a ha inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hcons := (hBootConsistent (a / ML) (div_pos ha hML) inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hJd := (tendstoInMeasure_iff_measureReal_norm.mp hJdata a ha).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hLd := (tendstoInMeasure_iff_measureReal_norm.mp hLdata 1 zero_lt_one).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hRd := (tendstoInMeasure_iff_measureReal_norm.mp hSampling (epsilon / 2)
      (by positivity)).eventually (Metric.ball_mem_nhds 0 halpha)
  apply eventually_atTop.1
  filter_upwards [hUdata, hScoreBoot, hqJ, hqL, hweight, hfoc, hcons, hJd, hLd, hRd,
      eventually_ne_atTop 0] with n hUn hScore_n hqJn hqLn hweightn hfocn hconsn
        hJdn hLdn hRdn hn
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    at hqJn hqLn hweightn hfocn hconsn hJdn hLdn hRdn ⊢
  have hJdn' : mu.real {x |
      a ≤ ‖S.sampleMeanVec (reg.deriv prob.θ₀) n x - prob.G‖} < alpha := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hJdn
  have hRdn' : mu.real {x | epsilon / 2 ≤
      ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n x‖} < alpha := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hRdn
  let badU : Set Omega := {omega | M0 < ‖U n omega‖}
  let badScore : Set Omega := {omega | inner <
    (bootstrapResample (S.sampleVector n omega)).real {xstar | M1 <
      ‖scaledBootstrapMeanDifference gG n (S.sampleVector n omega) xstar‖}}
  let badJboot : Set Omega := {omega | inner < qJ n omega}
  let badLboot : Set Omega := {omega | inner < qL n omega}
  let badWeight : Set Omega := {omega | inner <
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | a < ‖weightEst n xstar - prob.W‖}}
  let badFOC : Set Omega := {omega | inner <
    (bootstrapResample (S.sampleVector n omega)).real {xstar | a <
      ‖feasibleGMMFOCResidualFn prob reg (est n xstar) (weightEst n xstar) xstar‖}}
  let badCons : Set Omega := {omega | inner <
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | a / ML < ‖est n xstar - prob.θ₀‖}}
  let badJdata : Set Omega := {omega |
    a ≤ ‖S.sampleMeanVec (reg.deriv prob.θ₀) n omega - prob.G‖}
  let badLdata : Set Omega := {omega |
    1 ≤ |S.sampleMean L n omega - ∫ x, L x ∂P|}
  let badRdata : Set Omega := {omega | epsilon / 2 ≤
    ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖}
  have houterSubset :
      {omega | delta < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | epsilon < ‖zEstimatorBootstrapRemainder est prob.influence n
          (S.sampleVector n omega) xstar‖}} ⊆
        badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight ∪ badFOC ∪ badCons ∪
          badJdata ∪ badLdata ∪ badRdata := by
    intro omega homega
    by_contra hgood
    simp only [Set.mem_union, not_or] at hgood
    rcases hgood with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hUgood, hScoreGood⟩, hJbootGood⟩,
      hLbootGood⟩, hWeightGood⟩, hFOCGood⟩, hConsGood⟩, hJdataGood⟩,
      hLdataGood⟩, hRdataGood⟩
    have hUbound : ‖U n omega‖ ≤ M0 :=
      le_of_not_gt (by simpa [badU] using hUgood)
    have hJdataBound :
        ‖S.sampleMeanVec (reg.deriv prob.θ₀) n omega - prob.G‖ < a :=
      lt_of_not_ge (by simpa [badJdata] using hJdataGood)
    have hLdataBound : |S.sampleMean L n omega - ∫ x, L x ∂P| < 1 :=
      lt_of_not_ge (by simpa [badLdata] using hLdataGood)
    have hRdataBound :
        ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖ <
          epsilon / 2 :=
      lt_of_not_ge (by simpa [badRdata] using hRdataGood)
    let data : Fin n → X := S.sampleVector n omega
    let bad : Set (Fin n → X) := {xstar | epsilon <
      ‖zEstimatorBootstrapRemainder est prob.influence n data xstar‖}
    let scoreFail : Set (Fin n → X) := {xstar | M1 <
      ‖scaledBootstrapMeanDifference gG n data xstar‖}
    let jFail : Set (Fin n → X) := {xstar | a / kJ <
      ‖Causalean.Stat.finMean (fun i ↦ gJ (xstar i)) -
        Causalean.Stat.finMean (fun i ↦ gJ (data i))‖}
    let lFail : Set (Fin n → X) := {xstar | 1 <
      |Causalean.Stat.finMean (fun i ↦ L (xstar i)) -
        Causalean.Stat.finMean (fun i ↦ L (data i))|}
    let weightFail : Set (Fin n → X) := {xstar |
      a < ‖weightEst n xstar - prob.W‖}
    let focFail : Set (Fin n → X) := {xstar | a <
      ‖feasibleGMMFOCResidualFn prob reg (est n xstar) (weightEst n xstar) xstar‖}
    let consFail : Set (Fin n → X) := {xstar |
      a / ML < ‖est n xstar - prob.θ₀‖}
    have hbadSubset : bad ⊆
        scoreFail ∪ jFail ∪ lFail ∪ weightFail ∪ focFail ∪ consFail := by
      intro xstar hxstar
      by_contra hxgood
      simp only [Set.mem_union, not_or] at hxgood
      rcases hxgood with ⟨⟨⟨⟨⟨hscorex, hJx⟩, hLx⟩, hWeightx⟩, hFOCx⟩, hConsx⟩
      have hJbridge : Causalean.Stat.finMean
          (fun i ↦ reg.deriv prob.θ₀ (data i)) =
          S.sampleMeanVec (reg.deriv prob.θ₀) n omega := by
        unfold Causalean.Stat.finMean IIDSample.sampleMeanVec data IIDSample.sampleVector
        rw [Fin.sum_univ_eq_sum_range
          (fun i ↦ reg.deriv prob.θ₀ (S.Z i omega)) n]
      have hLbridge : Causalean.Stat.finMean (fun i ↦ L (data i)) =
          S.sampleMean L n omega := by
        unfold Causalean.Stat.finMean IIDSample.sampleMean data IIDSample.sampleVector
        rw [Fin.sum_univ_eq_sum_range (fun i ↦ L (S.Z i omega)) n]
        rfl
      have hGbridge : Causalean.Stat.finMean
          (fun i ↦ prob.g prob.θ₀ (data i)) =
          S.sampleMeanVec (prob.g prob.θ₀) n omega := by
        unfold Causalean.Stat.finMean IIDSample.sampleMeanVec data IIDSample.sampleVector
        rw [Fin.sum_univ_eq_sum_range
          (fun i ↦ prob.g prob.θ₀ (S.Z i omega)) n]
      have hJstar : ‖Causalean.Stat.finMean
          (fun i ↦ reg.deriv prob.θ₀ (xstar i)) - prob.G‖ ≤ 2 * a := by
        have heq : eJ (Causalean.Stat.finMean
            (fun i ↦ reg.deriv prob.θ₀ (xstar i)) -
            Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (data i))) =
            Causalean.Stat.finMean (fun i ↦ gJ (xstar i)) -
            Causalean.Stat.finMean (fun i ↦ gJ (data i)) := by
          simp [gJ, Causalean.Stat.finMean, map_sub, map_sum]
        have horig : ‖Causalean.Stat.finMean
            (fun i ↦ reg.deriv prob.θ₀ (xstar i)) -
            Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (data i))‖ ≤ a := by
          calc
            _ = ‖eJ.symm (eJ (Causalean.Stat.finMean
                (fun i ↦ reg.deriv prob.θ₀ (xstar i)) -
                Causalean.Stat.finMean
                  (fun i ↦ reg.deriv prob.θ₀ (data i))))‖ := by simp
            _ ≤ ‖eJ.symm.toContinuousLinearMap‖ * ‖eJ (Causalean.Stat.finMean
                (fun i ↦ reg.deriv prob.θ₀ (xstar i)) -
                Causalean.Stat.finMean
                  (fun i ↦ reg.deriv prob.θ₀ (data i)))‖ :=
              eJ.symm.toContinuousLinearMap.le_opNorm _
            _ ≤ kJ * (a / kJ) := by
              gcongr
              · dsimp [kJ]; linarith [norm_nonneg eJ.symm.toContinuousLinearMap]
              · rw [heq]; exact le_of_not_gt hJx
            _ = a := by field_simp [hkJ.ne']
        rw [hJbridge] at horig
        calc
          _ ≤ ‖Causalean.Stat.finMean
                (fun i ↦ reg.deriv prob.θ₀ (xstar i)) -
                S.sampleMeanVec (reg.deriv prob.θ₀) n omega‖ +
              ‖S.sampleMeanVec (reg.deriv prob.θ₀) n omega - prob.G‖ := by
            convert norm_add_le
              (Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (xstar i)) -
                S.sampleMeanVec (reg.deriv prob.θ₀) n omega)
              (S.sampleMeanVec (reg.deriv prob.θ₀) n omega - prob.G) using 1 <;> abel
          _ ≤ 2 * a := by linarith
      have hLstar : Causalean.Stat.finMean (fun i ↦ L (xstar i)) ≤ ML := by
        have hdiff := le_trans (le_abs_self
          (Causalean.Stat.finMean (fun i ↦ L (xstar i)) -
            Causalean.Stat.finMean (fun i ↦ L (data i)))) (le_of_not_gt hLx)
        have hdataDev : |Causalean.Stat.finMean (fun i ↦ L (data i)) -
            ∫ x, L x ∂P| ≤ 1 := by rw [hLbridge]; exact hLdataBound.le
        have hdataUpper : Causalean.Stat.finMean (fun i ↦ L (data i)) ≤
            ∫ x, L x ∂P + 1 := by
          have := (le_abs_self (Causalean.Stat.finMean (fun i ↦ L (data i)) -
            ∫ x, L x ∂P)).trans hdataDev
          linarith
        dsimp [ML]
        linarith [le_abs_self (∫ x, L x ∂P)]
      have hLstar_nonneg : 0 ≤ Causalean.Stat.finMean (fun i ↦ L (xstar i)) := by
        unfold Causalean.Stat.finMean
        exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun i _ ↦ hLnonneg (xstar i))
      have hd : ‖est n xstar - prob.θ₀‖ ≤ a / ML := le_of_not_gt hConsx
      let C : ℝ := ‖Causalean.Stat.finMean
          (fun i ↦ reg.deriv prob.θ₀ (xstar i)) - prob.G‖ +
        Causalean.Stat.finMean (fun i ↦ L (xstar i)) *
          ‖est n xstar - prob.θ₀‖
      have hCnonneg : 0 ≤ C := by
        exact add_nonneg (norm_nonneg _) (mul_nonneg hLstar_nonneg (norm_nonneg _))
      have hC : C ≤ 3 * a := by
        have hprod : Causalean.Stat.finMean (fun i ↦ L (xstar i)) *
            ‖est n xstar - prob.θ₀‖ ≤ a := by
          calc
            _ ≤ ML * (a / ML) := mul_le_mul hLstar hd (norm_nonneg _) hML.le
            _ = a := by field_simp [hML.ne']
        dsimp [C]
        linarith
      have hJtheta : ‖gmmSampleJacobianFn reg (est n xstar) xstar - prob.G‖ ≤ C := by
        calc
          _ ≤ ‖Causalean.Stat.finMean
                (fun i ↦ reg.deriv prob.θ₀ (xstar i)) - prob.G‖ +
              ‖gmmSampleJacobianFn reg (est n xstar) xstar -
                Causalean.Stat.finMean
                  (fun i ↦ reg.deriv prob.θ₀ (xstar i))‖ := by
            have ht := norm_add_le
              (Causalean.Stat.finMean
                (fun i ↦ reg.deriv prob.θ₀ (xstar i)) - prob.G)
              (gmmSampleJacobianFn reg (est n xstar) xstar -
                Causalean.Stat.finMean
                  (fun i ↦ reg.deriv prob.θ₀ (xstar i)))
            convert ht using 1 <;> abel
          _ ≤ C := by
            dsimp [C]
            gcongr
            unfold gmmSampleJacobianFn Causalean.Stat.finMean
            rw [← smul_sub, ← Finset.sum_sub_distrib]
            calc
              ‖(n : ℝ)⁻¹ • ∑ i,
                  (reg.deriv (est n xstar) (xstar i) -
                    reg.deriv prob.θ₀ (xstar i))‖ ≤
                  (n : ℝ)⁻¹ * ∑ i, ‖reg.deriv (est n xstar) (xstar i) -
                    reg.deriv prob.θ₀ (xstar i)‖ := by
                rw [norm_smul_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
                exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
                  (inv_nonneg.2 (Nat.cast_nonneg _))
              _ ≤ (n : ℝ)⁻¹ * ∑ i,
                    L (xstar i) * ‖est n xstar - prob.θ₀‖ := by
                gcongr with i
                exact hLbound _ _ _
              _ = Causalean.Stat.finMean (fun i ↦ L (xstar i)) *
                    ‖est n xstar - prob.θ₀‖ := by
                unfold Causalean.Stat.finMean
                rw [← Finset.sum_mul]
                ring
      have hWdiff : ‖weightEst n xstar - prob.W‖ ≤ a := le_of_not_gt hWeightx
      have hWnorm : ‖weightEst n xstar‖ ≤ ‖prob.W‖ + 1 := by
        calc
          _ ≤ ‖weightEst n xstar - prob.W‖ + ‖prob.W‖ := by
            convert norm_add_le (weightEst n xstar - prob.W) prob.W using 1 <;> abel
          _ ≤ ‖prob.W‖ + 1 := by linarith
      have hOperator :
          ‖(adjoint (gmmSampleJacobianFn reg (est n xstar) xstar) ∘L
              weightEst n xstar) - A0‖ ≤ D0 * a := by
        have hidop :
            (adjoint (gmmSampleJacobianFn reg (est n xstar) xstar) ∘L
                weightEst n xstar) - A0 =
              ((adjoint (gmmSampleJacobianFn reg (est n xstar) xstar) -
                adjoint prob.G) ∘L weightEst n xstar) +
              (adjoint prob.G ∘L (weightEst n xstar - prob.W)) := by
          ext y
          simp [A0, map_sub]
        rw [hidop]
        calc
          _ ≤ ‖((adjoint (gmmSampleJacobianFn reg (est n xstar) xstar) -
                adjoint prob.G) ∘L weightEst n xstar)‖ +
              ‖adjoint prob.G ∘L (weightEst n xstar - prob.W)‖ := norm_add_le _ _
          _ ≤ ‖gmmSampleJacobianFn reg (est n xstar) xstar - prob.G‖ *
                ‖weightEst n xstar‖ + ‖prob.G‖ *
                ‖weightEst n xstar - prob.W‖ := by
            apply add_le_add
            · calc
                _ ≤ ‖adjoint (gmmSampleJacobianFn reg (est n xstar) xstar) -
                    adjoint prob.G‖ * ‖weightEst n xstar‖ := opNorm_comp_le _ _
                _ = ‖gmmSampleJacobianFn reg (est n xstar) xstar - prob.G‖ *
                    ‖weightEst n xstar‖ := by
                  rw [← map_sub]
                  congr 1
                  exact ContinuousLinearMap.adjoint.norm_map _
            · simpa using opNorm_comp_le (adjoint prob.G) (weightEst n xstar - prob.W)
          _ ≤ D0 * a := by
            dsimp [D0]
            calc
              _ ≤ (3 * a) * (‖prob.W‖ + 1) + ‖prob.G‖ * a := by
                gcongr
                exact hJtheta.trans hC
              _ = (3 * (‖prob.W‖ + 1) + ‖prob.G‖) * a := by ring
      have hcenterG : ‖scaledBootstrapMeanDifference
          (prob.g prob.θ₀) n data xstar‖ ≤ kG * M1 := by
        have heq : eG (scaledBootstrapMeanDifference
            (prob.g prob.θ₀) n data xstar) =
            scaledBootstrapMeanDifference gG n data xstar := by
          simp [scaledBootstrapMeanDifference, gG, Causalean.Stat.finMean,
            map_sub, map_sum]
        calc
          _ = ‖eG.symm (eG (scaledBootstrapMeanDifference
              (prob.g prob.θ₀) n data xstar))‖ := by simp
          _ ≤ ‖eG.symm.toContinuousLinearMap‖ * ‖eG (scaledBootstrapMeanDifference
              (prob.g prob.θ₀) n data xstar)‖ :=
            eG.symm.toContinuousLinearMap.le_opNorm _
          _ ≤ kG * M1 := by
            rw [heq]
            exact mul_le_mul (by dsimp [kG]; linarith [norm_nonneg eG.symm.toContinuousLinearMap])
              (le_of_not_gt hscorex) (norm_nonneg _) hkG.le
      have hUstar : ‖gmmNormalizedMomentFn prob prob.θ₀ xstar‖ ≤ K := by
        have hdecomp : gmmNormalizedMomentFn prob prob.θ₀ xstar =
            scaledBootstrapMeanDifference (prob.g prob.θ₀) n data xstar +
              U n omega := by
          unfold gmmNormalizedMomentFn scaledBootstrapMeanDifference
          rw [hUmean, ← hGbridge]
          unfold Causalean.Stat.finMean
          simp only [smul_sub]
          have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
          have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
          have hcoef : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
              (Real.sqrt (n : ℝ))⁻¹ := by
            field_simp [hsqrt.ne']
            rw [Real.sq_sqrt hnpos.le]
          rw [smul_smul, hcoef]
          abel
        rw [hdecomp]
        exact (norm_add_le _ _).trans <| (add_le_add hcenterG hUbound).trans <| by
          dsimp [K]
          linarith [le_max_left (M0 + kG * M1) 1]
      have hExpansion := gmmNormalizedMomentFn_expansion_le reg hLnonneg hLbound
        hn xstar (est n xstar)
      have hExpansion' :
          ‖gmmNormalizedMomentFn prob (est n xstar) xstar -
            (gmmNormalizedMomentFn prob prob.θ₀ xstar +
              prob.G (Real.sqrt (n : ℝ) • (est n xstar - prob.θ₀)))‖ ≤
            (3 * a) * ‖Real.sqrt (n : ℝ) • (est n xstar - prob.θ₀)‖ :=
        hExpansion.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
      have hAbsorb : ‖prob.breadInv‖ *
          ((D0 * a) * (‖prob.G‖ + 3 * a) + ‖A0‖ * (3 * a)) ≤ 1 / 2 := by
        have haR : 2 * p * R * a ≤ 1 := by
          have ha' : a ≤ 1 / (2 * p * R) :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          calc
            2 * p * R * a ≤ 2 * p * R * (1 / (2 * p * R)) := by gcongr
            _ = 1 := by field_simp [hp.ne', hR.ne']
        have hcore : D0 * (‖prob.G‖ + 3 * a) + 3 * B ≤ R := by
          dsimp [R, B]
          nlinarith [hD0.le, norm_nonneg prob.G, norm_nonneg A0]
        have hp' : ‖prob.breadInv‖ ≤ p := by dsimp [p]; linarith
        calc
          _ = ‖prob.breadInv‖ * a *
              (D0 * (‖prob.G‖ + 3 * a) + 3 * ‖A0‖) := by ring
          _ ≤ p * a * R := by gcongr
          _ ≤ 1 / 2 := by nlinarith
      have hC3 : 0 ≤ 3 * a := by positivity
      have hD : 0 ≤ D0 * a := mul_nonneg hD0.le ha.le
      have hFOCbound :
          ‖feasibleGMMFOCResidualFn prob reg (est n xstar)
            (weightEst n xstar) xstar‖ ≤ a := le_of_not_gt hFOCx
      have hOperator' :
          ‖(adjoint (gmmSampleJacobianFn reg (est n xstar) xstar) ∘L
              weightEst n xstar) - (adjoint prob.G ∘L prob.W)‖ ≤ D0 * a := by
        simpa only [A0] using hOperator
      have hAbsorb' : ‖prob.breadInv‖ *
          ((D0 * a) * (‖prob.G‖ + 3 * a) +
            ‖adjoint prob.G ∘L prob.W‖ * (3 * a)) ≤ 1 / 2 := by
        simpa only [A0] using hAbsorb
      have hpop := feasibleGMM_populationRemainder_le prob reg hn xstar
        (est n xstar) (weightEst n xstar)
        hC3 hD ha.le hK.le hExpansion' hOperator' hFOCbound hUstar hAbsorb'
      let mA : ℝ := 2 * ‖prob.breadInv‖ *
        ((D0 * a) * K + a + ‖A0‖ * K)
      have hMactual : mA ≤ M := by
        dsimp [mA, M, p, B]
        have hp' : ‖prob.breadInv‖ ≤ ‖prob.breadInv‖ + 1 := by linarith
        have hinside : (D0 * a) * K + a + ‖A0‖ * K ≤
            D0 * K + 1 + ‖A0‖ * K := by
          have hDa : D0 * a ≤ D0 := mul_le_of_le_one_right hD0.le ha1
          have hDaK : (D0 * a) * K ≤ D0 * K :=
            mul_le_mul_of_nonneg_right hDa hK.le
          exact add_le_add (add_le_add hDaK ha1) le_rfl
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp' (by positivity)) hinside
          (by positivity) (by positivity)
      have hpopSmall :
          ‖Real.sqrt (n : ℝ) • (est n xstar - prob.θ₀) -
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (xstar i)‖ ≤
            epsilon / 2 := by
        refine hpop.trans ?_
        have haH : 2 * p * H * a ≤ epsilon := by
          have ha' : a ≤ epsilon / (2 * p * H) :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          calc
            2 * p * H * a ≤ 2 * p * H * (epsilon / (2 * p * H)) := by gcongr
            _ = epsilon := by field_simp [hp.ne', hH.ne']
        have hp' : ‖prob.breadInv‖ ≤ p := by dsimp [p]; linarith
        have hinside :
            D0 * (K + (‖prob.G‖ + 3 * a) * mA) + 1 + ‖A0‖ * 3 * mA ≤ H := by
          have hmA : mA ≤ M := hMactual
          have hmA0 : 0 ≤ mA := by
            dsimp [mA]
            positivity
          have hga : ‖prob.G‖ + 3 * a ≤ ‖prob.G‖ + 3 := by linarith
          have hprod : (‖prob.G‖ + 3 * a) * mA ≤
              (‖prob.G‖ + 3) * M :=
            mul_le_mul hga hmA hmA0 (by positivity)
          have hDterm : D0 * (K + (‖prob.G‖ + 3 * a) * mA) ≤
              D0 * (K + (‖prob.G‖ + 3) * M) :=
            mul_le_mul_of_nonneg_left
              (add_le_add le_rfl hprod) hD0.le
          have hBterm : ‖A0‖ * 3 * mA ≤ 3 * ‖A0‖ * M := by
            calc
              ‖A0‖ * 3 * mA = (3 * ‖A0‖) * mA := by ring
              _ ≤ (3 * ‖A0‖) * M :=
                mul_le_mul_of_nonneg_left hmA (by positivity)
              _ = 3 * ‖A0‖ * M := rfl
          dsimp [H, B]
          calc
            _ ≤ D0 * (K + (‖prob.G‖ + 3) * M) + 1 + 3 * ‖A0‖ * M :=
              add_le_add (add_le_add hDterm le_rfl) hBterm
            _ ≤ D0 * (K + (‖prob.G‖ + 3) * M) + 1 + 3 * ‖A0‖ * M + 1 :=
              le_add_of_nonneg_right zero_le_one
        change ‖prob.breadInv‖ *
          ((D0 * a) * (K + (‖prob.G‖ + 3 * a) * mA) + a +
            ‖A0‖ * (3 * a) * mA) ≤ epsilon / 2
        calc
          _ ≤ p * a * H := by
            calc
              _ = ‖prob.breadInv‖ * a *
                  (D0 * (K + (‖prob.G‖ + 3 * a) * mA) +
                    1 + ‖A0‖ * 3 * mA) := by ring
              _ ≤ p * a * H := by gcongr
          _ ≤ epsilon / 2 := by
            apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
            calc
              p * a * H * 2 = 2 * p * H * a := by ring
              _ ≤ epsilon := haH
      have hremainderEq :
          zEstimatorBootstrapRemainder est prob.influence n data xstar =
            (Real.sqrt (n : ℝ) • (est n xstar - prob.θ₀) -
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (xstar i)) -
              zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega := by
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
        have hcoef : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
            (Real.sqrt (n : ℝ))⁻¹ := by
          field_simp [hsqrt.ne']
          rw [Real.sq_sqrt hnpos.le]
        have hstarInf : Real.sqrt (n : ℝ) •
            Causalean.Stat.finMean (fun i ↦ prob.influence (xstar i)) =
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (xstar i) := by
          unfold Causalean.Stat.finMean
          rw [smul_smul, hcoef]
        have hdataInf : Real.sqrt (n : ℝ) •
            Causalean.Stat.finMean (fun i ↦ prob.influence (data i)) =
              IsAsymLinearVec.normalizedSum S prob.influence
                (fun m ↦ Finset.range m) n omega := by
          unfold Causalean.Stat.finMean data IIDSample.sampleVector
            IsAsymLinearVec.normalizedSum
          rw [Fin.sum_univ_eq_sum_range (fun i ↦ prob.influence (S.Z i omega)) n]
          simp only [Finset.card_range]
          rw [smul_smul, hcoef]
        unfold zEstimatorBootstrapRemainder zEstimatorSamplingRemainder
          scaledBootstrapMeanDifference
        simp only [smul_sub]
        rw [hstarInf, hdataInf]
        dsimp [data]
        abel
      change epsilon < ‖zEstimatorBootstrapRemainder est prob.influence n data xstar‖ at hxstar
      rw [hremainderEq] at hxstar
      have htotal :
          ‖(Real.sqrt (n : ℝ) • (est n xstar - prob.θ₀) -
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (xstar i)) -
              zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖ ≤
            epsilon := by
        calc
          _ ≤ ‖Real.sqrt (n : ℝ) • (est n xstar - prob.θ₀) -
                (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (xstar i)‖ +
              ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖ :=
            norm_sub_le _ _
          _ ≤ epsilon / 2 + epsilon / 2 := add_le_add hpopSmall hRdataBound.le
          _ = epsilon := by ring
      exact (not_lt_of_ge htotal) hxstar
    let _ : IsProbabilityMeasure (bootstrapResample data) :=
      bootstrapResample_isProbabilityMeasure data hn
    have hmeasureBad : (bootstrapResample data).real bad ≤ 6 * inner := by
      calc
        _ ≤ (bootstrapResample data).real
            (scoreFail ∪ jFail ∪ lFail ∪ weightFail ∪ focFail ∪ consFail) :=
          measureReal_mono hbadSubset
        _ ≤ (bootstrapResample data).real scoreFail +
            (bootstrapResample data).real jFail + (bootstrapResample data).real lFail +
            (bootstrapResample data).real weightFail +
            (bootstrapResample data).real focFail +
            (bootstrapResample data).real consFail := by
          have h1 := measureReal_union_le (μ := bootstrapResample data) scoreFail jFail
          have h2 := measureReal_union_le (μ := bootstrapResample data)
            (scoreFail ∪ jFail) lFail
          have h3 := measureReal_union_le (μ := bootstrapResample data)
            (scoreFail ∪ jFail ∪ lFail) weightFail
          have h4 := measureReal_union_le (μ := bootstrapResample data)
            (scoreFail ∪ jFail ∪ lFail ∪ weightFail) focFail
          have h5 := measureReal_union_le (μ := bootstrapResample data)
            (scoreFail ∪ jFail ∪ lFail ∪ weightFail ∪ focFail) consFail
          linarith
        _ ≤ 6 * inner := by
          have hs := le_of_not_gt (by simpa [badScore, scoreFail, data] using hScoreGood)
          have hj := le_of_not_gt (by simpa [badJboot, jFail, qJ, data] using hJbootGood)
          have hl := le_of_not_gt (by simpa [badLboot, lFail, qL, data] using hLbootGood)
          have hw := le_of_not_gt (by simpa [badWeight, weightFail, data] using hWeightGood)
          have hf := le_of_not_gt (by simpa [badFOC, focFail, data] using hFOCGood)
          have hc := le_of_not_gt (by simpa [badCons, consFail, data] using hConsGood)
          linarith
    have hmeasureBad' : (bootstrapResample data).real bad ≤ delta := by
      convert hmeasureBad using 1 <;> dsimp [inner] <;> ring
    have homega' : delta < (bootstrapResample data).real bad := by
      simpa [bad, data] using homega
    exact (not_lt_of_ge hmeasureBad') homega'
  calc
    mu.real {omega | delta < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | epsilon < ‖zEstimatorBootstrapRemainder est prob.influence n
          (S.sampleVector n omega) xstar‖}} ≤
      mu.real (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight ∪ badFOC ∪
        badCons ∪ badJdata ∪ badLdata ∪ badRdata) := measureReal_mono houterSubset
    _ ≤ mu.real badU + mu.real badScore + mu.real badJboot + mu.real badLboot +
        mu.real badWeight + mu.real badFOC + mu.real badCons + mu.real badJdata +
        mu.real badLdata + mu.real badRdata := by
      have h1 := measureReal_union_le (μ := mu) badU badScore
      have h2 := measureReal_union_le (μ := mu) (badU ∪ badScore) badJboot
      have h3 := measureReal_union_le (μ := mu) (badU ∪ badScore ∪ badJboot) badLboot
      have h4 := measureReal_union_le (μ := mu)
        (badU ∪ badScore ∪ badJboot ∪ badLboot) badWeight
      have h5 := measureReal_union_le (μ := mu)
        (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight) badFOC
      have h6 := measureReal_union_le (μ := mu)
        (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight ∪ badFOC) badCons
      have h7 := measureReal_union_le (μ := mu)
        (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight ∪ badFOC ∪ badCons)
        badJdata
      have h8 := measureReal_union_le (μ := mu)
        (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight ∪ badFOC ∪ badCons ∪
          badJdata) badLdata
      have h9 := measureReal_union_le (μ := mu)
        (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badWeight ∪ badFOC ∪ badCons ∪
          badJdata ∪ badLdata) badRdata
      linarith
    _ < eta := by
      have hbU : mu.real badU < 2 * alpha := by simpa [badU] using hUn
      have hbS : mu.real badScore < alpha := by simpa [badScore] using hScore_n
      have hbJ : mu.real badJboot < alpha := by simpa [badJboot] using hqJn
      have hbL : mu.real badLboot < alpha := by simpa [badLboot] using hqLn
      have hbW : mu.real badWeight < alpha := by simpa [badWeight] using hweightn
      have hbF : mu.real badFOC < alpha := by simpa [badFOC] using hfocn
      have hbC : mu.real badCons < alpha := by simpa [badCons] using hconsn
      have hbJd : mu.real badJdata < alpha := by simpa [badJdata] using hJdn'
      have hbLd : mu.real badLdata < alpha := by
        simpa [badLdata, Real.norm_eq_abs] using hLdn
      have hbRd : mu.real badRdata < alpha := by simpa [badRdata] using hRdn'
      have halpha_eq : 12 * alpha = eta := by dsimp [alpha]; ring
      linarith

end

end Causalean.Stat
