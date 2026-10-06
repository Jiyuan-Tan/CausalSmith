/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.SampleFnEstimator
public import Causalean.Stat.EmpiricalProcess.CrossFitRate
public import Causalean.Stat.GMM.AsymptoticNormality
public import Causalean.Stat.Limit.ContinuousMapping
public import Causalean.Stat.Limit.WLLN

/-! # Feasible generalized method of moments

This module defines the sample GMM first-order condition using a sample
Jacobian and estimated weight.  It also defines the empirical moment and the
literal Hansen sample statistic.  The asymptotic theory transfers a negligible
normalized sample first-order-condition residual to the population-score equation and
then applies the Z-estimator expansion; the moment CLT used in that transfer is
the library's iid multivariate CLT.

Use this high-level stochastic-equicontinuity route for nonsmooth moments
(Newey--McFadden 1994, Theorem 7.2; Andrews 1994). Use
`SmoothFeasibleGeneral` when observationwise differentiability supplies the
empirical expansion directly (Newey--McFadden 1994, Theorem 3.2).
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped RealInnerProductSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

/-- Given [an iid sample](hyp:S), [a moment function](hyp:g), [a parameter](hyp:θ), [a
sample size](hyp:n), and [an outcome](hyp:ω), the [sample GMM moment](goal) is the average
of the first `n` moment vectors. -/
noncomputable def gmmSampleMoment (S : IIDSample Ω X μ P) (g : E → X → F)
    (θ : E) (n : ℕ) (ω : Ω) : F :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g θ (S.Z i ω)

/-- Given [a sample Jacobian](hyp:sampleG), [an estimated weight](hyp:sampleW), [an iid
sample](hyp:S), [a moment function](hyp:g), [a parameter](hyp:θ), [a sample size](hyp:n), and
[an outcome](hyp:ω), the [feasible GMM first-order-condition vector](goal) is
`G-hat_n(θ)' W-hat_n` applied to the summed sample moments. -/
noncomputable def feasibleGMMScoreSum
    (sampleG : ℕ → Ω → E → (E →L[ℝ] F))
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (S : IIDSample Ω X μ P) (g : E → X → F)
    (n : ℕ) (ω : Ω) (θ : E) : E :=
  adjoint (sampleG n ω θ)
    (sampleW n ω (∑ i ∈ Finset.range n, g θ (S.Z i ω)))

/-- Given [an iid sample](hyp:S), [a moment function](hyp:g), [an estimator](hyp:θn), and
[estimated weights](hyp:sampleW), [a sample size and outcome](hyp:n,ω), the [sample Hansen J
statistic](goal) is `n` times the weighted squared norm of the sample moment at the estimator. -/
noncomputable def hansenJStatistic
    (S : IIDSample Ω X μ P) (g : E → X → F)
    (θn : ℕ → Ω → E) (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ) * ⟪sampleW n ω (gmmSampleMoment S g (θn n ω) n ω),
    gmmSampleMoment S g (θn n ω) n ω⟫

/-- If [the raw GMM moment process is stochastically equicontinuous](hyp:hMomentEquicont)
and [the moment is locally integrable within a positive radius](hyp:δ,hδ,hInt), then
[the combined GMM score process is stochastically equicontinuous](goal) for
[the problem, sample, and estimator](hyp:prob,S,θn).

This transfers the estimator-indexed conclusion of van der Vaart (1998), Lemma 19.24,
through the fixed continuous linear map `GᵀW`. -/
theorem GMMProblem.stochEquicontAt_score
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (δ : ℝ) (hδ : 0 < δ)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hMomentEquicont : StochEquicontAt prob.g prob.θ₀ P μ S θn) :
    StochEquicontAt prob.score prob.θ₀ P μ S θn := by
  let A : F →L[ℝ] E := adjoint prob.G ∘L prob.W
  intro ε hε
  have hden : 0 < ‖A‖ + 1 := by positivity
  have hεA : 0 < ε / (‖A‖ + 1) := div_pos hε hden
  rcases hMomentEquicont (ε / (‖A‖ + 1)) hεA with ⟨ρ, hρ, hproc⟩
  refine ⟨min ρ δ / 2, by positivity, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hproc
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards with n
  apply measure_mono
  intro ω hω
  refine ⟨?_, ?_⟩
  · exact lt_of_lt_of_le hω.1 (div_le_self (by positivity) (by norm_num)) |>.trans_le
      (min_le_left _ _)
  · let θ := θn n ω
    let R : F :=
      (Real.sqrt (n : ℝ))⁻¹ •
          (∑ i ∈ Finset.range n,
            (prob.g θ (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω)))
        - Real.sqrt (n : ℝ) •
            ∫ z, (prob.g θ z - prob.g prob.θ₀ z) ∂P
    have hθδ : ‖θ - prob.θ₀‖ < δ := by
      exact lt_of_lt_of_le hω.1 (div_le_self (by positivity) (by norm_num)) |>.trans_le
        (min_le_right _ _)
    have hdiff : Integrable (fun z => prob.g θ z - prob.g prob.θ₀ z) P :=
      (hInt θ hθδ).sub (hInt prob.θ₀ (by simpa using hδ))
    have hres :
        (Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n,
                (prob.score θ (S.Z i ω) - prob.score prob.θ₀ (S.Z i ω)))
            - Real.sqrt (n : ℝ) •
                ∫ z, (prob.score θ z - prob.score prob.θ₀ z) ∂P = A R := by
      rw [show (∫ z, (prob.score θ z - prob.score prob.θ₀ z) ∂P) =
          A (∫ z, (prob.g θ z - prob.g prob.θ₀ z) ∂P) by
        rw [← A.integral_comp_comm hdiff]
        simp [A, GMMProblem.score, gmmScore, map_sub]]
      simp [R, A, GMMProblem.score, gmmScore, map_sub, map_sum, map_smul]
    have hbad : ε < ‖A R‖ := by
      rw [← hres]
      simpa [θ] using hω.2
    by_contra hnot
    have hRle : ‖R‖ ≤ ε / (‖A‖ + 1) := le_of_not_gt hnot
    have hAle : ‖A R‖ ≤ ‖A‖ * ‖R‖ := A.le_opNorm R
    have hbound : ‖A R‖ < ε := calc
      ‖A R‖ ≤ ‖A‖ * ‖R‖ := hAle
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) :=
        mul_le_mul_of_nonneg_left hRle (norm_nonneg _)
      _ < ε := by
        rw [div_eq_mul_inv, ← mul_assoc]
        have hratio : ‖A‖ * (‖A‖ + 1)⁻¹ < 1 := by
          rw [mul_inv_lt_iff₀ hden]
          linarith
        nlinarith
    exact (not_lt_of_ge hbad.le) hbound

/-- For [a GMM problem](hyp:prob) with [measurable, locally integrable moments on a positive
neighborhood](hyp:hMeas,δ₀,hδ₀,hInt), an [iid sample, estimator, sample Jacobians, and estimated
weights](hyp:S,θn,sampleG,sampleW), [consistency](hyp:hConsistent), [stochastic equicontinuity of
the raw moment process](hyp:hStochEquicont), [combined-operator convergence](hyp:hCombined), and
[an approximate feasible first-order condition](hyp:hSampleFOC), [the estimator has the GMM
influence-function expansion](goal).

The proof derives the root-sample-size rate jointly with the transfer from the
feasible FOC to the oracle combined score.  It is the high-level
stochastic-equicontinuity argument of Newey--McFadden (1994), Theorem 7.2,
with the empirical-process condition supplied in the sense of Andrews (1994). This is the
high-level route for nonsmooth moments; use `feasibleGMM_asymLinear_of_smoothMoment` for the
Newey--McFadden (1994), Theorem 3.2 smooth-moment route. -/
theorem feasibleGMM_asymLinear
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ₀ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (sampleG : ℕ → Ω → E → (E →L[ℝ] F))
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.g prob.θ₀ P μ S θn)
    (hCombined : Tendsto_inProb (fun n ω =>
      ‖(adjoint (sampleG n ω (θn n ω)) ∘L sampleW n ω) -
        (adjoint prob.G ∘L prob.W)‖) (fun _ => 0) μ)
    (hSampleFOC : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        feasibleGMMScoreSum sampleG sampleW S prob.g n ω (θn n ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S
      (fun n => Finset.range n) := by
  let reg := ZEstimatorRegularity.ofGMMProblem prob hMeas δ₀ hδ₀ hInt
  let U : ℕ → Ω → F :=
    IsAsymLinearVec.normalizedSum S (prob.g prob.θ₀) (fun n => Finset.range n)
  let D : ℕ → Ω → ℝ := fun n ω =>
    ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
      (prob.g (θn n ω) (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω))‖
  let Qm : ℕ → Ω → F := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n,
          (prob.g (θn n ω) (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω))
      - Real.sqrt (n : ℝ) •
          ∫ z, (prob.g (θn n ω) z - prob.g prob.θ₀ z) ∂P
  let R : E → F := fun θ =>
    (∫ z, (prob.g θ z - prob.g prob.θ₀ z) ∂P) - prob.G (θ - prob.θ₀)
  let d : ℕ → Ω → ℝ := fun n ω => ‖θn n ω - prob.θ₀‖
  let C : ℕ → Ω → ℝ := fun n ω =>
    if d n ω = 0 then 0 else ‖R (θn n ω)‖ / d n ω
  let V : ℕ → Ω → F := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, prob.g (θn n ω) (S.Z i ω)
  let An : ℕ → Ω → (F →L[ℝ] E) := fun n ω =>
    adjoint (sampleG n ω (θn n ω)) ∘L sampleW n ω
  let A0 : F →L[ℝ] E := adjoint prob.G ∘L prob.W
  let Q : ℕ → Ω → E := fun n ω => An n ω (V n ω)
  let delta : ℕ → Ω → ℝ := fun n ω => ‖An n ω - A0‖
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)‖
  have hUmeas : ∀ n, AEMeasurable (U n) μ := by
    intro n
    exact ((Finset.measurable_sum _ (fun i _ => prob.g_meas.comp (S.meas i))).const_smul _)
      |>.aemeasurable
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit prob.g_meas prob.finite_var) μ hUmeas := by
    exact S.clt_normalizedSum_vec prob.g_meas prob.finite_var prob.identification
  have hNormUclt := Tendsto_dist_vec.map_continuous continuous_norm hUmeas hUclt
  have hNormUbig : IsBigOp (fun n ω => ‖U n ω‖) (fun _ => (1 : ℝ)) μ := by
    letI : IsProbabilityMeasure
        ((gaussianLimit prob.g_meas prob.finite_var).map norm) :=
      Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
    exact Tendsto_dist.tightness
      (fun n => continuous_norm.measurable.comp_aemeasurable (hUmeas n))
      ((Tendsto_dist_iff _ _ _ _).2 hNormUclt)
  have hQmLittle : IsLittleOp (fun n ω => ‖Qm n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa [Qm] using empiricalScoreDiff_isLittleOp_sqrt prob.g prob.θ₀ P S θn
      hConsistent hStochEquicont
  have hF : R =o[𝓝 prob.θ₀] fun θ => ‖θ - prob.θ₀‖ := by
    simpa [R] using prob.populationMomentDiff_isLittleO δ₀ hδ₀ hInt
  have hClittle : IsLittleOp C (fun _ => (1 : ℝ)) μ := by
    apply (Modes.isLittleOpF_iff_strict
      (fun _ => μ) C atTop (fun _ => (1 : ℝ))
      (Eventually.of_forall fun _ => zero_lt_one)).2
    intro ε hε
    have hnear0 := hF.def hε
    have hnear : ∀ᶠ θ in 𝓝 prob.θ₀, ‖R θ‖ ≤ ε * ‖θ - prob.θ₀‖ := by
      filter_upwards [hnear0] with θ hθ
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (θ - prob.θ₀))] using hθ
    rcases Metric.eventually_nhds_iff.mp hnear with ⟨ρ, hρpos, hρ⟩
    have hρhalf : 0 < ρ / 2 := by linarith
    have hcons := hConsistent (ρ / 2) hρhalf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcons
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with n
    apply measure_mono
    intro ω hω
    have hCgt : ε < C n ω := by
      simpa [abs_of_nonneg (by positivity : 0 ≤ C n ω)] using hω
    by_contra hnot
    have hdle : d n ω ≤ ρ / 2 := le_of_not_gt hnot
    have hdlt : d n ω < ρ := lt_of_le_of_lt hdle (by linarith)
    have hRle : ‖R (θn n ω)‖ ≤ ε * d n ω := by
      exact hρ (by simpa [dist_eq_norm, d] using hdlt)
    by_cases hd0 : d n ω = 0
    · exact (not_lt_of_ge hε.le) (by simpa [C, hd0] using hCgt)
    · have hdpos : 0 < d n ω := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
      have hCle : C n ω ≤ ε := by
        dsimp [C]
        rw [if_neg hd0]
        exact (div_le_iff₀ hdpos).2 hRle
      exact (not_lt_of_ge hCle) hCgt
  have hCnonneg : ∀ n ω, 0 ≤ C n ω := by
    intro n ω
    dsimp [C]
    split_ifs
    · exact le_rfl
    · positivity
  have hRbound : ∀ n ω, ‖R (θn n ω)‖ ≤ C n ω * d n ω := by
    intro n ω
    by_cases hd0 : d n ω = 0
    · have hθ : θn n ω = prob.θ₀ := by
        have : θn n ω - prob.θ₀ = 0 := norm_eq_zero.mp (by simpa [d] using hd0)
        exact sub_eq_zero.mp this
      simp [R, C, d, hθ]
    · dsimp [C]
      rw [if_neg hd0]
      exact le_of_eq ((div_mul_cancel₀ _ hd0).symm)
  have hDbound : ∀ n ω, D n ω ≤
      ‖Qm n ω‖ + (‖prob.G‖ + C n ω) * Y n ω := by
    intro n ω
    have hid :
        (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
            (prob.g (θn n ω) (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω)) =
          Qm n ω + prob.G (Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)) +
            Real.sqrt (n : ℝ) • R (θn n ω) := by
      dsimp [Qm, R]
      simp only [map_smul]
      module
    change ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
      (prob.g (θn n ω) (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω))‖ ≤ _
    rw [hid]
    calc
      ‖Qm n ω + prob.G (Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)) +
          Real.sqrt (n : ℝ) • R (θn n ω)‖
          ≤ ‖Qm n ω‖ + ‖prob.G (Real.sqrt (n : ℝ) •
              (θn n ω - prob.θ₀))‖ + ‖Real.sqrt (n : ℝ) • R (θn n ω)‖ := by
            calc
              _ ≤ ‖Qm n ω + prob.G (Real.sqrt (n : ℝ) •
                    (θn n ω - prob.θ₀))‖ +
                    ‖Real.sqrt (n : ℝ) • R (θn n ω)‖ := norm_add_le _ _
              _ ≤ (‖Qm n ω‖ + ‖prob.G (Real.sqrt (n : ℝ) •
                    (θn n ω - prob.θ₀))‖) +
                    ‖Real.sqrt (n : ℝ) • R (θn n ω)‖ :=
                add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖Qm n ω‖ + ‖prob.G‖ * Y n ω + C n ω * Y n ω := by
        gcongr
        · exact prob.G.le_opNorm _
        · rw [norm_smul_of_nonneg (Real.sqrt_nonneg _)]
          calc
            Real.sqrt (n : ℝ) * ‖R (θn n ω)‖
                ≤ Real.sqrt (n : ℝ) * (C n ω * d n ω) :=
                  mul_le_mul_of_nonneg_left (hRbound n ω) (Real.sqrt_nonneg _)
            _ = C n ω * Y n ω := by
              simp [Y, d, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _)]
              ring
      _ = ‖Qm n ω‖ + (‖prob.G‖ + C n ω) * Y n ω := by ring
  have hVnormBound : ∀ n ω, ‖V n ω‖ ≤ ‖U n ω‖ + D n ω := by
    intro n ω
    have hsplit : V n ω = U n ω +
        (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
          (prob.g (θn n ω) (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω)) := by
      dsimp [U, V, IsAsymLinearVec.normalizedSum]
      simp only [Finset.card_range]
      rw [Finset.sum_sub_distrib, smul_sub]
      abel_nf
    rw [hsplit]
    exact norm_add_le _ _
  have hdeltaLittle : IsLittleOp delta (fun _ => (1 : ℝ)) μ := by
    simpa [delta, An, A0] using hCombined.isLittleOp_one
  have hQlittle : IsLittleOp (fun n ω => ‖Q n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa [Q, An, V, feasibleGMMScoreSum, comp_apply, map_smul] using hSampleFOC
  let Arate : ℕ → Ω → ℝ := fun n ω => delta n ω * (‖prob.G‖ + C n ω)
  let Brate : ℕ → Ω → ℝ := fun n ω =>
    ‖Q n ω‖ + delta n ω * (‖U n ω‖ + ‖Qm n ω‖)
  have hArateLittle : IsLittleOp Arate (fun _ => (1 : ℝ)) μ := by
    have hdeltaG : IsLittleOp (fun n ω => delta n ω * ‖prob.G‖)
        (fun _ => (1 : ℝ)) μ := by
      refine IsLittleOp.of_abs_le_const_mul_one
        (C := ‖prob.G‖ + 1) (by positivity) hdeltaLittle ?_
      intro n ω
      rw [abs_mul, abs_of_nonneg (norm_nonneg prob.G),
        abs_of_nonneg (norm_nonneg (An n ω - A0))]
      nlinarith [norm_nonneg prob.G, norm_nonneg (An n ω - A0)]
    have hdeltaC : IsLittleOp (fun n ω => delta n ω * C n ω)
        (fun _ => (1 : ℝ)) μ := by
      simpa using hdeltaLittle.mul_isBigOp
        (Eventually.of_forall fun _ => zero_lt_one)
        (Eventually.of_forall fun _ => zero_lt_one) hClittle.isBigOp_one
    simpa [Arate, mul_add] using hdeltaG.add_one hdeltaC
  have hdeltaUQLittle : IsLittleOp
      (fun n ω => delta n ω * (‖U n ω‖ + ‖Qm n ω‖))
      (fun _ => (1 : ℝ)) μ := by
    simpa using hdeltaLittle.mul_isBigOp
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one)
      (hNormUbig.add hQmLittle.isBigOp_one)
  have hBrateBig : IsBigOp Brate (fun _ => (1 : ℝ)) μ := by
    simpa [Brate] using hQlittle.isBigOp_one.add
      hdeltaUQLittle.isBigOp_one
  have hArateNonneg : ∀ n ω, 0 ≤ Arate n ω := by
    intro n ω
    exact mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (hCnonneg n ω))
  have hBrateNonneg : ∀ n ω, 0 ≤ Brate n ω := by
    intro n ω
    exact add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hScoreBound : ∀ (n : ℕ) (ω : Ω),
      ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖ ≤
          Brate n ω + Arate n ω * Y n ω := by
    intro n ω
    have hscore : (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) =
        A0 (V n ω) := by
      simp [A0, V, GMMProblem.score, gmmScore, comp_apply, map_sum, map_smul]
    have hdecomp : A0 (V n ω) = Q n ω + (A0 - An n ω) (V n ω) := by
      simp [Q, sub_apply]
    rw [hscore, hdecomp]
    calc
      ‖Q n ω + (A0 - An n ω) (V n ω)‖
          ≤ ‖Q n ω‖ + ‖(A0 - An n ω) (V n ω)‖ := norm_add_le _ _
      _ ≤ ‖Q n ω‖ + delta n ω * ‖V n ω‖ := by
        gcongr
        simpa [delta, norm_sub_rev] using (A0 - An n ω).le_opNorm (V n ω)
      _ ≤ ‖Q n ω‖ + delta n ω * (‖U n ω‖ + D n ω) := by
        gcongr
        exact hVnormBound n ω
      _ ≤ ‖Q n ω‖ + delta n ω *
          (‖U n ω‖ + (‖Qm n ω‖ + (‖prob.G‖ + C n ω) * Y n ω)) := by
        gcongr
        exact hDbound n ω
      _ = Brate n ω + Arate n ω * Y n ω := by
        simp only [Brate, Arate]
        ring
  have hRootRate : IsBigOp
      (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - prob.θ₀‖)
      (fun _ => (1 : ℝ)) μ := by
    exact zEstimator_rootRate_of_scoreBound prob.score prob.θ₀ P reg S θn
      hConsistent (prob.stochEquicontAt_score δ₀ hδ₀ hInt S θn hStochEquicont)
      Arate Brate hArateLittle hBrateBig
      hArateNonneg hBrateNonneg hScoreBound
  have hDbig : IsBigOp D (fun _ => (1 : ℝ)) μ := by
    apply IsBigOp.of_abs_le (Yn := fun n ω =>
      ‖Qm n ω‖ + (‖prob.G‖ + C n ω) * Y n ω)
    · intro n ω
      rw [abs_of_nonneg (norm_nonneg _)]
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _)
        (mul_nonneg (add_nonneg (norm_nonneg _) (hCnonneg n ω)) (norm_nonneg _)))]
      exact hDbound n ω
    · have hfactorY : IsBigOp
          (fun n ω => (‖prob.G‖ + C n ω) * Y n ω)
          (fun _ => (1 : ℝ)) μ := by
        have hYbig : IsBigOp Y (fun _ => (1 : ℝ)) μ := by
          simpa [Y, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)] using hRootRate
        have hGY : IsBigOp (fun n ω => ‖prob.G‖ * Y n ω)
            (fun _ => (1 : ℝ)) μ := IsBigOp.const_mul ‖prob.G‖ hYbig
        have hCY : IsBigOp (fun n ω => C n ω * Y n ω)
            (fun _ => (1 : ℝ)) μ := by
          have hCYlittle : IsLittleOp (fun n ω => C n ω * Y n ω)
              (fun _ => (1 : ℝ)) μ := by
            simpa using hClittle.mul_isBigOp
              (Eventually.of_forall fun _ => zero_lt_one)
              (Eventually.of_forall fun _ => zero_lt_one) hYbig
          exact hCYlittle.isBigOp_one
        simpa [add_mul] using hGY.add hCY
      exact hQmLittle.isBigOp_one.add
        hfactorY
  have hVbig : IsBigOp (fun n ω => ‖V n ω‖) (fun _ => (1 : ℝ)) μ := by
    apply IsBigOp.of_abs_le (Yn := fun n ω => ‖U n ω‖ + D n ω)
    · intro n ω
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg
        (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hVnormBound n ω
    · exact hNormUbig.add hDbig
  have hprodLittle : IsLittleOp (fun n ω => delta n ω * ‖V n ω‖)
      (fun _ => (1 : ℝ)) μ :=
    by simpa using
      hdeltaLittle.mul_isBigOp (Eventually.of_forall fun _ => zero_lt_one)
        (Eventually.of_forall fun _ => zero_lt_one) hVbig
  have hApprox : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ := by
    have hsum := hQlittle.add_one hprodLittle
    refine IsLittleOp.of_abs_le_const_mul_one (C := 1) zero_lt_one hsum ?_
    intro n ω
    simp only [abs_of_nonneg (norm_nonneg _), one_mul]
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hscore : (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) =
        A0 (V n ω) := by
      simp [A0, V, GMMProblem.score, gmmScore, comp_apply, map_sum, map_smul]
    have hdecomp : A0 (V n ω) = Q n ω + (A0 - An n ω) (V n ω) := by
      simp [Q, sub_apply]
    rw [hscore, hdecomp]
    calc
      ‖Q n ω + (A0 - An n ω) (V n ω)‖
          ≤ ‖Q n ω‖ + ‖(A0 - An n ω) (V n ω)‖ := norm_add_le _ _
      _ ≤ ‖Q n ω‖ + delta n ω * ‖V n ω‖ := by
        gcongr
        simpa [delta, norm_sub_rev] using (A0 - An n ω).le_opNorm (V n ω)
  have hAL := zEstimator_asymLinear prob.score prob.θ₀ P reg S θn
    hConsistent (prob.stochEquicontAt_score δ₀ hδ₀ hInt S θn hStochEquicont) hApprox
  have hIF : prob.influence = fun z => -(reg.J₀_inv (prob.score prob.θ₀ z)) := by
    funext z
    rfl
  rwa [← hIF] at hAL

/-- For [a GMM problem](hyp:prob) with
[measurable, locally integrable moments](hyp:hMeas,δ₀,hδ₀,hInt),
an [iid sample, estimator, sample Jacobians, and weights](hyp:S,θn,sampleG,sampleW),
[consistency](hyp:hConsistent), [moment stochastic equicontinuity](hyp:hStochEquicont),
[operator convergence](hyp:hCombined), [an approximate feasible FOC](hyp:hSampleFOC), and
[measurability](hyp:hθnMeas), [the rescaled estimator converges to its GMM Gaussian law](goal).

The root-sample-size rate is derived internally from the approximate FOC and
stochastic equicontinuity. -/
theorem feasibleGMM_tendsto_normal
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ₀ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (sampleG : ℕ → Ω → E → (E →L[ℝ] F))
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.g prob.θ₀ P μ S θn)
    (hCombined : Tendsto_inProb (fun n ω =>
      ‖(adjoint (sampleG n ω (θn n ω)) ∘L sampleW n ω) -
        (adjoint prob.G ∘L prob.W)‖) (fun _ => 0) μ)
    (hSampleFOC : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        feasibleGMMScoreSum sampleG sampleW S prob.g n ω (θn n ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hθnMeas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθnMeas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit prob.influence_measurable prob.influence_integrable_sq,
        inferInstance⟩) := by
  have hAL := feasibleGMM_asymLinear prob hMeas δ₀ hδ₀ hInt S θn sampleG sampleW
    hConsistent hStochEquicont hCombined hSampleFOC
  exact hAL.tendsto_normal_vec_clt prob.influence_measurable
    (gaussianLimit prob.influence_measurable prob.influence_integrable_sq)
    (gaussianLimit_charFun prob.influence_measurable prob.influence_integrable_sq)
    hθnMeas

/-- For [a GMM problem](hyp:prob) with
[measurable, locally integrable moments](hyp:hMeas,δ₀,hδ₀,hInt), an
[iid sample and sample-function estimator](hyp:S,est),
[sample Jacobians and weights](hyp:sampleG,sampleW), and
[consistency and moment equicontinuity](hyp:hConsistent,hStochEquicont),
[operator convergence and an approximate FOC](hyp:hCombined,hSampleFOC),
[the induced estimator has the standard GMM influence-function expansion](goal). -/
theorem feasibleGMM_asymLinear_of_sampleFn
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ₀ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (est : (n : ℕ) → (Fin n → X) → E)
    (sampleG : ℕ → Ω → E → (E →L[ℝ] F))
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0, Tendsto (fun n =>
      μ {ω | ε < ‖est n (S.sampleVector n ω) - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.g prob.θ₀ P μ S
      (fun n ω => est n (S.sampleVector n ω)))
    (hCombined : Tendsto_inProb (fun n ω =>
      ‖(adjoint (sampleG n ω (est n (S.sampleVector n ω))) ∘L sampleW n ω) -
        (adjoint prob.G ∘L prob.W)‖) (fun _ => 0) μ)
    (hSampleFOC : IsLittleOp (fun n ω =>
      ‖(Real.sqrt (n : ℝ))⁻¹ • feasibleGMMScoreSum sampleG sampleW S prob.g n ω
        (est n (S.sampleVector n ω))‖) (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) (fun n ω => est n (S.sampleVector n ω)) prob.θ₀
      prob.influence S (fun n => Finset.range n) :=
  feasibleGMM_asymLinear prob hMeas δ₀ hδ₀ hInt S
    (fun n ω => est n (S.sampleVector n ω)) sampleG sampleW hConsistent
    hStochEquicont hCombined hSampleFOC

/-- For [a GMM problem](hyp:prob) with
[measurable, locally integrable moments](hyp:hMeas,δ₀,hδ₀,hInt), an
[iid sample and sample-function estimator](hyp:S,est),
[sample Jacobians and weights](hyp:sampleG,sampleW),
[consistency and moment equicontinuity](hyp:hConsistent,hStochEquicont),
[operator convergence and an approximate FOC](hyp:hCombined,hSampleFOC), and
[rescaled-estimator measurability](hyp:hEstMeas),
[the induced estimator has its GMM limit law](goal). -/
theorem feasibleGMM_tendsto_normal_of_sampleFn
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (hMeas : ∀ θ, Measurable (prob.g θ))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hInt : ∀ θ : E, ‖θ - prob.θ₀‖ < δ₀ → Integrable (prob.g θ) P)
    (S : IIDSample Ω X μ P) (est : (n : ℕ) → (Fin n → X) → E)
    (sampleG : ℕ → Ω → E → (E →L[ℝ] F))
    (sampleW : ℕ → Ω → (F →L[ℝ] F))
    (hConsistent : ∀ ε > 0, Tendsto (fun n =>
      μ {ω | ε < ‖est n (S.sampleVector n ω) - prob.θ₀‖}) atTop (nhds 0))
    (hStochEquicont : StochEquicontAt prob.g prob.θ₀ P μ S
      (fun n ω => est n (S.sampleVector n ω)))
    (hCombined : Tendsto_inProb (fun n ω =>
      ‖(adjoint (sampleG n ω (est n (S.sampleVector n ω))) ∘L sampleW n ω) -
        (adjoint prob.G ∘L prob.W)‖) (fun _ => 0) μ)
    (hSampleFOC : IsLittleOp (fun n ω =>
      ‖(Real.sqrt (n : ℝ))⁻¹ • feasibleGMMScoreSum sampleG sampleW S prob.g n ω
        (est n (S.sampleVector n ω))‖) (fun _ => (1 : ℝ)) μ)
    (hEstMeas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator
        (fun m ω => est m (S.sampleVector m ω)) prob.θ₀
        (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator
          (fun m ω => est m (S.sampleVector m ω)) prob.θ₀
          (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hEstMeas n)⟩)
      atTop
      (nhds ⟨gaussianLimit prob.influence_measurable prob.influence_integrable_sq,
        inferInstance⟩) :=
  feasibleGMM_tendsto_normal prob hMeas δ₀ hδ₀ hInt S
    (fun n ω => est n (S.sampleVector n ω)) sampleG sampleW hConsistent
    hStochEquicont hCombined hSampleFOC hEstMeas

end Causalean.Stat
