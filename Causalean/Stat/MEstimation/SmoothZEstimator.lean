/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.VectorWLLN
public import Causalean.Stat.EmpiricalProcess.CrossFitRate
public import Causalean.Stat.Limit.WLLN
public import Causalean.Stat.MEstimation.SmoothTaylor
public import Causalean.Stat.MEstimation.ZEstimatorCLT

/-! # Smooth-score Z-estimators

This module proves asymptotic linearity and normality for smooth-score
Z-estimators without assuming stochastic equicontinuity or a root-sample-size
rate.  A deterministic mean-value bound controls the score remainder, a
Banach-valued iid weak law controls the empirical Jacobian, and a stochastic
absorption argument derives the rate before establishing the influence-function
expansion.

The direct analogue is van der Vaart (1998), Theorem 5.41. Newey and McFadden
(1994), Theorem 3.1 supplies the corresponding smooth extremum-estimator
argument only when the score is the derivative of an objective criterion. The
empirical estimating equation here is allowed to have an `o_p(n⁻¹/²)` residual;
an eventual exact root is a special case.

Use this route for observationwise differentiable scores. Use the Lipschitz
route for van der Vaart (1998), Theorem 5.21, and the high-level
equicontinuity route for nonsmooth scores covered by Newey--McFadden (1994),
Theorem 7.2, or Andrews (1994).
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For [a score](hyp:ψ), [target parameter](hyp:θ₀), and [population
law](hyp:P), the smooth-score Z-estimator regularity package records
[population identification](hyp:identification), [score measurability](hyp:score_meas),
[a finite score second moment](hyp:score_finite_var), [the observationwise score
derivative](hyp:deriv), [its derivative identity](hyp:hasFDeriv),
[measurability and integrability of the derivative at the
target](hyp:deriv_at_target_meas,deriv_at_target_integrable),
[an integrable Lipschitz envelope for derivative changes](hyp:deriv_lipschitz),
and [an inverse for the expected target derivative](hyp:jacobianInv,jacobian_inverse). -/
structure SmoothZEstimatorRegularity
    (ψ : E → X → E) (θ₀ : E) (P : Measure X) where
  identification : ∫ x, ψ θ₀ x ∂P = 0
  score_meas : Measurable (ψ θ₀)
  score_finite_var : Integrable (fun x => ‖ψ θ₀ x‖ ^ 2) P
  deriv : E → X → (E →L[ℝ] E)
  hasFDeriv : ∀ θ x, HasFDerivAt (fun η => ψ η x) (deriv θ x) θ
  deriv_at_target_meas : Measurable (deriv θ₀)
  deriv_at_target_integrable : Integrable (deriv θ₀) P
  /-- The observationwise derivative is Lipschitz in the parameter, with an integrable
  envelope, on some ball around the target. Only a neighbourhood is required: demanding a
  globally integrable envelope would exclude ordinary scores such as the Poisson score. -/
  deriv_lipschitz : ∃ δ : ℝ, 0 < δ ∧ ∃ L : X → ℝ,
    Measurable L ∧ Integrable L P ∧ (∀ x, 0 ≤ L x) ∧
      ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ θ' ∈ Metric.closedBall θ₀ δ, ∀ x,
        ‖deriv θ x - deriv θ' x‖ ≤ L x * ‖θ - θ'‖
  jacobianInv : E →L[ℝ] E
  jacobian_inverse :
    (∫ x, deriv θ₀ x ∂P).comp jacobianInv = ContinuousLinearMap.id ℝ E

namespace SmoothZEstimatorRegularity

/-- For [a score, target, population law, and smooth regularity
package](hyp:ψ,θ₀,P,reg), the [population Jacobian](goal) is the expected
observationwise derivative at the target. -/
def jacobian {ψ : E → X → E} {θ₀ : E} {P : Measure X}
    (reg : SmoothZEstimatorRegularity ψ θ₀ P) : E →L[ℝ] E :=
  ∫ x, reg.deriv θ₀ x ∂P

/-- For [a score, target, population law, and smooth regularity
package](hyp:ψ,θ₀,P,reg), the [influence function](goal) applies the negative
inverse population Jacobian to the target score. -/
def influence {ψ : E → X → E} {θ₀ : E} {P : Measure X}
    (reg : SmoothZEstimatorRegularity ψ θ₀ P) : X → E :=
  fun x => -(reg.jacobianInv (ψ θ₀ x))

/-- For [a score, target, population law, and smooth regularity
package](hyp:ψ,θ₀,P,reg), [its canonical influence function satisfies the
common influence-function regularity interface](goal). -/
theorem influenceFunction {ψ : E → X → E} {θ₀ : E} {P : Measure X}
    (reg : SmoothZEstimatorRegularity ψ θ₀ P) [IsFiniteMeasure P] :
    InfluenceFunction P reg.influence := by
  have hmeas : Measurable reg.influence :=
    reg.jacobianInv.continuous.measurable.comp reg.score_meas |>.neg
  have hbound : ∀ x, ‖reg.influence x‖ ^ 2 ≤
      ‖reg.jacobianInv‖ ^ 2 * ‖ψ θ₀ x‖ ^ 2 := by
    intro x
    have hop := reg.jacobianInv.le_opNorm (ψ θ₀ x)
    have hleft : 0 ≤ ‖reg.jacobianInv (ψ θ₀ x)‖ := norm_nonneg _
    have hright : 0 ≤ ‖reg.jacobianInv‖ * ‖ψ θ₀ x‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    dsimp [influence]
    rw [norm_neg]
    nlinarith
  have hvar : Integrable (fun x => ‖reg.influence x‖ ^ 2) P := by
    refine (reg.score_finite_var.const_mul (‖reg.jacobianInv‖ ^ 2)).mono' ?_ ?_
    · exact hmeas.norm.pow_const 2 |>.aestronglyMeasurable
    · filter_upwards with x
      have hx : 0 ≤ ‖reg.influence x‖ ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hbound x
  have hψint : Integrable (ψ θ₀) P :=
    ((memLp_two_iff_integrable_sq_norm reg.score_meas.aestronglyMeasurable).2
      reg.score_finite_var).integrable (by norm_num)
  have hmean : ∫ x, reg.influence x ∂P = 0 := by
    calc
      ∫ x, reg.influence x ∂P
          = -(∫ x, reg.jacobianInv (ψ θ₀ x) ∂P) := by
              simp only [influence]
              rw [MeasureTheory.integral_neg]
      _ = -(reg.jacobianInv (∫ x, ψ θ₀ x ∂P)) := by
              rw [ContinuousLinearMap.integral_comp_comm reg.jacobianInv hψint]
      _ = 0 := by simp [reg.identification]
  exact ⟨hmeas, hmean, hvar⟩

omit [FiniteDimensional ℝ E] in
/-- For [a score, target, population law, and smooth regularity
package](hyp:ψ,θ₀,P,reg), [its influence function is measurable](goal).

This compatibility projection is retained for callers that have not yet
switched to `SmoothZEstimatorRegularity.influenceFunction`. -/
@[fun_prop]
theorem influence_measurable {ψ : E → X → E} {θ₀ : E} {P : Measure X}
    (reg : SmoothZEstimatorRegularity ψ θ₀ P) :
    Measurable reg.influence :=
  reg.jacobianInv.continuous.measurable.comp reg.score_meas |>.neg

omit [FiniteDimensional ℝ E] in
/-- For [a score, target, population law, and smooth regularity
package](hyp:ψ,θ₀,P,reg), [the squared norm of its influence function is
integrable](goal).

This compatibility projection is retained for callers that have not yet
switched to `SmoothZEstimatorRegularity.influenceFunction`. -/
@[fun_prop]
theorem influence_integrable_sq {ψ : E → X → E} {θ₀ : E} {P : Measure X}
    (reg : SmoothZEstimatorRegularity ψ θ₀ P) :
    Integrable (fun x => ‖reg.influence x‖ ^ 2) P := by
  have hbound : ∀ x, ‖reg.influence x‖ ^ 2 ≤
      ‖reg.jacobianInv‖ ^ 2 * ‖ψ θ₀ x‖ ^ 2 := by
    intro x
    have hop := reg.jacobianInv.le_opNorm (ψ θ₀ x)
    have hleft : 0 ≤ ‖reg.jacobianInv (ψ θ₀ x)‖ := norm_nonneg _
    have hright : 0 ≤ ‖reg.jacobianInv‖ * ‖ψ θ₀ x‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    dsimp [influence]
    rw [norm_neg]
    nlinarith
  refine (reg.score_finite_var.const_mul (‖reg.jacobianInv‖ ^ 2)).mono' ?_ ?_
  · exact reg.influence_measurable.norm.pow_const 2 |>.aestronglyMeasurable
  · filter_upwards with x
    have hx : 0 ≤ ‖reg.influence x‖ ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hbound x

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- For [a score, target, population law, comparison parameter, and smooth regularity
package](hyp:ψ,θ₀,P,θ,reg), suppose [an envelope](hyp:L) [is nonnegative](hyp:hLnonneg) and
[bounds how much the score's derivative can change across a closed ball around the
target](hyp:hLbound), and suppose [the comparison parameter lies in that ball](hyp:hθ). At [an
observation](hyp:x), the [first-order Taylor remainder is bounded by the envelope times the
squared parameter displacement](goal).

The ball hypothesis is what makes the mean-value step available: the whole segment from the
target to the comparison parameter stays inside the region where the Lipschitz bound holds. -/
theorem score_taylor_remainder_le
    {ψ : E → X → E} {θ₀ θ : E} {P : Measure X}
    (reg : SmoothZEstimatorRegularity ψ θ₀ P)
    {L : X → ℝ} {δ : ℝ}
    (hLnonneg : ∀ x, 0 ≤ L x)
    (hLbound : ∀ η ∈ Metric.closedBall θ₀ δ, ∀ η' ∈ Metric.closedBall θ₀ δ, ∀ x,
      ‖reg.deriv η x - reg.deriv η' x‖ ≤ L x * ‖η - η'‖)
    (hθ : θ ∈ Metric.closedBall θ₀ δ)
    (x : X) :
    ‖ψ θ x - ψ θ₀ x - reg.deriv θ₀ x (θ - θ₀)‖ ≤
      L x * ‖θ - θ₀‖ ^ 2 := by
  exact norm_taylor_remainder_le_of_fderiv_lipschitz
    (fun η => ψ η x) (fun η => reg.deriv η x) θ₀ θ
    (hLnonneg x) (fun η hη η' hη' => hLbound η hη η' hη' x)
    (fun η => reg.hasFDeriv η x) hθ

end SmoothZEstimatorRegularity

private theorem isBigOp_one_of_isLittleOp_one
    {A : ℕ → Ω → ℝ}
    (hA : IsLittleOp A (fun _ => (1 : ℝ)) μ) :
    IsBigOp A (fun _ => (1 : ℝ)) μ :=
  Modes.IsLittleOpF.boundedInProbability hA

/-- A self-bounding inequality holding only on events whose probabilities tend to one still
implies boundedness in probability when its additive term is bounded and its coefficient
vanishes in probability.

This is the event-restricted analogue of `IsLittleOp.isBigOp_of_absorption`: the inequality
`Y n ω ≤ B n ω + A n ω * Y n ω` is assumed only for `ω ∈ G n`, where
`μ (G n)ᶜ → 0`. The conclusion is a statement in probability, so the
failure event is absorbed by a third vanishing term in the union bound. This is what lets a
Lipschitz hypothesis valid only near the target drive a rate argument: the estimator lies in
that neighbourhood with probability tending to one, not always. -/
private theorem isBigOp_of_absorption_on_event
    {A B Y : ℕ → Ω → ℝ} {G : ℕ → Set Ω}
    (hA : IsLittleOp A (fun _ => (1 : ℝ)) μ)
    (hB : IsBigOp B (fun _ => (1 : ℝ)) μ)
    (hA_nonneg : ∀ n ω, 0 ≤ A n ω)
    (hB_nonneg : ∀ n ω, 0 ≤ B n ω)
    (hY_nonneg : ∀ n ω, 0 ≤ Y n ω)
    (hG : Tendsto (fun n => μ ((G n)ᶜ)) atTop (𝓝 0))
    (hbound : ∀ n ω, ω ∈ G n → Y n ω ≤ B n ω + A n ω * Y n ω) :
    IsBigOp Y (fun _ => (1 : ℝ)) μ := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  rcases hB (δ / 2) hhalf with ⟨M, hM, hBevent⟩
  refine ⟨2 * M, mul_pos (by norm_num) hM, ?_⟩
  let Aevent : ℕ → Set Ω := fun n => {ω | (1 / 2 : ℝ) ≤ |A n ω|}
  let Bevent : ℕ → Set Ω := fun n => {ω | M ≤ |B n ω|}
  let Cevent : ℕ → Set Ω := fun n => {ω | 2 * M ≤ |Y n ω|}
  have hAt : Tendsto (fun n => μ (Aevent n)) atTop (𝓝 0) := by
    simpa [Aevent] using hA (1 / 2) (by norm_num)
  have hAGt : Tendsto
      (fun n => μ (Aevent n) + μ ((G n)ᶜ)) atTop (𝓝 0) := by
    simpa using hAt.add hG
  have hAGevent := (ENNReal.tendsto_nhds_zero.mp hAGt) (δ / 2) hhalf
  have hsubset : ∀ n, Cevent n ⊆ Bevent n ∪ (Aevent n ∪ (G n)ᶜ) := by
    intro n ω hω
    by_contra hnot
    have hnotB : ¬ M ≤ |B n ω| := fun h => hnot (Or.inl h)
    have hnotA : ¬ (1 / 2 : ℝ) ≤ |A n ω| :=
      fun h => hnot (Or.inr (Or.inl h))
    have hmemG : ω ∈ G n := by
      by_contra hg
      exact hnot (Or.inr (Or.inr hg))
    have hAlt : A n ω < 1 / 2 := by
      rw [← abs_of_nonneg (hA_nonneg n ω)]
      exact lt_of_not_ge hnotA
    have hBlt : B n ω < M := by
      rw [← abs_of_nonneg (hB_nonneg n ω)]
      exact lt_of_not_ge hnotB
    have hYlt : Y n ω < 2 * M := by
      nlinarith [hbound n ω hmemG, hY_nonneg n ω]
    have hYge : 2 * M ≤ Y n ω := by
      simpa [Cevent, abs_of_nonneg (hY_nonneg n ω)] using hω
    exact (not_lt_of_ge hYge) hYlt
  filter_upwards [hBevent, hAGevent] with n hBn hAGn
  have hBn' : μ (Bevent n) ≤ δ / 2 := by
    simpa [Bevent, Real.norm_eq_abs] using hBn
  calc
    μ {ω | (2 * M) * (fun _ => (1 : ℝ)) n ≤ |Y n ω|}
        = μ (Cevent n) := by simp [Cevent]
    _ ≤ μ (Bevent n ∪ (Aevent n ∪ (G n)ᶜ)) := measure_mono (hsubset n)
    _ ≤ μ (Bevent n) + μ (Aevent n ∪ (G n)ᶜ) := measure_union_le _ _
    _ ≤ μ (Bevent n) + (μ (Aevent n) + μ ((G n)ᶜ)) := by
      gcongr
      exact measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hBn' hAGn
    _ = δ := ENNReal.add_halves δ

/-- **Smooth-score Z-estimator asymptotic linearity.** Given [a score, target,
population law, and smooth regularity package](hyp:ψ,θ₀,P,reg), if [an
estimator based on an iid sample](hyp:S,θn) [is consistent](hyp:hConsistent)
and [its normalized estimating-equation residual is `o_p(1)`](hyp:hMoment),
then [the estimator is asymptotically linear with influence function
`-V⁻¹ ψ(θ₀,·)`](goal).

The normalized residual condition is exactly
`Pₙ ψ(θ̂ₙ) = o_p(n⁻¹/²)`.  The proof derives the root-sample-size rate from the
smooth mean-value expansion and nonsingularity of the expected derivative; it
does not assume a rate or stochastic equicontinuity. -/
theorem zEstimator_asymLinear_of_smoothScore
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn θ₀ reg.influence S
      (fun n => Finset.range n) := by
  let : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  rcases reg.deriv_lipschitz with ⟨δL, hδL, L, hLmeas, hLint, hLnonneg, hLbound⟩
  -- The Lipschitz envelope is only valid near `θ₀`; consistency puts the estimator there
  -- with probability tending to one, and every bound below is asserted on that event.
  let G : ℕ → Set Ω := fun n => {ω | θn n ω ∈ Metric.closedBall θ₀ δL}
  have hGc : Tendsto (fun n => μ ((G n)ᶜ)) atTop (𝓝 0) := by
    refine (hConsistent δL hδL).congr fun n => ?_
    congr 1
    ext ω
    simp [G, Metric.mem_closedBall, dist_eq_norm, not_le]
  have hJleft : ∀ x : E, reg.jacobianInv (reg.jacobian x) = x := by
    have hJsurj : Function.Surjective reg.jacobian := fun y =>
      ⟨reg.jacobianInv y, by
        have h := congrArg (fun T : E →L[ℝ] E => T y) reg.jacobian_inverse
        simpa [SmoothZEstimatorRegularity.jacobian] using h⟩
    have hJinj : Function.Injective reg.jacobian :=
      (LinearMap.injective_iff_surjective
        (f := (reg.jacobian : E →ₗ[ℝ] E))).mpr hJsurj
    intro x
    apply hJinj
    have h := congrArg (fun T : E →L[ℝ] E => T (reg.jacobian x))
      reg.jacobian_inverse
    simpa [SmoothZEstimatorRegularity.jacobian] using h
  let U : ℕ → Ω → E :=
    IsAsymLinearVec.normalizedSum S (ψ θ₀) (fun n => Finset.range n)
  have hU_def : ∀ n ω, U n ω =
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) := by
    intro n ω
    simp [U, IsAsymLinearVec.normalizedSum_def]
  let T : ℕ → Ω → E := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ •
      ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)
  let Jn : ℕ → Ω → (E →L[ℝ] E) :=
    S.sampleMeanVec (reg.deriv θ₀)
  let A : ℕ → Ω → ℝ := fun n ω => ‖Jn n ω - reg.jacobian‖
  let Lbar : ℕ → Ω → ℝ := S.sampleMean L
  let d : ℕ → Ω → ℝ := fun n ω => ‖θn n ω - θ₀‖
  let C : ℕ → Ω → ℝ := fun n ω => A n ω + Lbar n ω * d n ω
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) • (θn n ω - θ₀)‖
  let M : ℕ → Ω → ℝ := fun n ω => ‖T n ω‖
  let c : ℝ := ‖reg.jacobianInv‖ + 1
  let Ac : ℕ → Ω → ℝ := fun n ω => c * C n ω
  let B : ℕ → Ω → ℝ := fun n ω => c * (‖U n ω‖ + M n ω)
  have hc : 0 < c := by
    dsimp [c]
    linarith [norm_nonneg reg.jacobianInv]
  have hUmeas : ∀ n, AEMeasurable (U n) μ := by
    intro n
    rw [show U n = fun ω => (Real.sqrt (n : ℝ))⁻¹ •
      ∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) by funext ω; exact hU_def n ω]
    exact ((Finset.measurable_sum _
      (fun i _ => reg.score_meas.comp (S.meas i))).const_smul _).aemeasurable
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit reg.score_meas reg.score_finite_var) μ hUmeas := by
    exact S.clt_normalizedSum_vec reg.score_meas reg.score_finite_var
      reg.identification
  have hNormUclt := Tendsto_dist_vec.map_continuous continuous_norm hUmeas hUclt
  have hUbig : IsBigOp (fun n ω => ‖U n ω‖) (fun _ => (1 : ℝ)) μ := by
    let : IsProbabilityMeasure
        ((gaussianLimit reg.score_meas reg.score_finite_var).map norm) :=
      Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
    exact Tendsto_dist.tightness
      (fun n => continuous_norm.measurable.comp_aemeasurable (hUmeas n))
      ((Tendsto_dist_iff _ _ _ _).2 hNormUclt)
  have hAlo : IsLittleOp A (fun _ => (1 : ℝ)) μ := by
    simpa [A, Jn, SmoothZEstimatorRegularity.jacobian] using
      S.sampleMeanVec_norm_sub_isLittleOp reg.deriv_at_target_meas
        reg.deriv_at_target_integrable
  have hLbig : IsBigOp Lbar (fun _ => (1 : ℝ)) μ := by
    simpa [Lbar] using (S.sampleMean_tendsto_inProb hLmeas hLint).isBigOp_one
  have hdlo : IsLittleOp d (fun _ => (1 : ℝ)) μ := by
    apply (Modes.isLittleOpF_iff_strict
      (fun _ => μ) d atTop (fun _ => (1 : ℝ))
      (Eventually.of_forall fun _ => zero_lt_one)).2
    intro ε hε
    simpa [d, abs_of_nonneg (norm_nonneg _)] using hConsistent ε hε
  have hLdlo : IsLittleOp (fun n ω => Lbar n ω * d n ω)
      (fun _ => (1 : ℝ)) μ :=
    IsBigOp.mul_isLittleOp_one_isLittleOp hLbig hdlo
  have hClo : IsLittleOp C (fun _ => (1 : ℝ)) μ := by
    simpa [C] using hAlo.add_one hLdlo
  have hAclo : IsLittleOp Ac (fun _ => (1 : ℝ)) μ := by
    apply IsLittleOp.of_abs_le_const_mul_one hc hClo
    intro n ω
    simp [Ac, abs_mul, abs_of_pos hc]
  have hMlo : IsLittleOp M (fun _ => (1 : ℝ)) μ := by
    simpa [M, T] using hMoment
  have hMbig : IsBigOp M (fun _ => (1 : ℝ)) μ :=
    isBigOp_one_of_isLittleOp_one hMlo
  have hBbig : IsBigOp B (fun _ => (1 : ℝ)) μ := by
    simpa [B] using IsBigOp.const_mul c
      (IsBigOp.add hUbig hMbig)
  have hA_nonneg : ∀ n ω, 0 ≤ Ac n ω := by
    intro n ω
    exact mul_nonneg hc.le <| add_nonneg (norm_nonneg _)
      (mul_nonneg
        (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun i _ => hLnonneg _))
        (norm_nonneg _))
  have hB_nonneg : ∀ n ω, 0 ≤ B n ω := by
    intro n ω
    exact mul_nonneg hc.le (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hY_nonneg : ∀ n ω, 0 ≤ Y n ω := fun n ω => norm_nonneg _
  have hExpansion : ∀ n ω, ω ∈ G n →
      ‖T n ω - (U n ω + reg.jacobian
        (Real.sqrt (n : ℝ) • (θn n ω - θ₀)))‖ ≤ C n ω * Y n ω := by
    intro n ω hmem
    by_cases hn : n = 0
    · subst n
      rw [hU_def]
      simp [T, C, Y, Jn, A, Lbar, d, IIDSample.sampleMean,
        IIDSample.sampleMeanVec]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      let Δ : E := θn n ω - θ₀
      let R : ℕ → E := fun i =>
        ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω) -
          reg.deriv θ₀ (S.Z i ω) Δ
      have hR : ∀ i ∈ Finset.range n,
          ‖R i‖ ≤ L (S.Z i ω) * ‖Δ‖ ^ 2 := by
        intro i hi
        exact reg.score_taylor_remainder_le hLnonneg hLbound hmem (S.Z i ω)
      have hsum :
          (∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)) =
            (∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω)) +
            (∑ i ∈ Finset.range n, reg.deriv θ₀ (S.Z i ω) Δ) +
            ∑ i ∈ Finset.range n, R i := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [R, Δ]
        abel
      have hcoef : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
          (Real.sqrt (n : ℝ))⁻¹ := by
        field_simp [hsqrt.ne']
        rw [Real.sq_sqrt hnpos.le]
      have hJn : Jn n ω (Real.sqrt (n : ℝ) • Δ) =
          (Real.sqrt (n : ℝ))⁻¹ •
            ∑ i ∈ Finset.range n, reg.deriv θ₀ (S.Z i ω) Δ := by
        simp only [Jn, IIDSample.sampleMeanVec, smul_apply, map_smul]
        rw [smul_smul, hcoef]
        simp
      have heq :
          T n ω - (U n ω + reg.jacobian (Real.sqrt (n : ℝ) • Δ)) =
            (Jn n ω - reg.jacobian) (Real.sqrt (n : ℝ) • Δ) +
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i := by
        dsimp [T]
        rw [hU_def, hsum, smul_add, smul_add, ← hJn]
        simp only [sub_apply]
        abel
      have hrem :
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖ ≤
            Lbar n ω * d n ω * Y n ω := by
        calc
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖
              ≤ (Real.sqrt (n : ℝ))⁻¹ *
                  ∑ i ∈ Finset.range n, ‖R i‖ := by
                rw [norm_smul_of_nonneg (inv_nonneg.2 hsqrt.le)]
                exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
                  (inv_nonneg.2 hsqrt.le)
          _ ≤ (Real.sqrt (n : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n, (L (S.Z i ω) * ‖Δ‖ ^ 2) := by
                gcongr with i hi
                exact hR i hi
          _ = Lbar n ω * d n ω * Y n ω := by
                simp only [Lbar, IIDSample.sampleMean, d, Y, Δ]
                rw [← Finset.sum_mul]
                rw [norm_smul_of_nonneg hsqrt.le]
                field_simp [hsqrt.ne']
                rw [Real.sq_sqrt hnpos.le]
                ring
      rw [show θn n ω - θ₀ = Δ by rfl, heq]
      calc
        ‖(Jn n ω - reg.jacobian) (Real.sqrt (n : ℝ) • Δ) +
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖
            ≤ ‖(Jn n ω - reg.jacobian) (Real.sqrt (n : ℝ) • Δ)‖ +
                ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖ :=
              norm_add_le _ _
        _ ≤ A n ω * Y n ω + Lbar n ω * d n ω * Y n ω := by
              exact add_le_add
                ((Jn n ω - reg.jacobian).le_opNorm _)
                hrem
        _ = C n ω * Y n ω := by ring
  have hRateBound : ∀ n ω, ω ∈ G n → Y n ω ≤ B n ω + Ac n ω * Y n ω := by
    intro n ω hmem
    let v : E := Real.sqrt (n : ℝ) • (θn n ω - θ₀)
    let err : E := T n ω - (U n ω + reg.jacobian v)
    have hvid : v = reg.jacobianInv (T n ω - U n ω - err) := by
      have hinside : T n ω - U n ω - err = reg.jacobian v := by
        dsimp [err]
        abel
      rw [hinside, hJleft]
    calc
      Y n ω = ‖v‖ := rfl
      _ = ‖reg.jacobianInv (T n ω - U n ω - err)‖ := by rw [hvid]
      _ ≤ ‖reg.jacobianInv‖ * ‖T n ω - U n ω - err‖ :=
        reg.jacobianInv.le_opNorm _
      _ ≤ ‖reg.jacobianInv‖ * (M n ω + ‖U n ω‖ + ‖err‖) := by
        gcongr
        exact (norm_sub_le _ _).trans <| add_le_add_left (norm_sub_le _ _) _
      _ ≤ c * (M n ω + ‖U n ω‖ + C n ω * Y n ω) := by
        gcongr
        · dsimp [c]
          linarith [norm_nonneg reg.jacobianInv]
        · exact hExpansion n ω hmem
      _ = B n ω + Ac n ω * Y n ω := by
        simp only [B, Ac]
        ring
  have hYbig : IsBigOp Y (fun _ => (1 : ℝ)) μ :=
    isBigOp_of_absorption_on_event hAclo hBbig hA_nonneg hB_nonneg hY_nonneg
      hGc hRateBound
  refine ⟨reg.influenceFunction.mean_zero,
    reg.influenceFunction.finite_var, ?_⟩
  · have hCYlo : IsLittleOp (fun n ω => C n ω * Y n ω)
        (fun _ => (1 : ℝ)) μ := by
      simpa using IsLittleOp.mul_isBigOp
        (Eventually.of_forall fun _ => zero_lt_one)
        (Eventually.of_forall fun _ => zero_lt_one) hClo hYbig
    have hMCYlo : IsLittleOp (fun n ω => M n ω + C n ω * Y n ω)
        (fun _ => (1 : ℝ)) μ := hMlo.add_one hCYlo
    apply IsLittleOp.of_abs_le_const_mul_one_on_event hc hMCYlo hGc
    intro n ω hmem
    let v : E := Real.sqrt (n : ℝ) • (θn n ω - θ₀)
    let err : E := T n ω - (U n ω + reg.jacobian v)
    have hInfSum :
        IsAsymLinearVec.normalizedSum S reg.influence (fun m => Finset.range m) n ω =
          -reg.jacobianInv (U n ω) := by
      simp [IsAsymLinearVec.normalizedSum, SmoothZEstimatorRegularity.influence,
        hU_def, map_sum]
    have hInfSum' :
        (Real.sqrt (n : ℝ))⁻¹ •
            ∑ i ∈ Finset.range n, reg.influence (S.Z i ω) =
          -reg.jacobianInv (U n ω) := by
      simpa [IsAsymLinearVec.normalizedSum] using hInfSum
    have hid : v + reg.jacobianInv (U n ω) =
        reg.jacobianInv (T n ω - err) := by
      have hinside : T n ω - err = U n ω + reg.jacobian v := by
        dsimp [err]
        abel
      rw [hinside, map_add, hJleft]
      abel
    simp only [Finset.card_range]
    rw [hInfSum']
    change |‖v - -reg.jacobianInv (U n ω)‖| ≤
      c * |M n ω + C n ω * Y n ω|
    rw [sub_neg_eq_add, hid, abs_of_nonneg (norm_nonneg _)]
    have hright : 0 ≤ M n ω + C n ω * Y n ω := by
      exact add_nonneg (norm_nonneg _) <|
        mul_nonneg
          (add_nonneg (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
                (Finset.sum_nonneg fun i _ => hLnonneg _))
              (norm_nonneg _)))
          (norm_nonneg _)
    rw [abs_of_nonneg hright]
    calc
      ‖reg.jacobianInv (T n ω - err)‖
          ≤ ‖reg.jacobianInv‖ * ‖T n ω - err‖ := reg.jacobianInv.le_opNorm _
      _ ≤ ‖reg.jacobianInv‖ * (M n ω + ‖err‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ c * (M n ω + C n ω * Y n ω) := by
        gcongr
        · dsimp [c]
          linarith [norm_nonneg reg.jacobianInv]
        · exact hExpansion n ω hmem

/-- **Smooth-score Z-estimator asymptotic normality.** Given [a score, target,
population law, and smooth regularity package](hyp:ψ,θ₀,P,reg), if [an
iid-sample estimator](hyp:S,θn) [is consistent](hyp:hConsistent), [has an
`o_p(n⁻¹/²)` estimating-equation residual](hyp:hMoment), and [has measurable
rescalings](hyp:hθn_meas), then [its rescaled laws converge to the centered
Gaussian generated by the influence function `-V⁻¹ ψ(θ₀,·)`](goal). -/
theorem zEstimator_tendsto_normal_of_smoothScore
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθn_meas n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit reg.influence_measurable reg.influence_integrable_sq,
        inferInstance⟩) := by
  have hAL := zEstimator_asymLinear_of_smoothScore
    ψ θ₀ P reg S θn hConsistent hMoment
  exact hAL.tendsto_normal_vec_clt reg.influence_measurable
    (gaussianLimit reg.influence_measurable reg.influence_integrable_sq)
    (gaussianLimit_charFun reg.influence_measurable reg.influence_integrable_sq)
    hθn_meas

end

end Causalean.Stat
