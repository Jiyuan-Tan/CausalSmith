/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.VectorWLLN
public import Causalean.Stat.EmpiricalProcess.CrossFitRate
public import Causalean.Stat.GMM.Setup
public import Causalean.Stat.Limit.WLLN
public import Causalean.Stat.MEstimation.SmoothTaylor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! # Smooth GMM moments

This module packages observationwise smoothness of a vector-valued GMM moment
and develops its empirical mean-value expansion.  The derivative at the truth
obeys a vector weak law, while an integrable Lipschitz envelope makes the
empirical Taylor remainder negligible along a consistent root-sample-size
bounded estimator.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

/-- For [a bundled GMM problem](hyp:prob), the smooth GMM-moment regularity
package records [an observationwise derivative](hyp:deriv), [its
Fréchet-derivative identity](hyp:hasFDeriv), [measurability and integrability
of the derivative at the truth](hyp:deriv_at_target_meas,deriv_at_target_integrable),
[an integrable Lipschitz envelope for derivative changes](hyp:deriv_lipschitz),
and [identification of the expected target derivative with the problem's
population Jacobian](hyp:jacobian_eq). -/
structure SmoothGMomentRegularity (prob : GMMProblem (E := E) (F := F) P) where
  deriv : E → X → (E →L[ℝ] F)
  hasFDeriv : ∀ θ x, HasFDerivAt (fun η => prob.g η x) (deriv θ x) θ
  deriv_at_target_meas : Measurable (deriv prob.θ₀)
  deriv_at_target_integrable : Integrable (deriv prob.θ₀) P
  /-- The observationwise derivative is Lipschitz in the parameter, with an integrable
  envelope, on some ball around the target. Only a neighbourhood is required: demanding a
  globally integrable envelope would exclude ordinary moment functions such as the
  exponential-mean moment. -/
  deriv_lipschitz : ∃ δ : ℝ, 0 < δ ∧ ∃ L : X → ℝ,
    Measurable L ∧ Integrable L P ∧ (∀ x, 0 ≤ L x) ∧
      ∀ θ ∈ Metric.closedBall prob.θ₀ δ, ∀ θ' ∈ Metric.closedBall prob.θ₀ δ, ∀ x,
        ‖deriv θ x - deriv θ' x‖ ≤ L x * ‖θ - θ'‖
  jacobian_eq : ∫ x, deriv prob.θ₀ x ∂P = prob.G

/-- Given [smooth GMM moments](hyp:reg), [an iid sample](hyp:S), [a parameter](hyp:θ),
and [a sample size and outcome](hyp:n,ω), the [empirical moment Jacobian](goal)
is the average observationwise derivative. -/
noncomputable def gmmSampleJacobian
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θ : E) (n : ℕ) (ω : Ω) : E →L[ℝ] F :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, reg.deriv θ (S.Z i ω)

/-- Given [an iid sample](hyp:S), [a moment function](hyp:g), [a parameter](hyp:θ),
and [a sample size and outcome](hyp:n,ω), the [root-sample-size normalized
sample moment](goal) is `n⁻¹ᐟ²` times the sum of the first `n` moments. -/
noncomputable def gmmNormalizedMoment
    (S : IIDSample Ω X μ P) (g : E → X → F)
    (θ : E) (n : ℕ) (ω : Ω) : F :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, g θ (S.Z i ω)

namespace SmoothGMomentRegularity

/-- When [an efficient GMM problem](hyp:prob) is viewed with inverse-covariance weighting,
[its smooth moment regularity](hyp:reg) [is unchanged because the moment function, target, and
population Jacobian are unchanged](goal). -/
noncomputable def ofEfficientProblem
    {prob : EfficientGMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob.toGMMProblem) :
    SmoothGMomentRegularity prob.efficientProblem where
  deriv := reg.deriv
  hasFDeriv := reg.hasFDeriv
  deriv_at_target_meas := reg.deriv_at_target_meas
  deriv_at_target_integrable := reg.deriv_at_target_integrable
  deriv_lipschitz := reg.deriv_lipschitz
  jacobian_eq := reg.jacobian_eq

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- For [smooth GMM moments](hyp:reg), [a comparison parameter in the specified closed
neighborhood](hyp:θ,hθ),
[a nonnegative derivative envelope](hyp:hLnonneg) satisfying [the Lipschitz
derivative bound](hyp:hLbound), and [an observation](hyp:x), [the first-order
moment remainder is bounded by the envelope times the squared parameter
displacement](goal). -/
theorem taylor_remainder_le
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (θ : E)
    {L : X → ℝ} {δ : ℝ} (hLnonneg : ∀ x, 0 ≤ L x)
    (hLbound : ∀ η ∈ Metric.closedBall prob.θ₀ δ,
      ∀ η' ∈ Metric.closedBall prob.θ₀ δ, ∀ x,
      ‖reg.deriv η x - reg.deriv η' x‖ ≤ L x * ‖η - η'‖)
    (hθ : θ ∈ Metric.closedBall prob.θ₀ δ)
    (x : X) :
    ‖prob.g θ x - prob.g prob.θ₀ x - reg.deriv prob.θ₀ x (θ - prob.θ₀)‖ ≤
      L x * ‖θ - prob.θ₀‖ ^ 2 := by
  exact norm_taylor_remainder_le_of_fderiv_lipschitz
    (fun η => prob.g η x) (fun η => reg.deriv η x) prob.θ₀ θ
    (hLnonneg x) (fun η hη η' hη' => hLbound η hη η' hη' x)
    (fun η => reg.hasFDeriv η x) hθ

end SmoothGMomentRegularity

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- **Consistency of the empirical GMM Jacobian at the estimator.** For
[smooth GMM moments](hyp:reg) and [an iid sample and estimator](hyp:S,θn), if
[the estimator is consistent](hyp:hConsistent), then [the empirical average
of the observationwise derivative at the estimator converges in probability,
in operator norm, to the population Jacobian](goal). -/
theorem gmmSampleJacobian_norm_sub_isLittleOp
    [IsProbabilityMeasure μ]
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0)) :
    IsLittleOp (fun n ω => ‖gmmSampleJacobian reg S (θn n ω) n ω - prob.G‖)
      (fun _ => (1 : ℝ)) μ := by
  rcases reg.deriv_lipschitz with ⟨δL, hδL, L, hLmeas, hLint, hLnonneg, hLbound⟩
  -- The envelope is valid only near the target; consistency puts the estimator there with
  -- probability tending to one, and the conclusion is a statement in probability.
  let G : ℕ → Set Ω := fun n => {ω | θn n ω ∈ Metric.closedBall prob.θ₀ δL}
  have hGc : Tendsto (fun n => μ ((G n)ᶜ)) atTop (𝓝 0) := by
    refine (hConsistent δL hδL).congr fun n => ?_
    congr 1
    ext ω
    simp [G, Metric.mem_closedBall, dist_eq_norm, not_le]
  have hθ₀mem : prob.θ₀ ∈ Metric.closedBall prob.θ₀ δL :=
    Metric.mem_closedBall_self hδL.le
  let J0 : ℕ → Ω → (E →L[ℝ] F) := S.sampleMeanVec (reg.deriv prob.θ₀)
  let D : ℕ → Ω → ℝ := fun n ω => ‖θn n ω - prob.θ₀‖
  let Lbar : ℕ → Ω → ℝ := S.sampleMean L
  have hJ0 : IsLittleOp (fun n ω => ‖J0 n ω - prob.G‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa [J0, reg.jacobian_eq] using
      S.sampleMeanVec_norm_sub_isLittleOp reg.deriv_at_target_meas
        reg.deriv_at_target_integrable
  have hDbig : IsLittleOp D (fun _ => (1 : ℝ)) μ := by
    apply (Modes.isLittleOpF_iff_strict
      (fun _ => μ) D atTop (fun _ => (1 : ℝ))
      (Eventually.of_forall fun _ => zero_lt_one)).2
    intro ε hε
    simpa [D, abs_of_nonneg (norm_nonneg _)] using hConsistent ε hε
  have hLbig : IsBigOp Lbar (fun _ => (1 : ℝ)) μ := by
    simpa [Lbar] using (S.sampleMean_tendsto_inProb hLmeas hLint).isBigOp_one
  have hLD : IsLittleOp (fun n ω => Lbar n ω * D n ω)
      (fun _ => (1 : ℝ)) μ :=
    hLbig.mul_isLittleOp_one_isLittleOp hDbig
  have hbound : ∀ n ω, ω ∈ G n →
      ‖gmmSampleJacobian reg S (θn n ω) n ω - prob.G‖ ≤
        ‖J0 n ω - prob.G‖ + Lbar n ω * D n ω := by
    intro n ω hmem
    calc
      ‖gmmSampleJacobian reg S (θn n ω) n ω - prob.G‖
          ≤ ‖J0 n ω - prob.G‖ +
              ‖gmmSampleJacobian reg S (θn n ω) n ω - J0 n ω‖ := by
            have h := norm_add_le (J0 n ω - prob.G)
              (gmmSampleJacobian reg S (θn n ω) n ω - J0 n ω)
            rw [show (J0 n ω - prob.G) +
                (gmmSampleJacobian reg S (θn n ω) n ω - J0 n ω) =
              gmmSampleJacobian reg S (θn n ω) n ω - prob.G by abel] at h
            simpa [add_comm] using h
      _ ≤ ‖J0 n ω - prob.G‖ + Lbar n ω * D n ω := by
        gcongr
        unfold gmmSampleJacobian J0 IIDSample.sampleMeanVec Lbar IIDSample.sampleMean D
        rw [← smul_sub, ← Finset.sum_sub_distrib]
        calc
          ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
              (reg.deriv (θn n ω) (S.Z i ω) - reg.deriv prob.θ₀ (S.Z i ω))‖
              ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                  ‖reg.deriv (θn n ω) (S.Z i ω) -
                    reg.deriv prob.θ₀ (S.Z i ω)‖ := by
                rw [norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
                exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
                  (inv_nonneg.2 (Nat.cast_nonneg _))
          _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
                (L (S.Z i ω) * ‖θn n ω - prob.θ₀‖) := by
              gcongr with i hi
              exact hLbound _ hmem _ hθ₀mem _
          _ = ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, L (S.Z i ω)) *
                ‖θn n ω - prob.θ₀‖ := by
              rw [← Finset.sum_mul]
              ring
  refine IsLittleOp.of_abs_le_const_mul_one_on_event (C := 1) zero_lt_one
    (hJ0.add_one hLD) hGc ?_
  intro n ω hmem
  rw [one_mul, abs_of_nonneg (norm_nonneg _)]
  have hnonneg : 0 ≤ ‖J0 n ω - prob.G‖ + Lbar n ω * D n ω := by
    exact add_nonneg (norm_nonneg _) <|
      mul_nonneg
        (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun i _ => hLnonneg _))
        (norm_nonneg _)
  rw [abs_of_nonneg hnonneg]
  exact hbound n ω hmem

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- **Empirical mean-value control for smooth GMM moments.** For [smooth GMM
moments](hyp:reg) and [an iid sample and estimator](hyp:S,θn), if [the
estimator is consistent](hyp:hConsistent), then [there is a nonnegative
`o_P(1)` coefficient that bounds the normalized sample-moment Taylor remainder
times the norm of the root-sample-size parameter error](goal). -/
theorem exists_gmmNormalizedMoment_expansion_control
    [IsProbabilityMeasure μ]
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0)) :
    ∃ C : ℕ → Ω → ℝ,
      IsLittleOp C (fun _ => (1 : ℝ)) μ ∧
      (∀ n ω, 0 ≤ C n ω) ∧
      ∀ n ω, ‖gmmNormalizedMoment S prob.g (θn n ω) n ω -
        (gmmNormalizedMoment S prob.g prob.θ₀ n ω +
          prob.G (Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)))‖
        ≤ C n ω * ‖Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)‖ := by
  classical
  rcases reg.deriv_lipschitz with ⟨δL, hδL, L, hLmeas, hLint, hLnonneg, hLbound⟩
  -- The envelope is valid only near the target. The expansion below therefore holds on the
  -- event that the estimator is in that ball; off it the coefficient is redefined so the
  -- stated pointwise bound still holds, and it remains `o_p(1)` because the event is rare.
  let G : ℕ → Set Ω := fun n => {ω | θn n ω ∈ Metric.closedBall prob.θ₀ δL}
  have hGc : Tendsto (fun n => μ ((G n)ᶜ)) atTop (𝓝 0) := by
    refine (hConsistent δL hδL).congr fun n => ?_
    congr 1
    ext ω
    simp [G, Metric.mem_closedBall, dist_eq_norm, not_le]
  let J0 : ℕ → Ω → (E →L[ℝ] F) := S.sampleMeanVec (reg.deriv prob.θ₀)
  let A : ℕ → Ω → ℝ := fun n ω => ‖J0 n ω - prob.G‖
  let Lbar : ℕ → Ω → ℝ := S.sampleMean L
  let d : ℕ → Ω → ℝ := fun n ω => ‖θn n ω - prob.θ₀‖
  let C : ℕ → Ω → ℝ := fun n ω => A n ω + Lbar n ω * d n ω
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)‖
  have hAlo : IsLittleOp A (fun _ => (1 : ℝ)) μ := by
    simpa [A, J0, reg.jacobian_eq] using
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
      (fun _ => (1 : ℝ)) μ := hLbig.mul_isLittleOp_one_isLittleOp hdlo
  have hClo : IsLittleOp C (fun _ => (1 : ℝ)) μ := by
    simpa [C] using hAlo.add_one hLdlo
  let Res : ℕ → Ω → ℝ := fun n ω =>
    ‖gmmNormalizedMoment S prob.g (θn n ω) n ω -
      (gmmNormalizedMoment S prob.g prob.θ₀ n ω +
        prob.G (Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)))‖
  have hExpansion : ∀ n ω, ω ∈ G n → Res n ω ≤ C n ω * Y n ω := by
    intro n ω hmem
    simp only [Res]
    by_cases hn : n = 0
    · subst n
      simp [gmmNormalizedMoment, C, Y, J0, A, Lbar, d,
        IIDSample.sampleMean, IIDSample.sampleMeanVec]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      let Δ : E := θn n ω - prob.θ₀
      let R : ℕ → F := fun i =>
        prob.g (θn n ω) (S.Z i ω) - prob.g prob.θ₀ (S.Z i ω) -
          reg.deriv prob.θ₀ (S.Z i ω) Δ
      have hR : ∀ i ∈ Finset.range n,
          ‖R i‖ ≤ L (S.Z i ω) * ‖Δ‖ ^ 2 := by
        intro i hi
        exact reg.taylor_remainder_le (θn n ω) hLnonneg hLbound hmem (S.Z i ω)
      have hsum :
          (∑ i ∈ Finset.range n, prob.g (θn n ω) (S.Z i ω)) =
            (∑ i ∈ Finset.range n, prob.g prob.θ₀ (S.Z i ω)) +
            (∑ i ∈ Finset.range n, reg.deriv prob.θ₀ (S.Z i ω) Δ) +
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
      have hJ0 : J0 n ω (Real.sqrt (n : ℝ) • Δ) =
          (Real.sqrt (n : ℝ))⁻¹ •
            ∑ i ∈ Finset.range n, reg.deriv prob.θ₀ (S.Z i ω) Δ := by
        simp only [J0, IIDSample.sampleMeanVec, smul_apply, map_smul]
        rw [smul_smul, hcoef]
        simp
      have heq :
          gmmNormalizedMoment S prob.g (θn n ω) n ω -
              (gmmNormalizedMoment S prob.g prob.θ₀ n ω +
                prob.G (Real.sqrt (n : ℝ) • Δ)) =
            (J0 n ω - prob.G) (Real.sqrt (n : ℝ) • Δ) +
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i := by
        unfold gmmNormalizedMoment
        rw [hsum, smul_add, smul_add, ← hJ0]
        simp only [sub_apply]
        abel
      have hrem :
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖ ≤
            Lbar n ω * d n ω * Y n ω := by
        calc
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖
              ≤ (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ‖R i‖ := by
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
      rw [show θn n ω - prob.θ₀ = Δ by rfl, heq]
      calc
        ‖(J0 n ω - prob.G) (Real.sqrt (n : ℝ) • Δ) +
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖
            ≤ ‖(J0 n ω - prob.G) (Real.sqrt (n : ℝ) • Δ)‖ +
                ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, R i‖ :=
              norm_add_le _ _
        _ ≤ A n ω * Y n ω + Lbar n ω * d n ω * Y n ω := by
              exact add_le_add ((J0 n ω - prob.G).le_opNorm _) hrem
        _ = C n ω * Y n ω := by ring
  -- Extend the coefficient off the good event so that the stated bound is pointwise.
  let C' : ℕ → Ω → ℝ := fun n ω => if ω ∈ G n then C n ω else Res n ω / Y n ω
  have hCnonneg : ∀ n ω, 0 ≤ C n ω := by
    intro n ω
    exact add_nonneg (norm_nonneg _) <|
      mul_nonneg
        (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun i _ => hLnonneg _))
        (norm_nonneg _)
  -- When the rescaled error vanishes the remainder vanishes too, so the degenerate case of
  -- the extension is harmless.
  have hRes0 : ∀ n ω, Y n ω = 0 → Res n ω = 0 := by
    intro n ω hY
    have hv : Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀) = 0 := by
      simpa [Y] using hY
    by_cases hn : n = 0
    · subst n
      have h0 : Real.sqrt ((0 : ℕ) : ℝ) = 0 := by simp
      simp [Res, gmmNormalizedMoment, h0]
    · have hsqrt : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
      have hΔ : θn n ω = prob.θ₀ := by
        rcases smul_eq_zero.mp hv with h | h
        · exact absurd h hsqrt.ne'
        · exact sub_eq_zero.mp h
      simp [Res, hΔ, hv]
  refine ⟨C', ?_, ?_, ?_⟩
  · exact IsLittleOp.of_abs_le_const_mul_one_on_event (C := 1) zero_lt_one hClo hGc
      (fun n ω hmem => by simp [C', hmem])
  · intro n ω
    by_cases h : ω ∈ G n
    · simpa [C', h] using hCnonneg n ω
    · simp only [C', if_neg h]
      exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro n ω
    by_cases h : ω ∈ G n
    · simpa [C', h, Res, Y] using hExpansion n ω h
    · by_cases hY0 : Y n ω = 0
      · have hres : Res n ω = 0 := hRes0 n ω hY0
        show Res n ω ≤ C' n ω * Y n ω
        rw [hres, hY0, mul_zero]
      · show Res n ω ≤ C' n ω * Y n ω
        simp only [C', if_neg h]
        rw [div_mul_cancel₀ _ hY0]

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- **Empirical mean-value expansion for smooth GMM moments.** For [smooth GMM
moments](hyp:reg) and [an iid sample and estimator](hyp:S,θn), if [the
estimator is consistent](hyp:hConsistent) and [its root-sample-size rescaling
is bounded in probability](hyp:hRootRate), then [the normalized fitted sample
moment equals the normalized true sample moment plus the population Jacobian
applied to the rescaled parameter error, up to `o_P(1)`](goal). -/
theorem gmmNormalizedMoment_expansion_isLittleOp
    [IsProbabilityMeasure μ]
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (S : IIDSample Ω X μ P)
    (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hRootRate : IsBigOp
      (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - prob.θ₀‖)
      (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω => ‖gmmNormalizedMoment S prob.g (θn n ω) n ω -
        (gmmNormalizedMoment S prob.g prob.θ₀ n ω +
          prob.G (Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)))‖)
      (fun _ => (1 : ℝ)) μ := by
  rcases exists_gmmNormalizedMoment_expansion_control reg S θn hConsistent with
    ⟨C, hClo, hCnonneg, hExpansion⟩
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) • (θn n ω - prob.θ₀)‖
  have hYbig : IsBigOp Y (fun _ => (1 : ℝ)) μ := by
    simpa [Y, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      using hRootRate
  have hCY : IsLittleOp (fun n ω => C n ω * Y n ω)
      (fun _ => (1 : ℝ)) μ := by
    simpa using hClo.mul_isBigOp
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one) hYbig
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) zero_lt_one hCY ?_
  intro n ω
  rw [one_mul, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (hCnonneg n ω) (norm_nonneg _))]
  exact hExpansion n ω

end

end Causalean.Stat
