module

public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Uniformization
public import Causalean.Stat.Bootstrap.SmoothZEstimator.SamplingLinearization

/-!
# Conditional bootstrap linearization for smooth Z-estimators

This module is the bootstrap analogue of smooth Z-estimator asymptotic linearity.  It combines
Taylor expansion at the population target, the bootstrap weak law for the target Jacobian and
Lipschitz envelope, and conditional tightness of the centered target score mean.  No bootstrap
Donsker or stochastic-equicontinuity premise appears.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {mu : Measure Omega} {P : Measure X}

private theorem measureReal_union_five_le {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (s₁ s₂ s₃ s₄ s₅ : Set A) :
    nu.real (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅) ≤
      nu.real s₁ + nu.real s₂ + nu.real s₃ + nu.real s₄ + nu.real s₅ := by
  have h₁ := measureReal_union_le (μ := nu) s₁ s₂
  have h₂ := measureReal_union_le (μ := nu) (s₁ ∪ s₂) s₃
  have h₃ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃) s₄
  have h₄ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃ ∪ s₄) s₅
  linarith

private theorem measureReal_union_nine_le {A : Type*} [MeasurableSpace A]
    (nu : Measure A) (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Set A) :
    nu.real (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ s₇ ∪ s₈ ∪ s₉) ≤
      nu.real s₁ + nu.real s₂ + nu.real s₃ + nu.real s₄ + nu.real s₅ +
        nu.real s₆ + nu.real s₇ + nu.real s₈ + nu.real s₉ := by
  have h₁ := measureReal_union_le (μ := nu) s₁ s₂
  have h₂ := measureReal_union_le (μ := nu) (s₁ ∪ s₂) s₃
  have h₃ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃) s₄
  have h₄ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃ ∪ s₄) s₅
  have h₅ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅) s₆
  have h₆ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆) s₇
  have h₇ := measureReal_union_le (μ := nu) (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ s₇) s₈
  have h₈ := measureReal_union_le (μ := nu)
    (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ s₇ ∪ s₈) s₉
  linarith

omit [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem scoreResidual_populationRemainder_le
    (psi : E → X → E) (theta0 : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity psi theta0 P)
    (L : X → ℝ) (hLnonneg : ∀ x, 0 ≤ L x)
    {delta : ℝ}
    (hLbound : ∀ theta ∈ Metric.closedBall theta0 delta,
      ∀ theta' ∈ Metric.closedBall theta0 delta, ∀ x,
      ‖reg.deriv theta x - reg.deriv theta' x‖ ≤ L x * ‖theta - theta'‖)
    (hJleft : ∀ v : E, reg.jacobianInv (reg.jacobian v) = v)
    {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) (theta : E)
    (htheta : theta ∈ Metric.closedBall theta0 delta)
    (hsmall : (‖reg.jacobianInv‖ + 1) *
      (‖finMean (fun i ↦ reg.deriv theta0 (x i)) - reg.jacobian‖ +
        finMean (fun i ↦ L (x i)) * ‖theta - theta0‖) ≤ 1 / 2) :
    ‖Real.sqrt (n : ℝ) • (theta - theta0) -
        (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, reg.influence (x i)‖ ≤
      2 * (‖reg.jacobianInv‖ + 1) *
          ‖Real.sqrt (n : ℝ) • zEstimatorSampleScore psi theta x‖ +
        2 * (‖reg.jacobianInv‖ + 1) ^ 2 *
        (‖finMean (fun i ↦ reg.deriv theta0 (x i)) - reg.jacobian‖ +
          finMean (fun i ↦ L (x i)) * ‖theta - theta0‖) *
        ‖Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta0 (x i))‖ := by
  let c : ℝ := ‖reg.jacobianInv‖ + 1
  let C : ℝ :=
    ‖finMean (fun i ↦ reg.deriv theta0 (x i)) - reg.jacobian‖ +
      finMean (fun i ↦ L (x i)) * ‖theta - theta0‖
  let Delta : E := theta - theta0
  let v : E := Real.sqrt (n : ℝ) • Delta
  let U : E := Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta0 (x i))
  let Q : E := Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta (x i))
  let Jn : E →L[ℝ] E := finMean (fun i ↦ reg.deriv theta0 (x i))
  let R : Fin n → E := fun i ↦
    psi theta (x i) - psi theta0 (x i) - reg.deriv theta0 (x i) Delta
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hc : 0 < c := by
    dsimp [c]
    linarith [norm_nonneg reg.jacobianInv]
  have hLbar_nonneg : 0 ≤ finMean (fun i ↦ L (x i)) := by
    unfold finMean
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun i _ ↦ hLnonneg (x i))
  have hCnonneg : 0 ≤ C := by
    exact add_nonneg (norm_nonneg _)
      (mul_nonneg hLbar_nonneg (norm_nonneg _))
  have hR : ∀ i : Fin n, ‖R i‖ ≤ L (x i) * ‖Delta‖ ^ 2 := by
    intro i
    exact reg.score_taylor_remainder_le hLnonneg hLbound htheta (x i)
  have hscoreExpansion :
      finMean (fun i ↦ psi theta (x i)) =
        finMean (fun i ↦ psi theta0 (x i)) + Jn Delta + finMean R := by
    dsimp [Jn]
    unfold finMean
    simp only [smul_apply]
    rw [← smul_add, ← smul_add]
    apply congrArg
    simp only [sum_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [R, Delta]
    abel
  have hscaledR :
      ‖Real.sqrt (n : ℝ) • finMean R‖ ≤
        (finMean (fun i ↦ L (x i)) * ‖Delta‖) * ‖v‖ := by
    calc
      ‖Real.sqrt (n : ℝ) • finMean R‖
          = Real.sqrt (n : ℝ) * ‖finMean R‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
      _ ≤ Real.sqrt (n : ℝ) *
          ((n : ℝ)⁻¹ * ∑ i : Fin n, ‖R i‖) := by
            gcongr
            unfold finMean
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
              (inv_nonneg.2 (Nat.cast_nonneg _))
      _ ≤ Real.sqrt (n : ℝ) *
          ((n : ℝ)⁻¹ * ∑ i : Fin n, (L (x i) * ‖Delta‖ ^ 2)) := by
            gcongr with i
            exact hR i
      _ = (finMean (fun i ↦ L (x i)) * ‖Delta‖) * ‖v‖ := by
            simp only [finMean, v, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg hsqrt.le, smul_eq_mul]
            have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
              Real.sq_sqrt hnpos.le
            field_simp [hsqrt.ne', hn]
            rw [← Finset.sum_mul]
            ring
  have herr :
      ‖U + reg.jacobian v‖ ≤ ‖Q‖ + C * ‖v‖ := by
    have hscore : Q = U + Jn v + Real.sqrt (n : ℝ) • finMean R := by
      dsimp [Q]
      rw [hscoreExpansion]
      simp [U, v, map_smul, smul_add]
    have heq :
        U + reg.jacobian v =
          Q - (Jn - reg.jacobian) v - Real.sqrt (n : ℝ) • finMean R := by
      rw [hscore]
      simp only [sub_apply]
      abel
    rw [heq]
    calc
      ‖Q - (Jn - reg.jacobian) v - Real.sqrt (n : ℝ) • finMean R‖
          ≤ ‖Q‖ + ‖(Jn - reg.jacobian) v‖ +
              ‖Real.sqrt (n : ℝ) • finMean R‖ := by
                exact (norm_sub_le _ _).trans
                  (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ ‖Q‖ + ‖Jn - reg.jacobian‖ * ‖v‖ +
          (finMean (fun i ↦ L (x i)) * ‖Delta‖) * ‖v‖ :=
            add_le_add (add_le_add_right ((Jn - reg.jacobian).le_opNorm v) _)
              hscaledR
      _ = ‖Q‖ + C * ‖v‖ := by simp only [C, Jn]; ring
  have hv_bound : ‖v‖ ≤ 2 * c * (‖U‖ + ‖Q‖) := by
    have hvid : v = -reg.jacobianInv U +
        reg.jacobianInv (U + reg.jacobian v) := by
      rw [map_add, hJleft]
      abel
    have hpre : ‖v‖ ≤ c * (‖U‖ + ‖Q‖) + (1 / 2) * ‖v‖ := calc
      ‖v‖ = ‖-reg.jacobianInv U + reg.jacobianInv (U + reg.jacobian v)‖ :=
        congrArg norm hvid
      _ ≤ ‖reg.jacobianInv U‖ + ‖reg.jacobianInv (U + reg.jacobian v)‖ := by
        simpa [norm_neg] using norm_add_le (-reg.jacobianInv U)
          (reg.jacobianInv (U + reg.jacobian v))
      _ ≤ ‖reg.jacobianInv‖ * ‖U‖ +
          ‖reg.jacobianInv‖ * ‖U + reg.jacobian v‖ :=
            add_le_add (reg.jacobianInv.le_opNorm U)
              (reg.jacobianInv.le_opNorm _)
      _ ≤ c * ‖U‖ + c * (‖Q‖ + C * ‖v‖) := by
        gcongr <;> dsimp [c] <;> linarith [norm_nonneg reg.jacobianInv]
      _ ≤ c * (‖U‖ + ‖Q‖) + (1 / 2) * ‖v‖ := by
        have hcC : c * C ≤ 1 / 2 := by simpa [c, C] using hsmall
        have hmul := mul_le_mul_of_nonneg_right hcC (norm_nonneg v)
        nlinarith
    nlinarith [hpre, mul_nonneg hc.le (add_nonneg (norm_nonneg U) (norm_nonneg Q))]
  have hinfluence :
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, reg.influence (x i) =
        -reg.jacobianInv U := by
    have hcoef : (Real.sqrt (n : ℝ))⁻¹ =
        Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hnpos.le]
    have hU : (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i : Fin n, psi theta0 (x i) = U := by
      dsimp [U]
      unfold finMean
      rw [hcoef, mul_smul]
    calc
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, reg.influence (x i)
          = -(Real.sqrt (n : ℝ))⁻¹ •
              reg.jacobianInv (∑ i : Fin n, psi theta0 (x i)) := by
                simp [SmoothZEstimatorRegularity.influence, map_sum,
                  Finset.smul_sum]
      _ = -reg.jacobianInv ((Real.sqrt (n : ℝ))⁻¹ •
            ∑ i : Fin n, psi theta0 (x i)) := by rw [map_smul]; simp
      _ = -reg.jacobianInv U := by rw [hU]
  rw [hinfluence, sub_neg_eq_add]
  have hremid : v + reg.jacobianInv U =
      reg.jacobianInv (U + reg.jacobian v) := by
    rw [map_add, hJleft]
    abel
  rw [show Real.sqrt (n : ℝ) • (theta - theta0) = v by rfl, hremid]
  calc
    ‖reg.jacobianInv (U + reg.jacobian v)‖
        ≤ ‖reg.jacobianInv‖ * ‖U + reg.jacobian v‖ :=
          reg.jacobianInv.le_opNorm _
    _ ≤ c * (‖Q‖ + C * ‖v‖) := by
      gcongr
      · dsimp [c]
        linarith [norm_nonneg reg.jacobianInv]
    _ ≤ c * (‖Q‖ + C * (2 * c * (‖U‖ + ‖Q‖))) := by gcongr
    _ ≤ 2 * c * ‖Q‖ + 2 * c ^ 2 * C * ‖U‖ := by
      have hcC : c * C ≤ 1 / 2 := by simpa [c, C] using hsmall
      have hQterm : 2 * c ^ 2 * C * ‖Q‖ ≤ c * ‖Q‖ := by
        calc
          2 * c ^ 2 * C * ‖Q‖ = (2 * (c * C)) * (c * ‖Q‖) := by ring
          _ ≤ 1 * (c * ‖Q‖) := by
            apply mul_le_mul_of_nonneg_right (by nlinarith)
            exact mul_nonneg hc.le (norm_nonneg Q)
          _ = c * ‖Q‖ := one_mul _
      calc
        c * (‖Q‖ + C * (2 * c * (‖U‖ + ‖Q‖))) =
            c * ‖Q‖ + 2 * c ^ 2 * C * ‖U‖ +
              2 * c ^ 2 * C * ‖Q‖ := by ring
        _ ≤ c * ‖Q‖ + 2 * c ^ 2 * C * ‖U‖ + c * ‖Q‖ := by gcongr
        _ = 2 * c * ‖Q‖ + 2 * c ^ 2 * C * ‖U‖ := by ring

set_option maxHeartbeats 800000 in
-- The nested conditional-event argument needs extra elaboration budget for its large set terms.
/-- For [a score, target, and population law](hyp:psi,theta0,P), [a smooth Z-estimator regularity
package](hyp:reg), [an iid sample and sample-function estimator](hyp:S,est), [data and bootstrap
consistency](hyp:hConsistent,hBootConsistent), and [data and bootstrap solution of the estimating
equation up to negligible root-sample-size residuals](hyp:hSolve,hBootSolve), [the conditional
bootstrap vector linearization remainder vanishes in bootstrap probability, in outer sampling
probability](goal). -/
theorem zEstimator_bootstrapLinearization
    [IsProbabilityMeasure mu]
    (psi : E → X → E) (theta0 : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity psi theta0 P)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hConsistent : ∀ epsilon > 0,
      Tendsto
        (fun n ↦ mu {omega |
          epsilon < ‖est n (S.sampleVector n omega) - theta0‖})
        atTop (nhds 0))
    (hSolve : SolvesEstimatingEquationInProbability S psi est)
    (hBootConsistent : BootstrapEstimatorConsistent S est theta0)
    (hBootSolve : BootstrapSolvesEstimatingEquationInProbability S psi est) :
    BootstrapTendstoInProbability S
      (zEstimatorBootstrapRemainder est reg.influence)
      (fun _ _ ↦ 0) := by
  classical
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  rcases reg.deriv_lipschitz with ⟨deltaL, hdeltaL, L, hLmeas, hLint, hLnonneg, hLbound⟩
  have hJleft : ∀ v : E, reg.jacobianInv (reg.jacobian v) = v := by
    have hJsurj : Function.Surjective reg.jacobian := fun y ↦
      ⟨reg.jacobianInv y, by
        have h := congrArg (fun T : E →L[ℝ] E ↦ T y) reg.jacobian_inverse
        simpa [SmoothZEstimatorRegularity.jacobian] using h⟩
    have hJinj : Function.Injective reg.jacobian :=
      (LinearMap.injective_iff_surjective
        (f := (reg.jacobian : E →ₗ[ℝ] E))).mpr hJsurj
    intro v
    apply hJinj
    have h := congrArg (fun T : E →L[ℝ] E ↦ T (reg.jacobian v))
      reg.jacobian_inverse
    simpa [SmoothZEstimatorRegularity.jacobian] using h
  let eJ := toEuclidean (E := E →L[ℝ] E)
  let ePsi := toEuclidean (E := E)
  let gJ : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ (E →L[ℝ] E))) :=
    fun x ↦ eJ (reg.deriv theta0 x)
  let gPsi : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun x ↦ ePsi (psi theta0 x)
  have hgJ : Measurable gJ := eJ.continuous.measurable.comp reg.deriv_at_target_meas
  have hgJint : Integrable gJ P :=
    eJ.toContinuousLinearMap.integrable_comp reg.deriv_at_target_integrable
  have hgPsi : Measurable gPsi := ePsi.continuous.measurable.comp reg.score_meas
  have hgPsi2 : Integrable (fun x ↦ ‖gPsi x‖ ^ 2) P := by
    have hbound : ∀ x, ‖gPsi x‖ ^ 2 ≤
        ‖ePsi.toContinuousLinearMap‖ ^ 2 * ‖psi theta0 x‖ ^ 2 := by
      intro x
      have hop := ePsi.toContinuousLinearMap.le_opNorm (psi theta0 x)
      have hleft : 0 ≤ ‖gPsi x‖ := norm_nonneg _
      have hright : 0 ≤ ‖ePsi.toContinuousLinearMap‖ * ‖psi theta0 x‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      dsimp [gPsi] at hleft ⊢
      calc
        ‖ePsi (psi theta0 x)‖ ^ 2
            ≤ (‖ePsi.toContinuousLinearMap‖ * ‖psi theta0 x‖) ^ 2 :=
          (sq_le_sq₀ hleft hright).2 hop
        _ = ‖ePsi.toContinuousLinearMap‖ ^ 2 * ‖psi theta0 x‖ ^ 2 := by ring
    refine (reg.score_finite_var.const_mul (‖ePsi.toContinuousLinearMap‖ ^ 2)).mono' ?_ ?_
    · exact hgPsi.norm.pow_const 2 |>.aestronglyMeasurable
    · filter_upwards with x
      have hx : 0 ≤ ‖gPsi x‖ ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hbound x
  have hψmem : MemLp (psi theta0) 2 P :=
    (memLp_two_iff_integrable_sq_norm reg.score_meas.aestronglyMeasurable).2
      reg.score_finite_var
  have hψint : Integrable (psi theta0) P := hψmem.integrable (by norm_num)
  let U : ℕ → Omega → E :=
    IsAsymLinearVec.normalizedSum S (psi theta0) (fun m ↦ Finset.range m)
  have hUmean : ∀ n omega, U n omega =
      Real.sqrt (n : ℝ) • S.sampleMeanVec (psi theta0) n omega := by
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
      ∑ i ∈ Finset.range n, psi theta0 (S.Z i omega) by
        funext omega
        simp [U, IsAsymLinearVec.normalizedSum_def]]
    exact ((Finset.measurable_sum _
      (fun i _ ↦ reg.score_meas.comp (S.meas i))).const_smul _).aemeasurable
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit reg.score_meas reg.score_finite_var) mu hUmeas := by
    simpa only [U] using
      S.clt_normalizedSum_vec reg.score_meas reg.score_finite_var reg.identification
  have hNormUclt := Tendsto_dist_vec.map_continuous continuous_norm hUmeas hUclt
  have hUbig : IsBigOp (fun n omega ↦ ‖U n omega‖)
      (fun _ ↦ (1 : ℝ)) mu := by
    let _ : IsProbabilityMeasure
        ((gaussianLimit reg.score_meas reg.score_finite_var).map norm) :=
      Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
    exact Tendsto_dist.tightness
      (fun n ↦ continuous_norm.measurable.comp_aemeasurable (hUmeas n))
      ((Tendsto_dist_iff _ _ _ _).2 hNormUclt)
  have hSampling := zEstimator_samplingLinearization
    psi theta0 P reg S est hConsistent hSolve
  have hJdata : Tendsto_inProb
      (fun n omega ↦ ‖S.sampleMeanVec (reg.deriv theta0) n omega - reg.jacobian‖)
      (fun _ ↦ 0) mu := by
    rw [Tendsto_inProb_iff_hub,
      Modes.tendstoInProbability_zero_iff_isLittleOpF_one]
    simpa [IsLittleOp, SmoothZEstimatorRegularity.jacobian] using
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
  let inner : ℝ := delta / 5
  have hinner : 0 < inner := by dsimp [inner]; linarith
  rcases hUbig (ENNReal.ofReal alpha) (ENNReal.ofReal_pos.mpr halpha) with
    ⟨M0raw, hM0rawpos, hM0raw⟩
  let M0 : ℝ := max M0raw 1
  have hM0 : 0 < M0 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM0lim : Filter.limsup
      (fun n ↦ mu {omega | M0 < ‖U n omega‖}) atTop ≤ ENNReal.ofReal alpha := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_))
      (Filter.limsup_le_of_le (h := hM0raw))
    intro n
    apply measure_mono
    intro omega homega
    simpa [abs_of_nonneg (norm_nonneg _)] using
      ((le_max_left M0raw 1).trans_lt homega).le
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
  rcases scaledBootstrapMeanDifferenceVec_outer_tight S gPsi hgPsi hgPsi2
      inner hinner alpha halpha with ⟨M1, hM1, hScoreBoot⟩
  let kPsi : ℝ := ‖ePsi.symm.toContinuousLinearMap‖ + 1
  have hkPsi : 0 < kPsi := by
    dsimp [kPsi]
    linarith [norm_nonneg ePsi.symm.toContinuousLinearMap]
  let K : ℝ := max (M0 + kPsi * M1) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c : ℝ := ‖reg.jacobianInv‖ + 1
  have hc : 0 < c := by dsimp [c]; linarith [norm_nonneg reg.jacobianInv]
  let a : ℝ := min (1 / (12 * c)) (min (epsilon / (24 * c ^ 2 * K)) 1)
  have ha : 0 < a := by dsimp [a]; positivity
  let kJ : ℝ := ‖eJ.symm.toContinuousLinearMap‖ + 1
  have hkJ : 0 < kJ := by
    dsimp [kJ]
    linarith [norm_nonneg eJ.symm.toContinuousLinearMap]
  let ML : ℝ := |∫ x, L x ∂P| + 2
  have hML : 0 < ML := by dsimp [ML]; linarith [abs_nonneg (∫ x, L x ∂P)]
  let qJ : ℕ → Omega → ℝ := fun n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | a / kJ < ‖finMean (fun i ↦ gJ (xstar i)) -
        finMean (fun i ↦ gJ (S.sampleVector n omega i))‖}
  let qL : ℕ → Omega → ℝ := fun n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | 1 < |finMean (fun i ↦ L (xstar i)) -
        finMean (fun i ↦ L (S.sampleVector n omega i))|}
  have qJmeas (n : ℕ) : Measurable (qJ n) := by
    let A : Set ((Fin n → X) × (Fin n → X)) := {z |
      a / kJ < ‖finMean (fun i ↦ gJ (z.2 i)) - finMean (fun i ↦ gJ (z.1 i))‖}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold finMean
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
      1 < |finMean (fun i ↦ L (z.2 i)) - finMean (fun i ↦ L (z.1 i))|}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold finMean
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
  have hqJouter := measureReal_gt_tendsto_zero_of_ae_tendsto qJmeas qJae inner hinner
  have hqLouter := measureReal_gt_tendsto_zero_of_ae_tendsto qLmeas qLae inner hinner
  have hqJ := hqJouter.eventually (Metric.ball_mem_nhds 0 halpha)
  have hqL := hqLouter.eventually (Metric.ball_mem_nhds 0 halpha)
  have hresidual := (hBootSolve (epsilon / (8 * c)) (by positivity) inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hcons := (hBootConsistent (min (a / ML) deltaL)
      (lt_min (div_pos ha hML) hdeltaL) inner hinner).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hJd := (tendstoInMeasure_iff_measureReal_norm.mp hJdata a ha).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hLd := (tendstoInMeasure_iff_measureReal_norm.mp hLdata 1 zero_lt_one).eventually
    (Metric.ball_mem_nhds 0 halpha)
  have hRd := (tendstoInMeasure_iff_measureReal_norm.mp hSampling (epsilon / 2)
      (by positivity)).eventually
    (Metric.ball_mem_nhds 0 halpha)
  apply eventually_atTop.1
  filter_upwards [hUdata, hScoreBoot, hqJ, hqL, hresidual, hcons, hJd, hLd, hRd,
      eventually_ne_atTop 0] with n hUn hScore_n hqJn hqLn hresidualn hconsn hJdn hLdn hRdn hn
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    at hqJn hqLn hresidualn hconsn hJdn hLdn hRdn ⊢
  have hJdn' : mu.real {x |
      a ≤ ‖S.sampleMeanVec (reg.deriv theta0) n x - reg.jacobian‖} < alpha := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hJdn
  have hRdn' : mu.real {x |
      epsilon / 2 ≤ ‖zEstimatorSamplingRemainder
        S est theta0 reg.influence n x‖} < alpha := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hRdn
  let badU : Set Omega := {omega | M0 < ‖U n omega‖}
  let badScore : Set Omega := {omega |
    inner < (bootstrapResample (S.sampleVector n omega)).real
      {xstar | M1 < ‖scaledBootstrapMeanDifference gPsi n
        (S.sampleVector n omega) xstar‖}}
  let badJboot : Set Omega := {omega | inner < qJ n omega}
  let badLboot : Set Omega := {omega | inner < qL n omega}
  let badResidual : Set Omega := {omega |
    inner < (bootstrapResample (S.sampleVector n omega)).real
      {xstar | epsilon / (8 * c) <
        ‖Real.sqrt (n : ℝ) • zEstimatorSampleScore psi (est n xstar) xstar‖}}
  let badCons : Set Omega := {omega |
    inner < (bootstrapResample (S.sampleVector n omega)).real
      {xstar | min (a / ML) deltaL < ‖est n xstar - theta0‖}}
  let badJdata : Set Omega := {omega |
    a ≤ ‖S.sampleMeanVec (reg.deriv theta0) n omega - reg.jacobian‖}
  let badLdata : Set Omega := {omega |
    1 ≤ |S.sampleMean L n omega - ∫ x, L x ∂P|}
  let badRdata : Set Omega := {omega |
    epsilon / 2 ≤ ‖zEstimatorSamplingRemainder
      S est theta0 reg.influence n omega‖}
  have houterSubset :
      {omega | delta < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | epsilon < ‖zEstimatorBootstrapRemainder est reg.influence n
          (S.sampleVector n omega) xstar‖}} ⊆
        badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badResidual ∪ badCons ∪
          badJdata ∪ badLdata ∪ badRdata := by
    intro omega homega
    by_contra hgood
    simp only [Set.mem_union, not_or] at hgood
    rcases hgood with ⟨⟨⟨⟨⟨⟨⟨⟨hUgood, hScoreGood⟩, hJbootGood⟩,
      hLbootGood⟩, hResidualGood⟩, hConsGood⟩, hJdataGood⟩, hLdataGood⟩, hRdataGood⟩
    have hUbound : ‖U n omega‖ ≤ M0 :=
      le_of_not_gt (by simpa [badU] using hUgood)
    have hJdataBound :
        ‖S.sampleMeanVec (reg.deriv theta0) n omega - reg.jacobian‖ < a :=
      lt_of_not_ge (by simpa [badJdata] using hJdataGood)
    have hLdataBound : |S.sampleMean L n omega - ∫ x, L x ∂P| < 1 :=
      lt_of_not_ge (by simpa [badLdata] using hLdataGood)
    have hRdataBound :
        ‖zEstimatorSamplingRemainder S est theta0 reg.influence n omega‖ <
          epsilon / 2 :=
      lt_of_not_ge (by simpa [badRdata] using hRdataGood)
    let data : Fin n → X := S.sampleVector n omega
    let bad : Set (Fin n → X) := {xstar | epsilon <
      ‖zEstimatorBootstrapRemainder est reg.influence n data xstar‖}
    let residualFail : Set (Fin n → X) :=
      {xstar | epsilon / (8 * c) <
        ‖Real.sqrt (n : ℝ) • zEstimatorSampleScore psi (est n xstar) xstar‖}
    let consFail : Set (Fin n → X) :=
      {xstar | min (a / ML) deltaL < ‖est n xstar - theta0‖}
    let scoreFail : Set (Fin n → X) := {xstar | M1 <
      ‖scaledBootstrapMeanDifference gPsi n data xstar‖}
    let jFail : Set (Fin n → X) := {xstar | a / kJ <
      ‖finMean (fun i ↦ gJ (xstar i)) - finMean (fun i ↦ gJ (data i))‖}
    let lFail : Set (Fin n → X) := {xstar | 1 <
      |finMean (fun i ↦ L (xstar i)) - finMean (fun i ↦ L (data i))|}
    have hbadSubset : bad ⊆ residualFail ∪ consFail ∪ scoreFail ∪ jFail ∪ lFail := by
      intro xstar hxstar
      by_contra hxgood
      simp only [Set.mem_union, not_or] at hxgood
      rcases hxgood with ⟨⟨⟨⟨hresidualx, hconsx⟩, hscorex⟩, hJx⟩, hLx⟩
      have hJbridge : finMean (fun i ↦ reg.deriv theta0 (data i)) =
          S.sampleMeanVec (reg.deriv theta0) n omega := by
        unfold finMean IIDSample.sampleMeanVec data IIDSample.sampleVector
        rw [Fin.sum_univ_eq_sum_range
          (fun i ↦ reg.deriv theta0 (S.Z i omega)) n]
      have hLbridge : finMean (fun i ↦ L (data i)) = S.sampleMean L n omega := by
        unfold finMean IIDSample.sampleMean data IIDSample.sampleVector
        rw [Fin.sum_univ_eq_sum_range (fun i ↦ L (S.Z i omega)) n]
        rfl
      have hPsiBridge : finMean (fun i ↦ psi theta0 (data i)) =
          S.sampleMeanVec (psi theta0) n omega := by
        unfold finMean IIDSample.sampleMeanVec data IIDSample.sampleVector
        rw [Fin.sum_univ_eq_sum_range (fun i ↦ psi theta0 (S.Z i omega)) n]
      have hJstar :
          ‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) - reg.jacobian‖ ≤
            2 * a := by
        have heq : eJ (finMean (fun i ↦ reg.deriv theta0 (xstar i)) -
            finMean (fun i ↦ reg.deriv theta0 (data i))) =
            finMean (fun i ↦ gJ (xstar i)) - finMean (fun i ↦ gJ (data i)) := by
          simp [gJ, finMean, map_sub, map_sum]
        have horig : ‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) -
            finMean (fun i ↦ reg.deriv theta0 (data i))‖ ≤ a := by
          calc
            _ = ‖eJ.symm (eJ (finMean (fun i ↦ reg.deriv theta0 (xstar i)) -
                finMean (fun i ↦ reg.deriv theta0 (data i))))‖ := by simp
            _ ≤ ‖eJ.symm.toContinuousLinearMap‖ *
                ‖eJ (finMean (fun i ↦ reg.deriv theta0 (xstar i)) -
                  finMean (fun i ↦ reg.deriv theta0 (data i)))‖ :=
              eJ.symm.toContinuousLinearMap.le_opNorm _
            _ ≤ kJ * (a / kJ) := by
              gcongr
              · dsimp [kJ]
                linarith [norm_nonneg eJ.symm.toContinuousLinearMap]
              · rw [heq]
                exact le_of_not_gt hJx
            _ = a := by field_simp [hkJ.ne']
        rw [hJbridge] at horig
        calc
          ‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) - reg.jacobian‖ =
              ‖(finMean (fun i ↦ reg.deriv theta0 (xstar i)) -
                S.sampleMeanVec (reg.deriv theta0) n omega) +
                (S.sampleMeanVec (reg.deriv theta0) n omega - reg.jacobian)‖ := by
                  congr 1
                  abel
          _ ≤ ‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) -
                S.sampleMeanVec (reg.deriv theta0) n omega‖ +
                ‖S.sampleMeanVec (reg.deriv theta0) n omega - reg.jacobian‖ :=
              norm_add_le _ _
          _ ≤ 2 * a := by
            linarith [hJdataBound]
      have hLstar : finMean (fun i ↦ L (xstar i)) ≤ ML := by
        have hdiff := le_trans (le_abs_self
          (finMean (fun i ↦ L (xstar i)) - finMean (fun i ↦ L (data i))))
          (le_of_not_gt hLx)
        have hdataDev : |finMean (fun i ↦ L (data i)) - ∫ x, L x ∂P| ≤ 1 := by
          rw [hLbridge]
          exact hLdataBound.le
        have hdataUpper : finMean (fun i ↦ L (data i)) ≤ ∫ x, L x ∂P + 1 := by
          have := (le_abs_self
            (finMean (fun i ↦ L (data i)) - ∫ x, L x ∂P)).trans hdataDev
          linarith
        dsimp [ML]
        calc
          finMean (fun i ↦ L (xstar i))
              ≤ finMean (fun i ↦ L (data i)) + 1 := by linarith
          _ ≤ |∫ x, L x ∂P| + 2 := by
            linarith [hdataUpper, le_abs_self (∫ x, L x ∂P)]
      have hC :
          ‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) - reg.jacobian‖ +
              finMean (fun i ↦ L (xstar i)) * ‖est n xstar - theta0‖ ≤
            3 * a := by
        have hLstar_nonneg : 0 ≤ finMean (fun i ↦ L (xstar i)) := by
          unfold finMean
          exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun i _ ↦ hLnonneg (xstar i))
        have hdmin : ‖est n xstar - theta0‖ ≤ min (a / ML) deltaL :=
          le_of_not_gt (by simpa [consFail] using hconsx)
        have hd : ‖est n xstar - theta0‖ ≤ a / ML :=
          hdmin.trans (min_le_left _ _)
        have hprod : finMean (fun i ↦ L (xstar i)) * ‖est n xstar - theta0‖ ≤ a := by
          calc
            _ ≤ ML * (a / ML) := mul_le_mul hLstar hd (norm_nonneg _) hML.le
            _ = a := by field_simp [hML.ne']
        linarith
      have hsmall : c *
          (‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) - reg.jacobian‖ +
            finMean (fun i ↦ L (xstar i)) * ‖est n xstar - theta0‖) ≤ 1 / 2 := by
        calc
          _ ≤ c * (3 * a) := mul_le_mul_of_nonneg_left hC hc.le
          _ ≤ 1 / 2 := by
            have ha1 : a ≤ 1 / (12 * c) := min_le_left _ _
            have hca : 12 * c * a ≤ 1 := by
              calc
                12 * c * a ≤ 12 * c * (1 / (12 * c)) := by
                  gcongr
                _ = 1 := by field_simp [hc.ne']
            nlinarith
      have hcenterScore :
          ‖scaledBootstrapMeanDifference (psi theta0) n data xstar‖ ≤ kPsi * M1 := by
        have heq : ePsi (scaledBootstrapMeanDifference (psi theta0) n data xstar) =
            scaledBootstrapMeanDifference gPsi n data xstar := by
          simp [scaledBootstrapMeanDifference, gPsi, finMean, map_sub, map_sum]
        calc
          _ = ‖ePsi.symm (ePsi (scaledBootstrapMeanDifference
              (psi theta0) n data xstar))‖ := by simp
          _ ≤ ‖ePsi.symm.toContinuousLinearMap‖ * ‖ePsi (scaledBootstrapMeanDifference
              (psi theta0) n data xstar)‖ := ePsi.symm.toContinuousLinearMap.le_opNorm _
          _ ≤ kPsi * M1 := by
            rw [heq]
            exact mul_le_mul (by
              dsimp [kPsi]
              linarith [norm_nonneg ePsi.symm.toContinuousLinearMap])
              (le_of_not_gt hscorex) (norm_nonneg _) (by positivity)
      have hUstar :
          ‖Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta0 (xstar i))‖ ≤ K := by
        have hdecomp : Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta0 (xstar i)) =
            scaledBootstrapMeanDifference (psi theta0) n data xstar + U n omega := by
          dsimp [scaledBootstrapMeanDifference]
          rw [hUmean, ← hPsiBridge]
          simp only [smul_sub]
          abel
        rw [hdecomp]
        refine (norm_add_le _ _).trans ?_
        have hsum : kPsi * M1 + M0 ≤ K := by
          dsimp [K]
          linarith [le_max_left (M0 + kPsi * M1) 1]
        exact (add_le_add hcenterScore hUbound).trans hsum
      -- The same good event that bounds the resample error also places the resampled
      -- estimator inside the ball on which the Lipschitz envelope is valid.
      have hball : est n xstar ∈ Metric.closedBall theta0 deltaL := by
        have hdmin : ‖est n xstar - theta0‖ ≤ min (a / ML) deltaL :=
          le_of_not_gt (by simpa [consFail] using hconsx)
        simpa [Metric.mem_closedBall, dist_eq_norm] using
          hdmin.trans (min_le_right _ _)
      have hpop := scoreResidual_populationRemainder_le psi theta0 P reg L hLnonneg
        hLbound hJleft hn xstar (est n xstar) hball
        (by simpa [c] using hsmall)
      have hresidualSmall :
          2 * c * ‖Real.sqrt (n : ℝ) •
              zEstimatorSampleScore psi (est n xstar) xstar‖ ≤ epsilon / 4 := by
        have hscoreResidual :
            ‖Real.sqrt (n : ℝ) •
              zEstimatorSampleScore psi (est n xstar) xstar‖ ≤
                epsilon / (8 * c) :=
          le_of_not_gt (by simpa [residualFail] using hresidualx)
        calc
          2 * c * ‖Real.sqrt (n : ℝ) •
                zEstimatorSampleScore psi (est n xstar) xstar‖
              ≤ 2 * c * (epsilon / (8 * c)) := by gcongr
          _ = epsilon / 4 := by field_simp [hc.ne']; ring
      have hnonlinearSmall :
          2 * c ^ 2 *
              (‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) - reg.jacobian‖ +
                finMean (fun i ↦ L (xstar i)) * ‖est n xstar - theta0‖) *
                ‖Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta0 (xstar i))‖ ≤
            epsilon / 4 := by
        calc
          2 * c ^ 2 *
              (‖finMean (fun i ↦ reg.deriv theta0 (xstar i)) - reg.jacobian‖ +
                finMean (fun i ↦ L (xstar i)) * ‖est n xstar - theta0‖) *
                ‖Real.sqrt (n : ℝ) • finMean (fun i ↦ psi theta0 (xstar i))‖
              ≤ 2 * c ^ 2 * (3 * a) * K := by gcongr
          _ ≤ epsilon / 4 := by
            have ha2 : a ≤ epsilon / (24 * c ^ 2 * K) :=
              le_trans (min_le_right _ _) (min_le_left _ _)
            have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
            have hscale : 24 * c ^ 2 * K * a ≤ epsilon := by
              calc
                24 * c ^ 2 * K * a ≤
                    24 * c ^ 2 * K * (epsilon / (24 * c ^ 2 * K)) := by
                  gcongr
                _ = epsilon := by field_simp [hc2.ne', hK.ne']
            nlinarith
      have hpopSmall :
          ‖Real.sqrt (n : ℝ) • (est n xstar - theta0) -
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, reg.influence (xstar i)‖ ≤
            epsilon / 2 := by
        refine hpop.trans ?_
        calc
          _ ≤ epsilon / 4 + epsilon / 4 := by
            simpa [c] using add_le_add hresidualSmall hnonlinearSmall
          _ = epsilon / 2 := by ring
      have hremainderEq :
          zEstimatorBootstrapRemainder est reg.influence n data xstar =
            (Real.sqrt (n : ℝ) • (est n xstar - theta0) -
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, reg.influence (xstar i)) -
              zEstimatorSamplingRemainder S est theta0 reg.influence n omega := by
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
        have hcoef : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
            (Real.sqrt (n : ℝ))⁻¹ := by
          field_simp [hsqrt.ne']
          rw [Real.sq_sqrt hnpos.le]
        have hstarInf : Real.sqrt (n : ℝ) •
            finMean (fun i ↦ reg.influence (xstar i)) =
              (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, reg.influence (xstar i) := by
          unfold finMean
          rw [smul_smul, hcoef]
        have hdataInf : Real.sqrt (n : ℝ) •
            finMean (fun i ↦ reg.influence (data i)) =
              IsAsymLinearVec.normalizedSum S reg.influence
                (fun m ↦ Finset.range m) n omega := by
          unfold finMean data IIDSample.sampleVector IsAsymLinearVec.normalizedSum
          rw [Fin.sum_univ_eq_sum_range (fun i ↦ reg.influence (S.Z i omega)) n]
          simp only [Finset.card_range]
          rw [smul_smul, hcoef]
        unfold zEstimatorBootstrapRemainder zEstimatorSamplingRemainder
          scaledBootstrapMeanDifference
        simp only [smul_sub]
        rw [hstarInf, hdataInf]
        dsimp [data]
        abel
      change epsilon < ‖zEstimatorBootstrapRemainder est reg.influence n data xstar‖ at hxstar
      rw [hremainderEq] at hxstar
      exact (not_lt_of_ge ((norm_sub_le _ _).trans <| by
        linarith [hpopSmall, hRdataBound.le])) hxstar
    let _ : IsProbabilityMeasure (bootstrapResample data) :=
      bootstrapResample_isProbabilityMeasure data hn
    have hmeasureBad : (bootstrapResample data).real bad ≤ 5 * inner := by
      calc
        _ ≤ (bootstrapResample data).real
            (residualFail ∪ consFail ∪ scoreFail ∪ jFail ∪ lFail) :=
          measureReal_mono hbadSubset
        _ ≤ (bootstrapResample data).real residualFail +
            (bootstrapResample data).real consFail +
            (bootstrapResample data).real scoreFail +
            (bootstrapResample data).real jFail +
            (bootstrapResample data).real lFail :=
          measureReal_union_five_le (bootstrapResample data) _ _ _ _ _
        _ ≤ 5 * inner := by
          have hr : (bootstrapResample data).real residualFail ≤ inner :=
            le_of_not_gt (by simpa [badResidual, residualFail, data] using hResidualGood)
          have hcns : (bootstrapResample data).real consFail ≤ inner :=
            le_of_not_gt (by simpa [badCons, consFail, data] using hConsGood)
          have hs : (bootstrapResample data).real scoreFail ≤ inner :=
            le_of_not_gt (by simpa [badScore, scoreFail, data] using hScoreGood)
          have hj : (bootstrapResample data).real jFail ≤ inner :=
            le_of_not_gt (by simpa [badJboot, jFail, qJ, data] using hJbootGood)
          have hl : (bootstrapResample data).real lFail ≤ inner :=
            le_of_not_gt (by simpa [badLboot, lFail, qL, data] using hLbootGood)
          linarith
    have hmeasureBad' : (bootstrapResample data).real bad ≤ delta := by
      (convert hmeasureBad using 1; dsimp [inner])
      all_goals ring
    have homega' : delta < (bootstrapResample data).real bad := by
      simpa [bad, data] using homega
    exact (not_lt_of_ge hmeasureBad') homega'
  calc
    mu.real {omega | delta < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | epsilon < ‖zEstimatorBootstrapRemainder est reg.influence n
          (S.sampleVector n omega) xstar‖}}
        ≤ mu.real (badU ∪ badScore ∪ badJboot ∪ badLboot ∪ badResidual ∪ badCons ∪
          badJdata ∪ badLdata ∪ badRdata) := measureReal_mono houterSubset
    _ ≤ mu.real badU + mu.real badScore + mu.real badJboot + mu.real badLboot +
        mu.real badResidual + mu.real badCons + mu.real badJdata + mu.real badLdata +
        mu.real badRdata := measureReal_union_nine_le mu _ _ _ _ _ _ _ _ _
    _ < eta := by
      dsimp [badU, badScore, badJboot, badLboot, badResidual, badCons, badJdata,
        badLdata, badRdata, qJ, qL] at *
      have halpha_eq : 12 * alpha = eta := by dsimp [alpha]; ring
      linarith [hJdn', hRdn']

end

end Causalean.Stat
