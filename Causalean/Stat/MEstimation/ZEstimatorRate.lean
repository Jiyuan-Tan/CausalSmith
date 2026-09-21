/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.GaussianLimit
public import Causalean.Stat.Limit.QuadraticForm
public import Causalean.Stat.MEstimation.EmpiricalExpansion

/-! # Root-sample-size rates for Z-estimators

This module derives the root-sample-size stochastic rate for a consistent
Z-estimator from population differentiability, nonsingularity, stochastic
equicontinuity, and an approximate estimating equation.  The proof is the
Newey--McFadden (1994), Theorem 7.2, stochastic-absorption argument, with
Andrews (1994) stochastic equicontinuity retained as a high-level condition.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Z-estimator rate from an absorbable score bound.** For [a score, target, population
law, and regularity package](hyp:ψ,θ₀,P,reg), [an iid sample](hyp:S), and [an estimator
sequence](hyp:θn), suppose [the estimator is consistent](hyp:hConsistent), [its centered score
process is stochastically equicontinuous](hyp:hStochEquicont), [a nonnegative random
coefficient is negligible](hyp:A,hAlittle,hA_nonneg), [a nonnegative forcing term is bounded
in probability](hyp:B,hBbig,hB_nonneg), and [the normalized score at the estimator is bounded
by that forcing term plus the coefficient times the rescaled estimation error](hyp:hScoreBound).
Then [the rescaled estimation error is bounded in probability](goal).

This is the reusable stochastic-absorption step in Newey--McFadden (1994),
Theorem 7.2.  Applications must prove the displayed score bound; the generic
approximate-root theorem below and feasible GMM do so from their primitive
estimating-equation assumptions. -/
theorem zEstimator_rootRate_of_scoreBound
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (A B : ℕ → Ω → ℝ)
    (hAlittle : IsLittleOp A (fun _ => (1 : ℝ)) μ)
    (hBbig : IsBigOp B (fun _ => (1 : ℝ)) μ)
    (hA_nonneg : ∀ n ω, 0 ≤ A n ω)
    (hB_nonneg : ∀ n ω, 0 ≤ B n ω)
    (hScoreBound : ∀ (n : ℕ) (ω : Ω),
      ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖ ≤
          B n ω + A n ω * ‖Real.sqrt (n : ℝ) • (θn n ω - θ₀)‖) :
    IsBigOp (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖)
      (fun _ => (1 : ℝ)) μ := by
  let : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let U : ℕ → Ω → E :=
    IsAsymLinearVec.normalizedSum S (ψ θ₀) (fun n => Finset.range n)
  let T : ℕ → Ω → E := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)
  let Q : ℕ → Ω → E := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω))
      - Real.sqrt (n : ℝ) •
          ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P
  let R : E → E := fun θ =>
    (∫ z, (ψ θ z - ψ θ₀ z) ∂P) - reg.J₀ (θ - θ₀)
  let d : ℕ → Ω → ℝ := fun n ω => ‖θn n ω - θ₀‖
  let C : ℕ → Ω → ℝ := fun n ω =>
    if d n ω = 0 then 0 else ‖R (θn n ω)‖ / d n ω
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) • (θn n ω - θ₀)‖
  let c : ℝ := ‖reg.J₀_inv‖ + 1
  let Ac : ℕ → Ω → ℝ := fun n ω => c * (A n ω + C n ω)
  let Bb : ℕ → Ω → ℝ := fun n ω =>
    c * (B n ω + ‖U n ω‖ + ‖Q n ω‖)
  have hc : 0 < c := by
    dsimp [c]
    linarith [norm_nonneg reg.J₀_inv]
  have hJleft : ∀ x : E, reg.J₀_inv (reg.J₀ x) = x := by
    have hsurj : Function.Surjective reg.J₀ := fun y =>
      ⟨reg.J₀_inv y, by
        have h := congrArg (fun L : E →L[ℝ] E => L y) reg.J₀_inverse
        simpa using h⟩
    have hinj : Function.Injective reg.J₀ :=
      (LinearMap.injective_iff_surjective (f := (reg.J₀ : E →ₗ[ℝ] E))).mpr hsurj
    intro x
    apply hinj
    have h := congrArg (fun L : E →L[ℝ] E => L (reg.J₀ x)) reg.J₀_inverse
    simpa using h
  have hU_def : ∀ n ω, U n ω =
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) := by
    intro n ω
    simp [U, IsAsymLinearVec.normalizedSum_def]
  have hUmeas : ∀ n, AEMeasurable (U n) μ := by
    intro n
    rw [show U n = fun ω => (Real.sqrt (n : ℝ))⁻¹ •
      ∑ i ∈ Finset.range n, ψ θ₀ (S.Z i ω) by
        funext ω
        exact hU_def n ω]
    exact ((Finset.measurable_sum _
      (fun i _ => (reg.psi_meas θ₀).comp (S.meas i))).const_smul _).aemeasurable
  have hUclt : Tendsto_dist_vec U
      (gaussianLimit (reg.psi_meas θ₀) reg.finite_var) μ hUmeas := by
    exact S.clt_normalizedSum_vec (reg.psi_meas θ₀) reg.finite_var reg.identification
  have hNormUclt := hUclt.map_continuous continuous_norm hUmeas
  have hUbig : IsBigOp (fun n ω => ‖U n ω‖) (fun _ => (1 : ℝ)) μ := by
    letI : IsProbabilityMeasure
        ((gaussianLimit (reg.psi_meas θ₀) reg.finite_var).map norm) :=
      Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
    exact Tendsto_dist.tightness
      (fun n => continuous_norm.measurable.comp_aemeasurable (hUmeas n))
      ((Tendsto_dist_iff _ _ _ _).2 hNormUclt)
  have hQlittle : IsLittleOp (fun n ω => ‖Q n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa [Q] using
      empiricalScoreDiff_isLittleOp_sqrt ψ θ₀ P S θn hConsistent hStochEquicont
  have hQbig := hQlittle.isBigOp_one
  have hF : R =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖ := by
    simpa [R] using populationScoreDiff_eq_jacobian_plus_remainder ψ θ₀ P reg
  have hClittle : IsLittleOp C (fun _ => (1 : ℝ)) μ := by
    intro ε hε
    have hhalf_pos : 0 < ε / 2 := by linarith
    have hnear0 := hF.def hhalf_pos
    have hnear : ∀ᶠ θ in 𝓝 θ₀, ‖R θ‖ ≤ (ε / 2) * ‖θ - θ₀‖ := by
      filter_upwards [hnear0] with θ hθ
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (θ - θ₀))] using hθ
    rcases Metric.eventually_nhds_iff.mp hnear with ⟨ρ, hρpos, hρ⟩
    have hρhalf : 0 < ρ / 2 := by linarith
    have hcons := hConsistent (ρ / 2) hρhalf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcons
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with n
    apply measure_mono
    intro ω hω
    have hCge : ε ≤ C n ω := by
      simpa [abs_of_nonneg (by positivity : 0 ≤ C n ω)] using hω
    by_contra hnot
    have hdle : d n ω ≤ ρ / 2 := le_of_not_gt hnot
    have hdlt : d n ω < ρ := lt_of_le_of_lt hdle (by linarith)
    have hRle : ‖R (θn n ω)‖ ≤ (ε / 2) * d n ω := by
      exact hρ (by simpa [dist_eq_norm, d] using hdlt)
    by_cases hd0 : d n ω = 0
    · have hCzero : C n ω = 0 := by simp [C, hd0]
      linarith
    · have hdpos : 0 < d n ω := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
      have hCle : C n ω ≤ ε / 2 := by
        dsimp [C]
        rw [if_neg hd0]
        exact (div_le_iff₀ hdpos).2 hRle
      linarith
  have hC_nonneg : ∀ n ω, 0 ≤ C n ω := by
    intro n ω
    dsimp [C]
    split_ifs
    · exact le_rfl
    · positivity
  have hRbound : ∀ n ω, ‖R (θn n ω)‖ ≤ C n ω * d n ω := by
    intro n ω
    by_cases hd0 : d n ω = 0
    · have hθ : θn n ω = θ₀ := by
        have : θn n ω - θ₀ = 0 := norm_eq_zero.mp (by simpa [d] using hd0)
        exact sub_eq_zero.mp this
      simp [R, C, d, hθ]
    · have hdpos : 0 < d n ω := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
      dsimp [C]
      rw [if_neg hd0]
      exact le_of_eq ((div_mul_cancel₀ _ hd0).symm)
  have hExpansion : ∀ n ω,
      ‖T n ω - (U n ω + reg.J₀
        (Real.sqrt (n : ℝ) • (θn n ω - θ₀)))‖ ≤
          ‖Q n ω‖ + C n ω * Y n ω := by
    intro n ω
    have hid : T n ω - (U n ω + reg.J₀
          (Real.sqrt (n : ℝ) • (θn n ω - θ₀))) =
        Q n ω + Real.sqrt (n : ℝ) • R (θn n ω) := by
      rw [hU_def]
      dsimp [T, U, Q, R]
      simp only [Finset.sum_sub_distrib, map_smul]
      module
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt (n : ℝ) * ‖R (θn n ω)‖
          ≤ Real.sqrt (n : ℝ) * (C n ω * d n ω) :=
            mul_le_mul_of_nonneg_left (hRbound n ω) (Real.sqrt_nonneg _)
      _ = C n ω * Y n ω := by
        simp [Y, d, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
  have hAclittle : IsLittleOp Ac (fun _ => (1 : ℝ)) μ := by
    have hsum := hAlittle.add_one hClittle
    refine IsLittleOp.of_abs_le_const_mul_one hc hsum ?_
    intro n ω
    simp [Ac, abs_mul, abs_of_pos hc]
  have hBsumBig : IsBigOp
      (fun n ω => B n ω + ‖U n ω‖ + ‖Q n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    exact IsBigOp.add (IsBigOp.add hBbig hUbig) hQbig
  have hBbbig : IsBigOp Bb (fun _ => (1 : ℝ)) μ := by
    intro δ hδ
    obtain ⟨M, hM, htail⟩ := hBsumBig δ hδ
    refine ⟨c * M, mul_pos hc hM, ?_⟩
    filter_upwards [htail] with n hn
    refine (measure_mono fun ω hω => ?_).trans hn
    simp only [Set.mem_setOf_eq, mul_one] at hω ⊢
    dsimp [Bb] at hω
    rw [abs_mul, abs_of_pos hc] at hω
    rw [Real.norm_eq_abs]
    nlinarith
  have hAc_nonneg : ∀ n ω, 0 ≤ Ac n ω := by
    intro n ω
    exact mul_nonneg hc.le (add_nonneg (hA_nonneg n ω) (hC_nonneg n ω))
  have hBb_nonneg : ∀ n ω, 0 ≤ Bb n ω := by
    intro n ω
    exact mul_nonneg hc.le <| add_nonneg
      (add_nonneg (hB_nonneg n ω) (norm_nonneg _)) (norm_nonneg _)
  have hY_nonneg : ∀ n ω, 0 ≤ Y n ω := fun n ω => norm_nonneg _
  have hRateBound : ∀ n ω, Y n ω ≤ Bb n ω + Ac n ω * Y n ω := by
    intro n ω
    let v : E := Real.sqrt (n : ℝ) • (θn n ω - θ₀)
    let err : E := T n ω - (U n ω + reg.J₀ v)
    have hvid : v = reg.J₀_inv (T n ω - U n ω - err) := by
      have hinside : T n ω - U n ω - err = reg.J₀ v := by
        dsimp [err]
        abel
      rw [hinside, hJleft]
    calc
      Y n ω = ‖v‖ := rfl
      _ = ‖reg.J₀_inv (T n ω - U n ω - err)‖ := by rw [hvid]
      _ ≤ ‖reg.J₀_inv‖ * ‖T n ω - U n ω - err‖ :=
        reg.J₀_inv.le_opNorm _
      _ ≤ ‖reg.J₀_inv‖ * (‖T n ω‖ + ‖U n ω‖ + ‖err‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ c * ((B n ω + A n ω * Y n ω) + ‖U n ω‖ +
          (‖Q n ω‖ + C n ω * Y n ω)) := by
        apply mul_le_mul
        · dsimp [c]
          linarith [norm_nonneg reg.J₀_inv]
        · exact add_le_add (add_le_add (hScoreBound n ω) le_rfl)
            (by simpa [err, v] using hExpansion n ω)
        · positivity
        · positivity
      _ = Bb n ω + Ac n ω * Y n ω := by
        simp only [Bb, Ac]
        ring
  have hYbig := hAclittle.isBigOp_of_absorption hBbbig hAc_nonneg hBb_nonneg
    hY_nonneg (Eventually.of_forall fun n => Eventually.of_forall fun ω => hRateBound n ω)
  simpa [Y, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hYbig

/-- **Root-sample-size rate for an approximate-root Z-estimator.** For [a score, target,
population law, and regularity package](hyp:ψ,θ₀,P,reg), [an iid sample and estimator
sequence](hyp:S,θn), if [the estimator is consistent](hyp:hConsistent), [the centered score
process is stochastically equicontinuous](hyp:hStochEquicont), and [the normalized estimating
equation residual is negligible in probability](hyp:hMoment), then [the root-sample-size
estimation error is bounded in probability](goal).

The condition on `hMoment` is `Pₙ ψ(θ̂ₙ) = o_P(n⁻¹/²)`.  The rate is
derived by the stochastic-absorption proof of Newey--McFadden (1994),
Theorem 7.2, using Andrews (1994) stochastic equicontinuity as a high-level
condition. -/
theorem zEstimator_rootRate
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsBigOp (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖)
      (fun _ => (1 : ℝ)) μ := by
  let B : ℕ → Ω → ℝ := fun n ω =>
    ‖(Real.sqrt (n : ℝ))⁻¹ •
      ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖
  apply zEstimator_rootRate_of_scoreBound ψ θ₀ P reg S θn hConsistent hStochEquicont
    (fun _ _ => 0) B
  · simpa using (show IsLittleOp (fun (_ : ℕ) (_ : Ω) => (0 : ℝ))
        (fun _ => (1 : ℝ)) μ by
      intro ε hε
      simpa [not_le.mpr hε])
  · exact hMoment.isBigOp_one
  · intro n ω
    exact le_rfl
  · intro n ω
    exact norm_nonneg _
  · intro n ω
    simp [B]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If [the root-sample-size estimation error is bounded in probability](hyp:hRate), then
[the unscaled error is bounded in probability at the inverse-root sample-size rate](goal) for
[the estimator and target](hyp:θn,θ₀). -/
theorem inverseRootRate_of_rootRate
    (θn : ℕ → Ω → E) (θ₀ : E)
    (hRate : IsBigOp (fun n ω => Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖)
      (fun _ => (1 : ℝ)) μ) :
    IsBigOp (fun n ω => ‖θn n ω - θ₀‖)
      (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  intro ε hε
  rcases hRate ε hε with ⟨M₀, hM₀pos, hM₀tail⟩
  let M := max M₀ 0
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hMpos : 0 < M := hM₀pos.trans_le hM₀M
  refine ⟨M, hMpos, ?_⟩
  filter_upwards [hM₀tail, eventually_gt_atTop (0 : ℕ)] with n hnTail hn
  refine (measure_mono fun ω hω => ?_).trans hnTail
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnorm : M * (Real.sqrt (n : ℝ))⁻¹ ≤ ‖θn n ω - θ₀‖ := by
    simpa [abs_of_nonneg (norm_nonneg _)] using hω
  have hM : M ≤ Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖ := by
    calc
      M = Real.sqrt (n : ℝ) * (M * (Real.sqrt (n : ℝ))⁻¹) := by
        field_simp [hsqrt.ne']
      _ ≤ Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖ :=
        mul_le_mul_of_nonneg_left hnorm hsqrt.le
  change M₀ * 1 ≤ |Real.sqrt (n : ℝ) * ‖θn n ω - θ₀‖|
  rw [abs_of_nonneg (mul_nonneg hsqrt.le (norm_nonneg _))]
  simpa only [mul_one] using hM₀M.trans hM

end Causalean.Stat
