/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.Feasible
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.Helpers

/-! # K-fold empirical Jacobian consistency

This file derives consistency of the fold-averaged affine-score coefficient
from foldwise coefficient nuisance rates. It closes the probabilistic premise
used by the algebraic feasible-DML2 transfer theorem.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

private lemma tendstoInProb_zero_of_isLittleOp_one'
    {X : ℕ → Ω → ℝ} (h : IsLittleOp X (fun _ => (1 : ℝ)) μ) :
    Tendsto_inProb X (fun _ => 0) μ := by
  rw [Tendsto_inProb_iff]
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have ht := h (ε / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, sub_zero, mul_one] at hω ⊢
  linarith

private lemma isLittleOp_congr_eventually
    {X Y : ℕ → Ω → ℝ}
    (hX : IsLittleOp X (fun _ => (1 : ℝ)) μ)
    (hXY : ∀ᶠ n in atTop, X n = Y n) :
    IsLittleOp Y (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  refine (hX ε hε).congr' ?_
  filter_upwards [hXY] with n hn
  rw [hn]

/-- **K-fold empirical Jacobian consistency for an affine score.** For [an
affine moment system](hyp:M), [an i.i.d. sample](hyp:sample), [a nonempty
K-fold split](hyp:split,hK_pos), and [fold-specific complementary-sample
nuisance fits](hyp:η_hat), suppose [the true coefficient is
square-integrable](hyp:h_a_truth), and, on every fold, [the coefficient
increment is jointly and uncurried product-measurable](hyp:hΔa_meas,hΔa_uncurry_train),
with [a curried training-complement witness retained for
compatibility](hyp:_hΔa_train),
[square-integrable](hyp:hΔa_memLp), has [vanishing L² norm](hyp:hΔa_rate), and
has [vanishing population mean](hyp:hΔa_bias_rate). Then [the fold-averaged
empirical score coefficient converges in probability to the population
Jacobian](goal).

The compatibility witness does not enter the proof. -/
theorem crossFitLinearDML_jacobianConsistency
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 0 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (_hΔa_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z))
    (hΔa_uncurry_train : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n k ω,
      MemLp (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z)
    (hΔa_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (hΔa_bias_rate : ∀ k, IsLittleOp
      (fun n ω => ∫ z, (M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) ∂P_Z)
      (fun _ => (1 : ℝ)) μ) :
    Tendsto_inProb
      (fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ *
          ∑ i ∈ split.fold n k, M.m_a (η_hat n k ω) (sample.Z i ω))
      (fun _ => M.linScale) μ := by
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← sample.law]
    exact Measure.isProbabilityMeasure_map (sample.meas 0).aemeasurable
  let Y : Fin K → ℕ → Ω → ℝ := fun k n ω =>
    ((split.fold n k).card : ℝ)⁻¹ *
      ∑ i ∈ split.fold n k, M.m_a (η_hat n k ω) (sample.Z i ω)
  have hfold : ∀ k, IsLittleOp (fun n ω => Y k n ω - M.linScale)
      (fun _ => (1 : ℝ)) μ := by
    intro k
    let truthCentered : Z → ℝ := fun z => M.m_a M.η₀ z - M.linScale
    have htc_meas : Measurable truthCentered :=
      (M.m_a_meas M.η₀).sub measurable_const
    have htc_mean : ∫ z, truthCentered z ∂P_Z = 0 := by
      rw [integral_sub (h_a_truth.integrable (by norm_num))
        (integrable_const M.linScale),
        M.linScale_eq]
      simp
    have htc_sq : Integrable (fun z => truthCentered z ^ 2) P_Z := by
      exact (h_a_truth.sub (memLp_const M.linScale)).integrable_sq
    let truthFluct : ℕ → Ω → ℝ := fun n ω =>
      ((split.fold n k).card : ℝ)⁻¹ *
        ∑ i ∈ split.fold n k, truthCentered (sample.Z i ω)
    have hnorm : IsBigOp
        (fun n ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k, truthCentered (sample.Z i ω))
        (fun _ => (1 : ℝ)) μ :=
      foldNormalizedSum_isBigOp sample truthCentered htc_meas htc_mean htc_sq split k
    have hinv : Tendsto
        (fun n => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (split.grow k))).inv_tendsto_atTop
    have htruth : IsLittleOp truthFluct (fun _ => (1 : ℝ)) μ := by
      have hp := IsBigOp.const_mul_tendsto_zero hnorm hinv
      convert hp using 1
      funext n ω
      simp only [truthFluct]
      rw [← mul_assoc]
      have hsqrt :
          ((split.fold n k).card : ℝ)⁻¹ =
            (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
              (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ := by
        rw [← mul_inv]
        rcases Nat.eq_zero_or_pos (split.fold n k).card with hz | hp
        · simp [hz]
        · rw [Real.mul_self_sqrt (by positivity)]
      rw [hsqrt]
    let f : ℕ → Ω → Z → ℝ := fun n ω z =>
      M.m_a (η_hat n k ω) z - M.m_a M.η₀ z
    let centered : ℕ → Ω → ℝ := fun n ω =>
      ((split.fold n k).card : ℝ)⁻¹ * ∑ i ∈ split.fold n k,
        (f n ω (sample.Z i ω) - ∫ z, f n ω z ∂P_Z)
    have hcentered : IsLittleOp centered (fun _ => (1 : ℝ)) μ := by
      let G : ℕ → Ω → ℝ := fun n ω =>
        (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k,
            (f n ω (sample.Z i ω) - ∫ z, f n ω z ∂P_Z)
      have hG : IsLittleOp G (fun _ => (1 : ℝ)) μ := by
        simpa [G, f] using KFoldSplit.fold_centered_sum_isLittleOp_one
          sample split k f (fun n => hΔa_meas n k)
          (fun n => hΔa_uncurry_train n k) (fun n ω => hΔa_memLp n k ω)
          (hΔa_rate k)
      have hGbig : IsBigOp G (fun _ => (1 : ℝ)) μ :=
        (tendstoInProb_zero_of_isLittleOp_one' hG).isBigOp_one
      have hp := IsBigOp.const_mul_tendsto_zero hGbig hinv
      convert hp using 1
      funext n ω
      simp only [centered, G]
      rw [← mul_assoc]
      have hsqrt :
          ((split.fold n k).card : ℝ)⁻¹ =
            (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
              (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ := by
        rw [← mul_inv]
        rcases Nat.eq_zero_or_pos (split.fold n k).card with hz | hp
        · simp [hz]
        · rw [Real.mul_self_sqrt (by positivity)]
      rw [hsqrt]
    let biasEff : ℕ → Ω → ℝ := fun n ω =>
      (((split.fold n k).card : ℝ)⁻¹ * (split.fold n k).card) *
        ∫ z, f n ω z ∂P_Z
    have hbias : IsLittleOp biasEff (fun _ => (1 : ℝ)) μ := by
      refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos
        (hΔa_bias_rate k) ?_
      intro n ω
      rcases Nat.eq_zero_or_pos (split.fold n k).card with hz | hp
      · simp [biasEff, hz]
      · have hne : ((split.fold n k).card : ℝ) ≠ 0 := by positivity
        simp only [biasEff]
        rw [inv_mul_cancel₀ hne, one_mul]
        simpa [f]
    have hcombined : IsLittleOp
        (fun n ω => truthFluct n ω + centered n ω + biasEff n ω)
        (fun _ => (1 : ℝ)) μ :=
      IsLittleOp.add_one (IsLittleOp.add_one htruth hcentered) hbias
    refine isLittleOp_congr_eventually hcombined ?_
    have hpos : ∀ᶠ n in atTop, 0 < (split.fold n k).card :=
      (split.grow k) (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hp
    funext ω
    have hne : ((split.fold n k).card : ℝ) ≠ 0 := by positivity
    simp only [Y, truthFluct, centered, biasEff, f, truthCentered]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    field_simp [hne]
    ring
  let A : ℕ → Ω → ℝ := fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K, Y k n ω
  have hA : IsLittleOp
      (fun n ω => A n ω - M.linScale) (fun _ => (1 : ℝ)) μ := by
    have hsum := IsLittleOp_finset_sum_one (Finset.univ : Finset (Fin K))
      (fun k n ω => Y k n ω - M.linScale) (fun k _ => hfold k)
    have hscaled := IsLittleOp_const_mul_one (K : ℝ)⁻¹ hsum
    convert hscaled using 1
    funext n ω
    simp only [A, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul]
    have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK_pos)
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
  have hzero := tendstoInProb_zero_of_isLittleOp_one' hA
  have hadd := hzero.comp_continuousAt
    (g := fun x : ℝ => x + M.linScale)
    (continuous_add_const M.linScale).continuousAt
  simpa [A, Y] using hadd

/-- **Feasible K-fold affine-score DML asymptotic linearity.** Under [the
mean-zero, finite-variance, orthogonal-remainder, measurability, and foldwise
score-rate conditions used in the K-fold oracle
proof](hyp:hMZ,hFV,hBR_at,h_m_int,h_m_sq_int), [its joint and uncurried
measurability conditions](hyp:h_m_meas,h_m_train_uncurry), and [its score and
product rates](hyp:h_score_diff_rate,h_product_rate),
[a curried score-measurability witness](hyp:h_m_train) and [individual nuisance
rates](hyp:h_indiv_rate_ρ₁,h_indiv_rate_ρ₂) retained for compatibility,
and [the foldwise coefficient conditions of Assumption
3.2](hyp:h_a_truth,hΔa_meas,hΔa_uncurry_train,hΔa_memLp,hΔa_rate,hΔa_bias_rate),
[a curried coefficient-measurability witness retained for
compatibility](hyp:hΔa_train), and [at least two folds and the required
influence and oracle measurability](hyp:hK_pos,hψ_meas,hOracle_meas),
[the feasible DML2 moment-equation solution is asymptotically linear with
influence function `-J₀⁻¹ m(η₀,·,θ₀)` over the full sample](goal).

The compatibility witnesses and individual nuisance rates do not enter the proof. -/
theorem feasibleCrossFitLinearDML_isAsymLinear
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (hMZ : MeanZero M.toGeneralMoment)
    (hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H) {Crem : ℝ}
    (hBR_at : ∀ n k ω,
      |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (h_m_meas : ∀ n k, Measurable
      (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_int : ∀ n k ω,
      Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (h_m_sq_int : ∀ n k ω,
      Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (h_score_diff_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
        2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (h_indiv_rate_ρ₁ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (h_indiv_rate_ρ₂ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (h_product_rate : ∀ k, IsLittleOp
      (fun n ω =>
        ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z))
    (hΔa_uncurry_train : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n k ω,
      MemLp (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z)
    (hΔa_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (hΔa_bias_rate : ∀ k, IsLittleOp
      (fun n ω => ∫ z,
        (M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) ∂P_Z)
      (fun _ => (1 : ℝ)) μ)
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (hOracle_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (crossFitOneStepOracleDML M.toGeneralMoment sample split η_hat)
        M.θ₀ (fun n => Finset.range n) n) μ) :
    IsAsymLinear (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample (fun n => Finset.range n) := by
  have hOracle := crossFitOneStepOracleDML_isAsymLinear_of_everywhere M.toGeneralMoment
    hMZ hFV sample hK_pos split η_hat hBR_at h_m_meas h_m_train
    h_m_train_uncurry h_m_int h_m_sq_int h_score_diff_rate
    h_indiv_rate_ρ₁ h_indiv_rate_ρ₂ h_product_rate
  have hJ := crossFitLinearDML_jacobianConsistency M sample
    (Nat.zero_lt_of_lt hK_pos) split η_hat h_a_truth hΔa_meas hΔa_train
    hΔa_uncurry_train hΔa_memLp hΔa_rate hΔa_bias_rate
  exact feasibleCrossFitLinearDML_isAsymLinear_of_jacobianConsistency
    M sample split η_hat hOracle hJ hψ_meas hOracle_meas

/-- **Pointwise scalar DML2 specialization of Chernozhukov et al. (2018),
Theorem 3.1.** Under [the affine-score DML2 regularity and rates used by the
proof](hyp:hMZ,hFV,hBR_at,h_m_int,h_m_sq_int), [joint and uncurried score
measurability](hyp:h_m_meas,h_m_train_uncurry), [score and product
rates](hyp:h_score_diff_rate,h_product_rate), and [coefficient regularity,
uncurried measurability, and
rates](hyp:h_a_truth,hΔa_meas,hΔa_uncurry_train,hΔa_memLp,hΔa_rate,hΔa_bias_rate),
with [curried score and coefficient measurability
witnesses](hyp:h_m_train,hΔa_train) and [individual nuisance
rates](hyp:h_indiv_rate_ρ₁,h_indiv_rate_ρ₂) retained for compatibility, and for
[at least two folds and the required influence and oracle
measurability](hyp:hK_pos,hψ_meas,hOracle_meas), [the true positive standard
deviation](hyp:σ,hσ_pos,hσ_sq), and [measurability of the full-sample feasible
DML2 numerator and standardized statistic](hyp:hNum_meas,hStud_meas), [the
standardized statistic converges pointwise in distribution to `N(0,1)`](goal).

This specialization does not formalize the theorem's uniformity over expanding
model classes, explicit remainder order, root-sample-size concentration
statement, vector case, or DML1 result. The compatibility inputs do not enter
the proof. -/
theorem feasibleCrossFitLinearDML_tendstoStandardNormal
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (hMZ : MeanZero M.toGeneralMoment)
    (hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H) {Crem : ℝ}
    (hBR_at : ∀ n k ω,
      |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (h_m_meas : ∀ n k, Measurable
      (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_int : ∀ n k ω,
      Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (h_m_sq_int : ∀ n k ω,
      Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (h_score_diff_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
        2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (h_indiv_rate_ρ₁ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (h_indiv_rate_ρ₂ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (h_product_rate : ∀ k, IsLittleOp
      (fun n ω =>
        ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z))
    (hΔa_uncurry_train : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n k ω,
      MemLp (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z)
    (hΔa_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (hΔa_bias_rate : ∀ k, IsLittleOp
      (fun n ω => ∫ z,
        (M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) ∂P_Z)
      (fun _ => (1 : ℝ)) μ)
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (hOracle_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (crossFitOneStepOracleDML M.toGeneralMoment sample split η_hat)
        M.θ₀ (fun n => Finset.range n) n) μ)
    (σ : ℝ) (hσ_pos : 0 < σ)
    (hσ_sq : σ ^ 2 =
      ∫ z, (-M.linScaleInv * M.m M.η₀ z M.θ₀) ^ 2 ∂P_Z)
    (hNum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
        (fun n => Finset.range n) n) μ)
    (hStud_meas : ∀ n, AEMeasurable (fun ω =>
      IsAsymLinear.rescaledEstimator
        (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
        (fun n => Finset.range n) n ω / σ) μ) :
    Tendsto_dist (fun n ω =>
      IsAsymLinear.rescaledEstimator
        (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
        (fun n => Finset.range n) n ω / σ)
      (gaussianMeasure 0 1) μ hStud_meas := by
  have hAL := feasibleCrossFitLinearDML_isAsymLinear M hMZ hFV sample
    hK_pos split η_hat hBR_at h_m_meas h_m_train h_m_train_uncurry
    h_m_int h_m_sq_int h_score_diff_rate h_indiv_rate_ρ₁ h_indiv_rate_ρ₂
    h_product_rate h_a_truth hΔa_meas hΔa_train hΔa_uncurry_train
    hΔa_memLp hΔa_rate hΔa_bias_rate hψ_meas hOracle_meas
  exact feasibleCrossFitLinearDML_tendstoStandardNormal_of_isAsymLinear
    M sample split η_hat hAL hψ_meas σ hσ_pos hσ_sq hNum_meas hStud_meas

end OrthogonalMoments
end Estimation
end Causalean
