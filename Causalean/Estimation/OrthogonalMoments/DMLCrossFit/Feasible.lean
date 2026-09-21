/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.AsymptoticLinearity
public import Causalean.Stat.Inference.Studentize
public import Causalean.Stat.SampleSplit.FoldBWLLN

/-! # Feasible linear-score double machine learning

This file proves the generic one-shot feasible DML theorem for affine scores.
It first derives consistency of the empirical score coefficient from the
coefficient-level nuisance rates, then transfers the oracle one-step
linearization to the estimator that solves the empirical moment equation. It
also supplies the normalization by the true asymptotic standard deviation.
-/

public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

private lemma tendstoInProb_zero_of_isLittleOp_one
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

/-- **Empirical Jacobian consistency for an affine score.** For [an affine moment
system](hyp:M), [an i.i.d. sample](hyp:sample), [a one-shot split](hyp:split), and
[a complementary-fold nuisance fit](hyp:η_hat), suppose [the true coefficient is
square-integrable](hyp:h_a_truth), [the coefficient increment has the joint and
uncurried training-fold product measurability used for
cross-fitting](hyp:hΔa_meas,hΔa_uncurry_foldA), and [a curried training-fold
witness retained for compatibility](hyp:_hΔa_foldA),
[each increment is square-integrable](hyp:hΔa_memLp), [its L² norm is
`o_P(1)`](hyp:hΔa_rate), and [its population mean is `o_P(1)`](hyp:hΔa_bias_rate).
Then [the evaluation-fold empirical coefficient converges in probability to
the population Jacobian](goal).

The last two rates are the coefficient consequences of Assumption 3.2(c) in
Chernozhukov et al. (2018); the conclusion is derived rather than assumed.
The compatibility witness does not enter the proof. -/
theorem linearDML_jacobianConsistency
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → H)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z)))
    (_hΔa_foldA : ∀ n,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z))
    (hΔa_uncurry_foldA : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n ω,
      MemLp (fun z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z) 2 P_Z)
    (hΔa_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (hΔa_bias_rate : IsLittleOp
      (fun n ω => ∫ z, (M.m_a (η_hat n ω) z - M.m_a M.η₀ z) ∂P_Z)
      (fun _ => (1 : ℝ)) μ) :
    Tendsto_inProb
      (fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, M.m_a (η_hat n ω) (sample.Z i ω))
      (fun _ => M.linScale) μ := by
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← sample.law]
    exact Measure.isProbabilityMeasure_map (sample.meas 0).aemeasurable
  let Y : ℕ → Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, M.m_a (η_hat n ω) (sample.Z i ω)
  let Y₀ : ℕ → Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, M.m_a M.η₀ (sample.Z i ω)
  have hY₀ : Tendsto_inProb Y₀ (fun _ => M.linScale) μ := by
    have h := OneShotSplit.foldB_sampleMean_tendsto_inProb sample split
      (M.m_a_meas M.η₀) h_a_truth
    rw [← M.linScale_eq] at h
    exact h
  let bias : ℕ → Ω → ℝ := fun n ω =>
    ∫ z, (M.m_a (η_hat n ω) z - M.m_a M.η₀ z) ∂P_Z
  let centered : ℕ → Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n,
      ((M.m_a (η_hat n ω) (sample.Z i ω) - M.m_a M.η₀ (sample.Z i ω))
        - bias n ω)
  have hcentered : IsLittleOp centered (fun _ => (1 : ℝ)) μ := by
    let f : ℕ → Ω → Z → ℝ := fun n ω z =>
      M.m_a (η_hat n ω) z - M.m_a M.η₀ z
    let G : ℕ → Ω → ℝ := fun n ω =>
      (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n, (f n ω (sample.Z i ω) - ∫ z, f n ω z ∂P_Z)
    have hG : IsLittleOp G (fun _ => (1 : ℝ)) μ := by
      simpa [G] using foldB_centered_sum_isLittleOp_one sample split f
        hΔa_meas hΔa_uncurry_foldA hΔa_memLp hΔa_rate
    have hGbig : IsBigOp G (fun _ => (1 : ℝ)) μ :=
      (tendstoInProb_zero_of_isLittleOp_one hG).isBigOp_one
    have hinv : Tendsto
        (fun n => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp split.foldB_card_tendsto)).inv_tendsto_atTop
    have hprod := IsBigOp.const_mul_tendsto_zero hGbig hinv
    convert hprod using 1
    funext n ω
    simp only [centered, G, f, bias]
    rw [← mul_assoc]
    have hsqrt :
        ((split.foldB n).card : ℝ)⁻¹ =
          (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
            (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ := by
      rw [← mul_inv]
      rcases Nat.eq_zero_or_pos (split.foldB n).card with hz | hp
      · simp [hz]
      · rw [Real.mul_self_sqrt (by positivity)]
    rw [hsqrt]
  let biasEff : ℕ → Ω → ℝ := fun n ω =>
    (((split.foldB n).card : ℝ)⁻¹ * (split.foldB n).card) * bias n ω
  have hbiasEff : IsLittleOp biasEff (fun _ => (1 : ℝ)) μ := by
    refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hΔa_bias_rate ?_
    intro n ω
    rcases Nat.eq_zero_or_pos (split.foldB n).card with hz | hp
    · simp [biasEff, hz]
    · have hne : ((split.foldB n).card : ℝ) ≠ 0 := by positivity
      simp only [biasEff]
      rw [inv_mul_cancel₀ hne, one_mul]
      simpa [bias]
  have hdiff : (fun n ω => Y n ω - Y₀ n ω) =
      fun n ω => centered n ω + biasEff n ω := by
    funext n ω
    rcases Nat.eq_zero_or_pos (split.foldB n).card with hz | hp
    · simp [Y, Y₀, centered, biasEff, bias, Finset.card_eq_zero.mp hz]
    · have hne : ((split.foldB n).card : ℝ) ≠ 0 := by positivity
      simp only [Y, Y₀, centered, biasEff, bias]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hne, one_mul]
      ring
  have hYsub : IsLittleOp (fun n ω => Y n ω - Y₀ n ω) (fun _ => (1 : ℝ)) μ := by
    rw [hdiff]
    exact IsLittleOp.add_one hcentered hbiasEff
  have hYsubJ : IsLittleOp
      (fun n ω => Y n ω - M.linScale) (fun _ => (1 : ℝ)) μ := by
    convert IsLittleOp.add_one hYsub hY₀.sub_const.isLittleOp_one using 1
    funext n ω
    ring
  have hzero := tendstoInProb_zero_of_isLittleOp_one hYsubJ
  have hadd := hzero.comp_continuousAt
    (g := fun x : ℝ => x + M.linScale)
    (continuous_add_const M.linScale).continuousAt
  simpa [Y] using hadd

/-- **Feasible affine-score DML asymptotic linearity, conditional bridge.** If
[the corresponding oracle one-step estimator is asymptotically linear](hyp:hOracle),
[the empirical coefficient converges to the nonzero population
Jacobian](hyp:hJ), and [the influence function, oracle rescaling, and normalized
influence sum are measurable](hyp:hψ_meas,hOracle_meas,hSum_meas),
then [the solved feasible estimator has the same asymptotic linear expansion](goal).

This lemma isolates the algebraic oracle-to-solved transfer. The public
reference theorem below derives `hJ` from Assumption 3.2 coefficient rates. -/
theorem feasibleLinearDML_isAsymLinear_of_jacobianConsistency
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → H)
    (hOracle : IsAsymLinear
      (oneStepOracleDML M.toGeneralMoment sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB)
    (hJ : Tendsto_inProb
      (fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, M.m_a (η_hat n ω) (sample.Z i ω))
      (fun _ => M.linScale) μ)
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (hOracle_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (oneStepOracleDML M.toGeneralMoment sample split η_hat)
        M.θ₀ split.foldB n) μ)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample
        (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) split.foldB n) μ) :
    IsAsymLinear (feasibleLinearDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB := by
  let A : ℕ → Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, M.m_a (η_hat n ω) (sample.Z i ω)
  let Sψ : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
      ∑ i ∈ split.foldB n, M.m (η_hat n ω) (sample.Z i ω) M.θ₀
  let X : ℕ → Ω → ℝ := IsAsymLinear.rescaledEstimator
    (oneStepOracleDML M.toGeneralMoment sample split η_hat) M.θ₀ split.foldB
  let Y : ℕ → Ω → ℝ := IsAsymLinear.rescaledEstimator
    (feasibleLinearDML M sample split η_hat) M.θ₀ split.foldB
  let F : ℕ → Ω → ℝ := fun n ω => M.linScaleInv - (A n ω)⁻¹
  have hSψ_eq : Sψ = fun n ω => (-M.linScale) * X n ω := by
    funext n ω
    simp only [Sψ, X, IsAsymLinear.rescaledEstimator, oneStepOracleDML,
      GeneralMoment.linScaleInv]
    rcases Nat.eq_zero_or_pos (split.foldB n).card with hz | hp
    · simp [Finset.card_eq_zero.mp hz]
    · have hc : (0 : ℝ) < ((split.foldB n).card : ℝ) := by exact_mod_cast hp
      have hs : Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 := by positivity
      have hj := M.linScale_ne_zero
      field_simp
      rw [Real.sq_sqrt (le_of_lt hc)]
      ring
  have hXdist := hOracle.tendsto_normal_foldB split hψ_meas hOracle_meas hSum_meas
  have hSψ_big : IsBigOp Sψ (fun _ => (1 : ℝ)) μ := by
    rw [hSψ_eq]
    exact Causalean.Stat.IsBigOp.const_mul (-M.linScale)
      (Tendsto_dist.tightness hOracle_meas hXdist)
  have hFinProb : Tendsto_inProb F (fun _ => 0) μ := by
    have hi := hJ.inv M.linScale_ne_zero
    have hs := hi.sub_const
    have hn := hs.comp_continuousAt (g := fun x : ℝ => -x)
      continuous_neg.continuousAt
    simpa [F, A, GeneralMoment.linScaleInv, one_div] using hn
  have hprod : IsLittleOp (fun n ω => Sψ n ω * F n ω) (fun _ => (1 : ℝ)) μ :=
    hSψ_big.mul_isLittleOp_one_isLittleOp hFinProb.isLittleOp_one
  have heq : ∀ n ω, A n ω ≠ 0 → Y n ω - X n ω = Sψ n ω * F n ω := by
    intro n ω hA
    have hp : 0 < (split.foldB n).card := by
      rcases Nat.eq_zero_or_pos (split.foldB n).card with hz | hp
      · exact False.elim (hA (by simp [A, Finset.card_eq_zero.mp hz]))
      · exact hp
    have hc : (0 : ℝ) < ((split.foldB n).card : ℝ) := by exact_mod_cast hp
    have hs : Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 := by positivity
    let B : ℝ := ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n, M.m_b (η_hat n ω) (sample.Z i ω)
    have hscore : ((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, M.m (η_hat n ω) (sample.Z i ω) M.θ₀ =
        A n ω * M.θ₀ + B := by
      simp only [A, B, M.m_decomp]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
      ring
    have hsumscore : (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n, M.m (η_hat n ω) (sample.Z i ω) M.θ₀ =
        Real.sqrt ((split.foldB n).card : ℝ) * (A n ω * M.θ₀ + B) := by
      have hinv : (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ =
          Real.sqrt ((split.foldB n).card : ℝ) *
            ((split.foldB n).card : ℝ)⁻¹ := by
        field_simp
        rw [Real.sq_sqrt (le_of_lt hc)]
      rw [hinv, mul_assoc, hscore]
    have hfeas : feasibleLinearDML M sample split η_hat n ω =
        -(A n ω)⁻¹ * B := rfl
    simp only [Y, X, IsAsymLinear.rescaledEstimator, hfeas,
      oneStepOracleDML, Sψ, F]
    rw [show (((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n, M.m (η_hat n ω) (sample.Z i ω) M.θ₀) =
        A n ω * M.θ₀ + B from hscore, hsumscore]
    field_simp [hA]
    ring
  have hbad : Tendsto (fun n => μ {ω | Y n ω - X n ω ≠ Sψ n ω * F n ω})
      atTop (𝓝 0) := by
    have hsub : ∀ n, {ω | Y n ω - X n ω ≠ Sψ n ω * F n ω} ⊆
        {ω | |M.linScale| ≤ |A n ω - M.linScale|} := by
      intro n ω hw
      simp only [Set.mem_setOf_eq] at hw ⊢
      by_contra hlt
      push_neg at hlt
      have hne : A n ω ≠ 0 := by
        intro hz
        rw [hz, zero_sub, abs_neg] at hlt
        exact (lt_irrefl _ hlt)
      exact hw (heq n ω hne)
    have hjp : 0 < |M.linScale| := abs_pos.mpr M.linScale_ne_zero
    have ht := hJ
    rw [Tendsto_inProb_iff] at ht
    rw [tendstoInMeasure_iff_norm] at ht
    have htail := ht |M.linScale| hjp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => zero_le) ?_
    intro n
    exact measure_mono (hsub n)
  have hYX : IsLittleOp (fun n ω => Y n ω - X n ω) (fun _ => (1 : ℝ)) μ :=
    IsLittleOp.of_eq_on_asymptotic hbad hprod
  refine ⟨hOracle.mean_zero, hOracle.finite_var, ?_⟩
  have hsum := IsLittleOp.add_one hYX hOracle.remainder
  convert hsum using 1
  funext n ω
  simp only [Y, X, IsAsymLinear.rescaledEstimator]
  ring

/-- **Feasible affine-score DML asymptotic linearity.** Under [the mean-zero,
finite-variance, orthogonal-remainder, measurability, and score-rate conditions
of the oracle DML
theorem](hyp:hMZ,hFV,hBR_at,h_m_int,h_m_sq_int), [its joint and uncurried
measurability conditions](hyp:h_m_meas,h_m_foldA_uncurry), and [its score and
product rates](hyp:h_score_diff_rate,h_product_rate),
[a curried score-measurability witness retained for
compatibility](hyp:h_m_foldA),
[the coefficient-level moment and nuisance-rate conditions of Assumption
3.2](hyp:h_a_truth,hΔa_meas,hΔa_uncurry_foldA,hΔa_memLp,hΔa_rate,hΔa_bias_rate),
and [a curried coefficient-measurability witness retained for
compatibility](hyp:hΔa_foldA),
with [a positive limiting validation-fold share](hyp:hc_pos,h_split_rate) and [the required
convergence-wrapper measurability](hyp:hψ_meas,hOracle_meas,hSum_meas),
[the empirical-moment solution is asymptotically linear with influence function
`-J₀⁻¹ m(η₀,·,θ₀)`](goal).

Neither compatibility witness enters the proof. -/
theorem feasibleLinearDML_isAsymLinear
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (hMZ : MeanZero M.toGeneralMoment)
    (hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate : Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H) {Crem : ℝ}
    (hBR_at : ∀ n ω, |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤
      Crem * ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
    (h_m_meas : ∀ n, Measurable (fun p : Ω × Z => M.m (η_hat n p.1) p.2 M.θ₀))
    (h_m_foldA : ∀ n, Measurable[MeasurableSpace.comap
      (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
      (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (h_m_foldA_uncurry : ∀ n, Measurable[(MeasurableSpace.comap
      (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod inferInstance]
      (fun p : Ω × Z => M.m (η_hat n p.1) p.2 M.θ₀))
    (h_m_int : ∀ n ω, Integrable (fun z => M.m (η_hat n ω) z M.θ₀) P_Z)
    (h_m_sq_int : ∀ n ω, Integrable (fun z => (M.m (η_hat n ω) z M.θ₀) ^ 2) P_Z)
    (h_score_diff_rate : IsLittleOp (fun n ω => (eLpNorm
      (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (h_product_rate : IsLittleOp (fun n ω =>
      ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z)))
    (hΔa_foldA : ∀ n, Measurable[MeasurableSpace.comap
      (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
      (fun ω z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z))
    (hΔa_uncurry_foldA : ∀ n, Measurable[(MeasurableSpace.comap
      (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod inferInstance]
      (Function.uncurry (fun ω z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n ω, MemLp
      (fun z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z) 2 P_Z)
    (hΔa_rate : IsLittleOp (fun n ω => (eLpNorm
      (fun z => M.m_a (η_hat n ω) z - M.m_a M.η₀ z) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (hΔa_bias_rate : IsLittleOp
      (fun n ω => ∫ z, (M.m_a (η_hat n ω) z - M.m_a M.η₀ z) ∂P_Z)
      (fun _ => (1 : ℝ)) μ)
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (hOracle_meas : ∀ n, AEMeasurable (IsAsymLinear.rescaledEstimator
      (oneStepOracleDML M.toGeneralMoment sample split η_hat) M.θ₀ split.foldB n) μ)
    (hSum_meas : ∀ n, AEMeasurable (IsAsymLinear.normalizedSum sample
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) split.foldB n) μ) :
    IsAsymLinear (feasibleLinearDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB := by
  have hOracle := oneStepOracleDML_isAsymLinear_of_everywhere
    M.toGeneralMoment hMZ hFV
    sample split hc_pos h_split_rate η_hat hBR_at h_m_meas h_m_foldA
    h_m_foldA_uncurry h_m_int h_m_sq_int h_score_diff_rate h_product_rate
  have hJ := linearDML_jacobianConsistency M sample split η_hat h_a_truth
    hΔa_meas hΔa_foldA hΔa_uncurry_foldA hΔa_memLp hΔa_rate hΔa_bias_rate
  exact feasibleLinearDML_isAsymLinear_of_jacobianConsistency M sample split η_hat
    hOracle hJ hψ_meas hOracle_meas hSum_meas

/-- **True-σ standardized feasible DML limit.** If [the feasible affine-score
estimator is asymptotically linear with the reference influence
function](hyp:hAL), [that influence function is measurable](hyp:hψ_meas),
[its true standard deviation `σ` is positive and has the defining squared-value
identity](hyp:hσ_pos,hσ_sq), and [the numerator, its empirical sum, and standardized statistic are
measurable](hyp:hNum_meas,hSum_meas,hStud_meas), then [the true-σ standardized feasible
estimator converges to the standard normal law](goal). -/
theorem feasibleLinearDML_tendstoStandardNormal_of_isAsymLinear
    [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → H)
    (hAL : IsAsymLinear (feasibleLinearDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB)
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (σ : ℝ) (hσ_pos : 0 < σ)
    (hσ_sq : σ ^ 2 = ∫ z, (-M.linScaleInv * M.m M.η₀ z M.θ₀) ^ 2 ∂P_Z)
    (hNum_meas : ∀ n, AEMeasurable (IsAsymLinear.rescaledEstimator
      (feasibleLinearDML M sample split η_hat) M.θ₀ split.foldB n) μ)
    (hSum_meas : ∀ n, AEMeasurable (IsAsymLinear.normalizedSum sample
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) split.foldB n) μ)
    (hStud_meas : ∀ n, AEMeasurable (fun ω =>
      IsAsymLinear.rescaledEstimator (feasibleLinearDML M sample split η_hat)
        M.θ₀ split.foldB n ω / σ) μ) :
    Tendsto_dist (fun n ω =>
      IsAsymLinear.rescaledEstimator (feasibleLinearDML M sample split η_hat)
        M.θ₀ split.foldB n ω / σ)
      (gaussianMeasure 0 1) μ hStud_meas := by
  have hN := hAL.tendsto_normal_foldB split hψ_meas hNum_meas hSum_meas
  rw [← hσ_sq] at hN
  have hscaled := Tendsto_dist.const_mul_tendsto_gaussian
    (Xn := IsAsymLinear.rescaledEstimator
      (feasibleLinearDML M sample split η_hat) M.θ₀ split.foldB)
    (a := fun _ : ℕ => 1 / σ) (a₀ := 1 / σ) (v := σ ^ 2)
    hNum_meas hN tendsto_const_nhds
  have hvar : (1 / σ) ^ 2 * σ ^ 2 = 1 := by
    field_simp [ne_of_gt hσ_pos]
  rw [hvar] at hscaled
  simpa [div_eq_mul_inv, mul_comm] using hscaled

/-- **K-fold feasible affine-score DML transfer.** Given [an affine moment
system](hyp:M), [an i.i.d. sample and K-fold split](hyp:sample,split), and
[fold-specific complementary-sample nuisance fits](hyp:η_hat), if [the K-fold
oracle one-step object is asymptotically linear](hyp:hOracle), [the
fold-averaged empirical coefficient converges to the population
Jacobian](hyp:hJ), and [the influence function and oracle rescaling are
measurable](hyp:hψ_meas,hOracle_meas), then [the feasible DML2 empirical-moment
solution has the same full-sample asymptotic linear expansion](goal).

The theorem is the K-fold algebraic bridge. Its `hJ` premise is the direct
fold-averaged counterpart of `linearDML_jacobianConsistency`; concrete models
may prove it fold by fold from their Assumption 3.2 coefficient rates. -/
theorem feasibleCrossFitLinearDML_isAsymLinear_of_jacobianConsistency
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ}
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (hOracle : IsAsymLinear
      (crossFitOneStepOracleDML M.toGeneralMoment sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample (fun n => Finset.range n))
    (hJ : Tendsto_inProb
      (fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ *
          ∑ i ∈ split.fold n k, M.m_a (η_hat n k ω) (sample.Z i ω))
      (fun _ => M.linScale) μ)
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (hOracle_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (crossFitOneStepOracleDML M.toGeneralMoment sample split η_hat)
        M.θ₀ (fun n => Finset.range n) n) μ) :
    IsAsymLinear (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample (fun n => Finset.range n) := by
  let A : ℕ → Ω → ℝ := fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
    ((split.fold n k).card : ℝ)⁻¹ *
      ∑ i ∈ split.fold n k, M.m_a (η_hat n k ω) (sample.Z i ω)
  let B : ℕ → Ω → ℝ := fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
    ((split.fold n k).card : ℝ)⁻¹ *
      ∑ i ∈ split.fold n k, M.m_b (η_hat n k ω) (sample.Z i ω)
  let Q : ℕ → Ω → ℝ := fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
    ((split.fold n k).card : ℝ)⁻¹ *
      ∑ i ∈ split.fold n k,
        M.m (η_hat n k ω) (sample.Z i ω) M.θ₀
  let Sψ : ℕ → Ω → ℝ := fun n ω => Real.sqrt (n : ℝ) * Q n ω
  let X : ℕ → Ω → ℝ := IsAsymLinear.rescaledEstimator
    (crossFitOneStepOracleDML M.toGeneralMoment sample split η_hat)
    M.θ₀ (fun n => Finset.range n)
  let Y : ℕ → Ω → ℝ := IsAsymLinear.rescaledEstimator
    (feasibleCrossFitLinearDML M sample split η_hat)
    M.θ₀ (fun n => Finset.range n)
  let F : ℕ → Ω → ℝ := fun n ω => M.linScaleInv - (A n ω)⁻¹
  have hSψ_eq : Sψ = fun n ω => (-M.linScale) * X n ω := by
    funext n ω
    simp only [Sψ, Q, X, IsAsymLinear.rescaledEstimator,
      crossFitOneStepOracleDML, Finset.card_range, GeneralMoment.linScaleInv]
    field_simp [M.linScale_ne_zero]
    ring
  have hXdist := hOracle.tendsto_normal hψ_meas hOracle_meas
  have hSψ_big : IsBigOp Sψ (fun _ => (1 : ℝ)) μ := by
    rw [hSψ_eq]
    exact Causalean.Stat.IsBigOp.const_mul (-M.linScale)
      (Tendsto_dist.tightness hOracle_meas hXdist)
  have hFinProb : Tendsto_inProb F (fun _ => 0) μ := by
    have hi := hJ.inv M.linScale_ne_zero
    have hn := hi.sub_const.comp_continuousAt (g := fun x : ℝ => -x)
      continuous_neg.continuousAt
    simpa [F, A, GeneralMoment.linScaleInv, one_div] using hn
  have hprod : IsLittleOp (fun n ω => Sψ n ω * F n ω)
      (fun _ => (1 : ℝ)) μ :=
    hSψ_big.mul_isLittleOp_one_isLittleOp hFinProb.isLittleOp_one
  have hQ : ∀ n ω, Q n ω = A n ω * M.θ₀ + B n ω := by
    intro n ω
    simp only [Q, A, B, M.m_decomp]
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
    rw [Finset.sum_add_distrib]
    have hfold : ∀ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ *
            ((∑ i ∈ split.fold n k,
              M.m_a (η_hat n k ω) (sample.Z i ω)) * M.θ₀) =
          (((split.fold n k).card : ℝ)⁻¹ *
            ∑ i ∈ split.fold n k,
              M.m_a (η_hat n k ω) (sample.Z i ω)) * M.θ₀ := by
      intro k
      ring
    simp_rw [hfold, ← Finset.sum_mul]
    ring
  have heq : ∀ n ω, A n ω ≠ 0 →
      Y n ω - X n ω = Sψ n ω * F n ω := by
    intro n ω hA
    have hfeas : feasibleCrossFitLinearDML M sample split η_hat n ω =
        -(A n ω)⁻¹ * B n ω := rfl
    simp only [Y, X, IsAsymLinear.rescaledEstimator, Finset.card_range,
      hfeas, crossFitOneStepOracleDML, Sψ, F, Q]
    rw [show ((K : ℝ)⁻¹ * ∑ k : Fin K,
      ((split.fold n k).card : ℝ)⁻¹ *
        ∑ i ∈ split.fold n k,
          M.m (η_hat n k ω) (sample.Z i ω) M.θ₀) =
      A n ω * M.θ₀ + B n ω from hQ n ω]
    field_simp [hA]
    ring
  have hbad : Tendsto (fun n => μ {ω | Y n ω - X n ω ≠ Sψ n ω * F n ω})
      atTop (𝓝 0) := by
    have hsub : ∀ n, {ω | Y n ω - X n ω ≠ Sψ n ω * F n ω} ⊆
        {ω | |M.linScale| ≤ |A n ω - M.linScale|} := by
      intro n ω hw
      simp only [Set.mem_setOf_eq] at hw ⊢
      by_contra hlt
      push_neg at hlt
      have hne : A n ω ≠ 0 := by
        intro hz
        rw [hz, zero_sub, abs_neg] at hlt
        exact lt_irrefl _ hlt
      exact hw (heq n ω hne)
    have ht := hJ
    rw [Tendsto_inProb_iff] at ht
    rw [tendstoInMeasure_iff_norm] at ht
    have htail := ht |M.linScale| (abs_pos.mpr M.linScale_ne_zero)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => zero_le) ?_
    intro n
    exact measure_mono (hsub n)
  have hYX : IsLittleOp (fun n ω => Y n ω - X n ω)
      (fun _ => (1 : ℝ)) μ := IsLittleOp.of_eq_on_asymptotic hbad hprod
  refine ⟨hOracle.mean_zero, hOracle.finite_var, ?_⟩
  convert IsLittleOp.add_one hYX hOracle.remainder using 1
  funext n ω
  simp only [Y, X, IsAsymLinear.rescaledEstimator]
  ring

/-- **True-σ standardized K-fold feasible DML limit.** For [an affine moment
system, i.i.d. sample, K-fold split, and fold-specific nuisance
fits](hyp:M,sample,K,split,η_hat), if [the feasible DML2 estimator has the
reference asymptotic linear expansion](hyp:hAL), [its influence function is
measurable](hyp:hψ_meas), [the true standard deviation `σ` is positive and its
square equals the influence-function second moment](hyp:hσ_pos,hσ_sq), and
[the numerator and standardized statistic are measurable](hyp:hNum_meas,hStud_meas),
then [the true-σ standardized full-sample statistic converges to the standard
normal law](goal). -/
theorem feasibleCrossFitLinearDML_tendstoStandardNormal_of_isAsymLinear
    [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ}
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (hAL : IsAsymLinear (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample (fun n => Finset.range n))
    (hψ_meas : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀))
    (σ : ℝ) (hσ_pos : 0 < σ)
    (hσ_sq : σ ^ 2 = ∫ z, (-M.linScaleInv * M.m M.η₀ z M.θ₀) ^ 2 ∂P_Z)
    (hNum_meas : ∀ n, AEMeasurable (IsAsymLinear.rescaledEstimator
      (feasibleCrossFitLinearDML M sample split η_hat)
      M.θ₀ (fun n => Finset.range n) n) μ)
    (hStud_meas : ∀ n, AEMeasurable (fun ω =>
      IsAsymLinear.rescaledEstimator (feasibleCrossFitLinearDML M sample split η_hat)
        M.θ₀ (fun n => Finset.range n) n ω / σ) μ) :
    Tendsto_dist (fun n ω =>
      IsAsymLinear.rescaledEstimator (feasibleCrossFitLinearDML M sample split η_hat)
        M.θ₀ (fun n => Finset.range n) n ω / σ)
      (gaussianMeasure 0 1) μ hStud_meas := by
  have hN := hAL.tendsto_normal hψ_meas hNum_meas
  rw [← hσ_sq] at hN
  have hscaled := Tendsto_dist.const_mul_tendsto_gaussian
    (Xn := IsAsymLinear.rescaledEstimator
      (feasibleCrossFitLinearDML M sample split η_hat)
      M.θ₀ (fun n => Finset.range n))
    (a := fun _ : ℕ => 1 / σ) (a₀ := 1 / σ) (v := σ ^ 2)
    hNum_meas hN tendsto_const_nhds
  have hvar : (1 / σ) ^ 2 * σ ^ 2 = 1 := by
    field_simp [ne_of_gt hσ_pos]
  rw [hvar] at hscaled
  simpa [div_eq_mul_inv, mul_comm] using hscaled

end OrthogonalMoments
end Estimation
end Causalean
