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
used by the algebraic feasible-DML2 transfer theorem, and states the feasible
DML2 asymptotic-linearity and normal-limit theorems.

The theorems with the `_on_highProbEvent` suffix impose the bilinear remainder bound and
the integrability conditions only on events of probability tending to one; the
theorems without the suffix are their corollaries for nuisance fits satisfying those
conditions at every realization.
-/

public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

private lemma tendstoInProb_zero_of_isLittleOp_one'
    {X : ℕ → Ω → ℝ} (h : IsLittleOp X (fun _ => (1 : ℝ)) μ) :
    Modes.TendstoInProbability (fun _ : ℕ => μ) X atTop (fun _ _ => 0) := by
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

/-- **K-fold empirical Jacobian consistency for an affine score, with square-integrability on
events of probability tending to one.** For [an affine moment system](hyp:M), [an i.i.d.
sample](hyp:sample), [a nonempty K-fold split](hyp:split,hK_pos), and [fold-specific
complementary-sample nuisance fits](hyp:η_hat), let [G_n be events](hyp:goodSet) whose
[complements have probability at most Δ_n](hyp:hfail) for [a sequence Δ_n](hyp:Δ) that [tends to
zero](hyp:hΔ). Suppose [the true coefficient is square-integrable](hyp:h_a_truth), and, on every
fold, [the coefficient increment is jointly and uncurried
product-measurable](hyp:hΔa_meas,hΔa_uncurry_train), [square-integrable at every realization in
G_n](hyp:hΔa_memLp), has [vanishing L² norm](hyp:hΔa_rate), and has [vanishing population
mean](hyp:hΔa_bias_rate). Then [the fold-averaged empirical score coefficient converges in
probability to the population Jacobian](goal). -/
theorem crossFitLinearDML_jacobianConsistency_on_highProbEvent
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 0 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (goodSet : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, μ (goodSet n)ᶜ ≤ Δ n)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_uncurry_train : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n k ω, ω ∈ goodSet n →
      MemLp (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z)
    (hΔa_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (hΔa_bias_rate : ∀ k, IsLittleOp
      (fun n ω => ∫ z, (M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) ∂P_Z)
      (fun _ => (1 : ℝ)) μ) :
    Modes.TendstoInProbability (fun _ : ℕ => μ) (fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ *
          ∑ i ∈ split.fold
              n k, M.m_a (η_hat n k ω) (sample.Z i ω)) atTop (fun _ _ => M.linScale) := by
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
        simpa [G, f] using
          KFoldSplit.fold_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent
          sample split k f goodSet Δ hΔ hfail (fun n => hΔa_meas n k)
          (fun n => hΔa_uncurry_train n k) (fun n ω hω => hΔa_memLp n k ω hω)
          (hΔa_rate k)
      have hGbig : IsBigOp G (fun _ => (1 : ℝ)) μ :=
        Modes.TendstoInProbability.isBigOp_one (tendstoInProb_zero_of_isLittleOp_one' hG)
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
  have hadd := Modes.TendstoInProbability.comp_continuousAt (h := hzero)
    (g := fun x : ℝ => x + M.linScale)
    (continuous_add_const M.linScale).continuousAt
  simpa [A, Y] using hadd

/-- **K-fold empirical Jacobian consistency for an affine score.** For [an
affine moment system](hyp:M), [an i.i.d. sample](hyp:sample), [a nonempty
K-fold split](hyp:split,hK_pos), and [fold-specific complementary-sample
nuisance fits](hyp:η_hat), suppose [the true coefficient is
square-integrable](hyp:h_a_truth), and, on every fold, [the coefficient
increment is jointly and uncurried product-measurable](hyp:hΔa_meas,hΔa_uncurry_train),
[square-integrable](hyp:hΔa_memLp), has [vanishing L² norm](hyp:hΔa_rate), and
has [vanishing population mean](hyp:hΔa_bias_rate). Then [the fold-averaged
empirical score coefficient converges in probability to the population
Jacobian](goal). -/
theorem crossFitLinearDML_jacobianConsistency
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 0 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
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
    Modes.TendstoInProbability (fun _ : ℕ => μ) (fun n ω => (K : ℝ)⁻¹ * ∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ *
          ∑ i ∈ split.fold
              n k, M.m_a (η_hat n k ω) (sample.Z i ω)) atTop (fun _ _ => M.linScale) := by
  exact crossFitLinearDML_jacobianConsistency_on_highProbEvent M sample hK_pos split η_hat
    (fun _ => Set.univ) (fun _ => 0) tendsto_const_nhds (by simp) h_a_truth
    hΔa_meas hΔa_uncurry_train (fun n k ω _ => hΔa_memLp n k ω) hΔa_rate hΔa_bias_rate

/-- **Feasible K-fold affine-score DML asymptotic linearity, with nuisance conditions on events
of probability tending to one.** Take [a moment system whose score is affine in the parameter,
m(η, z, θ) = a(η, z)·θ + b(η, z), with true nuisance η₀, true parameter θ₀, error gauges ρ₁ and
ρ₂, and linearization scale J₀ equal to the population mean of a(η₀, ·)](hyp:M), whose [score has
mean zero at the truth](hyp:hMZ) and [finite second moment at the truth](hyp:hFV). Let [an i.i.d.
sample](hyp:sample) be [split into K folds](hyp:split) with [K at least two](hyp:hK_pos), let
[η̂_{n,k} be the nuisance fit used on fold k at sample size n](hyp:η_hat), and let [G_n be
events](hyp:goodSet) whose [complements have probability at most Δ_n](hyp:hfail) for [a sequence
Δ_n](hyp:Δ) that [tends to zero](hyp:hΔ). Assume that for every n, every fold k and every
realization in G_n [the population moment of m(η̂_{n,k}, ·, θ₀) is bounded in absolute value by a
fixed constant times ρ₁(η̂_{n,k}, η₀)·ρ₂(η̂_{n,k}, η₀)](hyp:hBR_at) and m(η̂_{n,k}, ·, θ₀) is
[integrable](hyp:h_m_int) and [square-integrable](hyp:h_m_sq_int) under the observation law; that
[(ω, z) ↦ m(η̂_{n,k}(ω), z, θ₀) is jointly measurable](hyp:h_m_meas) and [is measurable with
respect to the product of the σ-algebra generated by the observations outside fold k and the
σ-algebra on the observation space](hyp:h_m_train_uncurry); that [for each fold the L² distance
between m(η̂_{n,k}, ·, θ₀) and m(η₀, ·, θ₀) is o_p(1)](hyp:h_score_diff_rate); and that [for each
fold the product ρ₁(η̂_{n,k}, η₀)·ρ₂(η̂_{n,k}, η₀) is o_p(n^(−1/2))](hyp:h_product_rate). For the
coefficient, assume [a(η₀, ·) is square-integrable](hyp:h_a_truth) and that for each fold the
increment a(η̂_{n,k}, ·) − a(η₀, ·) is [jointly measurable in (ω, z)](hyp:hΔa_meas), [measurable
with respect to the same out-of-fold product σ-algebra](hyp:hΔa_uncurry_train), [square-integrable
at every realization in G_n](hyp:hΔa_memLp), [o_p(1) in L²](hyp:hΔa_rate), and [has a population
mean that is o_p(1)](hyp:hΔa_bias_rate). Assume also [z ↦ −J₀⁻¹·m(η₀, z, θ₀) is
measurable](hyp:hψ_meas) and [the rescaled oracle cross-fitted estimator is almost-everywhere
measurable at every sample size](hyp:hOracle_meas). Then [the feasible cross-fitted (DML2) estimator,
minus the fold-averaged empirical mean of b(η̂_{n,k}, ·) divided by the fold-averaged empirical
mean of a(η̂_{n,k}, ·), is asymptotically linear at θ₀ over the full sample with influence
function −J₀⁻¹·m(η₀, z, θ₀)](goal).

The bilinear remainder bound and the integrability conditions are required only on the events
`G_n`, whose probability tends to one, as in Chernozhukov et al. (2018), Assumption 3.2; outside
`G_n` the nuisance fits are unrestricted beyond measurability. -/
theorem feasibleCrossFitLinearDML_isAsymLinear_on_highProbEvent
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (hMZ : MeanZero M.toGeneralMoment)
    (hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (goodSet : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, μ (goodSet n)ᶜ ≤ Δ n) {Crem : ℝ}
    (hBR_at : ∀ n k ω, ω ∈ goodSet n →
      |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (h_m_meas : ∀ n k, Measurable
      (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_int : ∀ n k ω, ω ∈ goodSet n →
      Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (h_m_sq_int : ∀ n k ω, ω ∈ goodSet n →
      Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (h_score_diff_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
        2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (h_product_rate : ∀ k, IsLittleOp
      (fun n ω =>
        ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_uncurry_train : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n k ω, ω ∈ goodSet n →
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
  have hOracle := crossFitOneStepOracleDML_isAsymLinear_on_highProbEvent M.toGeneralMoment
    hMZ hFV sample hK_pos split η_hat goodSet Δ hΔ hfail hBR_at h_m_meas
    h_m_train_uncurry h_m_int h_m_sq_int h_score_diff_rate h_product_rate
  have hJ := crossFitLinearDML_jacobianConsistency_on_highProbEvent M sample
    (Nat.zero_lt_of_lt hK_pos) split η_hat goodSet Δ hΔ hfail h_a_truth hΔa_meas
    hΔa_uncurry_train hΔa_memLp hΔa_rate hΔa_bias_rate
  exact feasibleCrossFitLinearDML_isAsymLinear_of_jacobianConsistency
    M sample split η_hat hOracle hJ hψ_meas hOracle_meas

/-- **Feasible K-fold affine-score DML asymptotic linearity.** Take [a moment system whose score is
affine in the parameter, m(η, z, θ) = a(η, z)·θ + b(η, z), with true nuisance η₀, true parameter
θ₀, error gauges ρ₁ and ρ₂, and linearization scale J₀ equal to the population mean of a(η₀,
·)](hyp:M), whose [score has mean zero at the truth](hyp:hMZ) and [finite second moment at the
truth](hyp:hFV). Let [an i.i.d. sample](hyp:sample) be [split into K folds](hyp:split) with [K at
least two](hyp:hK_pos), and let [η̂_{n,k} be the nuisance fit used on fold k at sample size
n](hyp:η_hat). Assume that for every n, every fold k and every realization [the population moment
of m(η̂_{n,k}, ·, θ₀) is bounded in absolute value by a fixed constant times ρ₁(η̂_{n,k},
η₀)·ρ₂(η̂_{n,k}, η₀)](hyp:hBR_at) and m(η̂_{n,k}, ·, θ₀) is [integrable](hyp:h_m_int) and
[square-integrable](hyp:h_m_sq_int) under the observation law; that [(ω, z) ↦ m(η̂_{n,k}(ω), z,
θ₀) is jointly measurable](hyp:h_m_meas) and [is measurable with respect to the product of the
σ-algebra generated by the observations outside fold k and the σ-algebra on the observation
space](hyp:h_m_train_uncurry); that [for each fold the L² distance between m(η̂_{n,k}, ·, θ₀) and
m(η₀, ·, θ₀) is o_p(1)](hyp:h_score_diff_rate); and that [for each fold the product ρ₁(η̂_{n,k},
η₀)·ρ₂(η̂_{n,k}, η₀) is o_p(n^(−1/2))](hyp:h_product_rate). For the coefficient, assume [a(η₀, ·)
is square-integrable](hyp:h_a_truth) and that for each fold the increment a(η̂_{n,k}, ·) − a(η₀,
·) is [jointly measurable in (ω, z)](hyp:hΔa_meas), [measurable with respect to the same
out-of-fold product σ-algebra](hyp:hΔa_uncurry_train), [square-integrable at every
realization](hyp:hΔa_memLp), [o_p(1) in L²](hyp:hΔa_rate), and [has a population mean that is
o_p(1)](hyp:hΔa_bias_rate). Assume also [z ↦ −J₀⁻¹·m(η₀, z, θ₀) is measurable](hyp:hψ_meas) and
[the rescaled oracle cross-fitted estimator is almost-everywhere measurable at every sample
size](hyp:hOracle_meas). Then [the feasible cross-fitted (DML2) estimator, minus the fold-averaged
empirical mean of b(η̂_{n,k}, ·) divided by the fold-averaged empirical mean of a(η̂_{n,k}, ·), is
asymptotically linear at θ₀ over the full sample with influence function −J₀⁻¹·m(η₀, z,
θ₀)](goal). -/
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
    (h_product_rate : ∀ k, IsLittleOp
      (fun n ω =>
        ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
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
  exact feasibleCrossFitLinearDML_isAsymLinear_on_highProbEvent M hMZ hFV sample
    hK_pos split η_hat (fun _ => Set.univ) (fun _ => 0) tendsto_const_nhds (by simp)
    (fun n k ω _ => hBR_at n k ω) h_m_meas h_m_train_uncurry
    (fun n k ω _ => h_m_int n k ω) (fun n k ω _ => h_m_sq_int n k ω)
    h_score_diff_rate h_product_rate h_a_truth hΔa_meas hΔa_uncurry_train
    (fun n k ω _ => hΔa_memLp n k ω) hΔa_rate hΔa_bias_rate hψ_meas hOracle_meas

/-- **Scalar DML2 specialization of Chernozhukov et al. (2018), Theorem 3.1, with nuisance
conditions on events of probability tending to one.** Take [a moment system whose score is
affine in the parameter,
m(η, z, θ) = a(η, z)·θ + b(η, z), with true nuisance η₀, true parameter θ₀, error gauges ρ₁ and
ρ₂, and linearization scale J₀ equal to the population mean of a(η₀, ·)](hyp:M), whose [score has
mean zero at the truth](hyp:hMZ) and [finite second moment at the truth](hyp:hFV). Let [an i.i.d.
sample](hyp:sample) be [split into K folds](hyp:split) with [K at least two](hyp:hK_pos), let
[η̂_{n,k} be the nuisance fit used on fold k at sample size n](hyp:η_hat), and let [G_n be
events](hyp:goodSet) whose [complements have probability at most Δ_n](hyp:hfail) for [a sequence
Δ_n](hyp:Δ) that [tends to zero](hyp:hΔ). Assume that for every n, every fold k and every
realization in G_n [the population moment of m(η̂_{n,k}, ·, θ₀) is bounded in absolute value by a
fixed constant times ρ₁(η̂_{n,k}, η₀)·ρ₂(η̂_{n,k}, η₀)](hyp:hBR_at) and m(η̂_{n,k}, ·, θ₀) is
[integrable](hyp:h_m_int) and [square-integrable](hyp:h_m_sq_int) under the observation law; that
[(ω, z) ↦ m(η̂_{n,k}(ω), z, θ₀) is jointly measurable](hyp:h_m_meas) and [is measurable with
respect to the product of the σ-algebra generated by the observations outside fold k and the
σ-algebra on the observation space](hyp:h_m_train_uncurry); that [for each fold the L² distance
between m(η̂_{n,k}, ·, θ₀) and m(η₀, ·, θ₀) is o_p(1)](hyp:h_score_diff_rate); and that [for each
fold the product ρ₁(η̂_{n,k}, η₀)·ρ₂(η̂_{n,k}, η₀) is o_p(n^(−1/2))](hyp:h_product_rate). For the
coefficient, assume [a(η₀, ·) is square-integrable](hyp:h_a_truth) and that for each fold the
increment a(η̂_{n,k}, ·) − a(η₀, ·) is [jointly measurable in (ω, z)](hyp:hΔa_meas), [measurable
with respect to the same out-of-fold product σ-algebra](hyp:hΔa_uncurry_train), [square-integrable
at every realization in G_n](hyp:hΔa_memLp), [o_p(1) in L²](hyp:hΔa_rate), and [has a population
mean that is o_p(1)](hyp:hΔa_bias_rate). Assume also [z ↦ −J₀⁻¹·m(η₀, z, θ₀) is
measurable](hyp:hψ_meas) and [the rescaled oracle cross-fitted estimator is almost-everywhere
measurable at every sample size](hyp:hOracle_meas). Let [σ be a real number](hyp:σ)
that [is positive](hyp:hσ_pos) and [whose square is the second moment of −J₀⁻¹·m(η₀, Z,
θ₀)](hyp:hσ_sq), and assume [√n times the estimation error of the feasible cross-fitted
estimator](hyp:hNum_meas) and [the same quantity divided by σ](hyp:hStud_meas) are
almost-everywhere measurable at every sample size. Then [√n times the error of the feasible
cross-fitted (DML2) estimator, divided by σ, converges in distribution to the standard normal
law](goal).

The nuisance conditions hold on events `G_n` of probability tending to one, matching the
nuisance-realization-set form of Assumption 3.2. This specialization does not formalize the
theorem's uniformity over expanding model classes, explicit remainder order,
root-sample-size concentration statement, vector case, or DML1 result. -/
theorem feasibleCrossFitLinearDML_tendstoStandardNormal_on_highProbEvent
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : LinearMoment Ω μ Z P_Z H)
    (hMZ : MeanZero M.toGeneralMoment)
    (hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (goodSet : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, μ (goodSet n)ᶜ ≤ Δ n) {Crem : ℝ}
    (hBR_at : ∀ n k ω, ω ∈ goodSet n →
      |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (h_m_meas : ∀ n k, Measurable
      (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (fun p : Ω × Z => M.m (η_hat n k p.1) p.2 M.θ₀))
    (h_m_int : ∀ n k ω, ω ∈ goodSet n →
      Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (h_m_sq_int : ∀ n k ω, ω ∈ goodSet n →
      Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (h_score_diff_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
        2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (h_product_rate : ∀ k, IsLittleOp
      (fun n ω =>
        ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_uncurry_train : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
    (hΔa_memLp : ∀ n k ω, ω ∈ goodSet n →
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
    Modes.TendstoInLaw (fun _ : ℕ => μ) (fun n ω =>
      IsAsymLinear.rescaledEstimator
        (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
        (fun n => Finset.range n) n ω / σ) atTop (gaussianMeasure 0 1) := by
  have hAL := feasibleCrossFitLinearDML_isAsymLinear_on_highProbEvent M hMZ hFV sample
    hK_pos split η_hat goodSet Δ hΔ hfail hBR_at h_m_meas h_m_train_uncurry
    h_m_int h_m_sq_int h_score_diff_rate
    h_product_rate h_a_truth hΔa_meas hΔa_uncurry_train
    hΔa_memLp hΔa_rate hΔa_bias_rate hψ_meas hOracle_meas
  exact feasibleCrossFitLinearDML_tendstoStandardNormal_of_isAsymLinear
    M sample split η_hat hAL hψ_meas σ hσ_pos hσ_sq hNum_meas hStud_meas

/-- **Pointwise scalar DML2 specialization of Chernozhukov et al. (2018), Theorem 3.1.** Take [a
moment system whose score is affine in the parameter, m(η, z, θ) = a(η, z)·θ + b(η, z), with true
nuisance η₀, true parameter θ₀, error gauges ρ₁ and ρ₂, and linearization scale J₀ equal to the
population mean of a(η₀, ·)](hyp:M), whose [score has mean zero at the truth](hyp:hMZ) and [finite
second moment at the truth](hyp:hFV). Let [an i.i.d. sample](hyp:sample) be [split into K
folds](hyp:split) with [K at least two](hyp:hK_pos), and let [η̂_{n,k} be the nuisance fit used on
fold k at sample size n](hyp:η_hat). Assume that for every n, every fold k and every realization
[the population moment of m(η̂_{n,k}, ·, θ₀) is bounded in absolute value by a fixed constant
times ρ₁(η̂_{n,k}, η₀)·ρ₂(η̂_{n,k}, η₀)](hyp:hBR_at) and m(η̂_{n,k}, ·, θ₀) is
[integrable](hyp:h_m_int) and [square-integrable](hyp:h_m_sq_int) under the observation law; that
[(ω, z) ↦ m(η̂_{n,k}(ω), z, θ₀) is jointly measurable](hyp:h_m_meas) and [is measurable with
respect to the product of the σ-algebra generated by the observations outside fold k and the
σ-algebra on the observation space](hyp:h_m_train_uncurry); that [for each fold the L² distance
between m(η̂_{n,k}, ·, θ₀) and m(η₀, ·, θ₀) is o_p(1)](hyp:h_score_diff_rate); and that [for each
fold the product ρ₁(η̂_{n,k}, η₀)·ρ₂(η̂_{n,k}, η₀) is o_p(n^(−1/2))](hyp:h_product_rate). For the
coefficient, assume [a(η₀, ·) is square-integrable](hyp:h_a_truth) and that for each fold the
increment a(η̂_{n,k}, ·) − a(η₀, ·) is [jointly measurable in (ω, z)](hyp:hΔa_meas), [measurable
with respect to the same out-of-fold product σ-algebra](hyp:hΔa_uncurry_train), [square-integrable
at every realization](hyp:hΔa_memLp), [o_p(1) in L²](hyp:hΔa_rate), and [has a population mean
that is o_p(1)](hyp:hΔa_bias_rate). Assume also [z ↦ −J₀⁻¹·m(η₀, z, θ₀) is
measurable](hyp:hψ_meas) and [the rescaled oracle cross-fitted estimator is almost-everywhere
measurable at every sample size](hyp:hOracle_meas). Let [σ be a real number](hyp:σ) that [is
positive](hyp:hσ_pos) and [whose square is the second moment of −J₀⁻¹·m(η₀, Z, θ₀)](hyp:hσ_sq),
and assume [√n times the estimation error of the feasible cross-fitted estimator](hyp:hNum_meas)
and [the same quantity divided by σ](hyp:hStud_meas) are almost-everywhere measurable at every
sample size. Then [√n times the error of the feasible cross-fitted (DML2) estimator, divided by σ,
converges in distribution to the standard normal law](goal).

This specialization does not formalize the theorem's uniformity over expanding
model classes, explicit remainder order, root-sample-size concentration
statement, vector case, or DML1 result. -/
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
    (h_product_rate : ∀ k, IsLittleOp
      (fun n ω =>
        ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (h_a_truth : MemLp (M.m_a M.η₀) 2 P_Z)
    (hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)))
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
    Modes.TendstoInLaw (fun _ : ℕ => μ) (fun n ω =>
      IsAsymLinear.rescaledEstimator
        (feasibleCrossFitLinearDML M sample split η_hat) M.θ₀
        (fun n => Finset.range n) n ω / σ) atTop (gaussianMeasure 0 1) := by
  exact feasibleCrossFitLinearDML_tendstoStandardNormal_on_highProbEvent M hMZ hFV sample
    hK_pos split η_hat (fun _ => Set.univ) (fun _ => 0) tendsto_const_nhds (by simp)
    (fun n k ω _ => hBR_at n k ω) h_m_meas h_m_train_uncurry
    (fun n k ω _ => h_m_int n k ω) (fun n k ω _ => h_m_sq_int n k ω)
    h_score_diff_rate h_product_rate h_a_truth hΔa_meas hΔa_uncurry_train
    (fun n k ω _ => hΔa_memLp n k ω) hΔa_rate hΔa_bias_rate hψ_meas hOracle_meas
    σ hσ_pos hσ_sq hNum_meas hStud_meas

end OrthogonalMoments
end Estimation
end Causalean
