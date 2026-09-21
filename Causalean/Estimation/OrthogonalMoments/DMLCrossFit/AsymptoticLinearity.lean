/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# K-fold cross-fitted Chernozhukov DML

K-fold version of the one-shot asymptotic-linearity interfaces from
`Estimation/OrthogonalMoments/DMLChernozhukov.lean`.  Each evaluation fold k uses a
nuisance estimator `η̂^{(-k)}` trained on the complement; the K fold scores
are averaged to form the final estimator.

Reference: Chernozhukov et al. (2018), §3.2 (DML2).
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.Estimator
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.Helpers

/-! # Cross-Fitted Double Machine Learning

This file proves the K-fold analogue of the Chernozhukov-form DML theorem.
The estimator `crossFitOneStepOracleDML` evaluates each fold with a nuisance
learner trained on the complementary data and averages the fold scores. The
main theorem `crossFitOneStepOracleDML_isAsymLinear_of_goodSet` shows asymptotic linearity with
influence function `-linScale⁻¹ · m(η₀, ·, θ₀)` under the same mean-zero,
finite-variance, score-difference, individual-rate, and product-rate
hypotheses as the one-shot theorem, but imposed fold by fold. -/

public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]
/-- **Asymptotic linearity of the K-fold cross-fitted Chernozhukov DML estimator.** This has
the same Chernozhukov form as `oneStepOracleDML_isAsymLinear_of_goodSet`, but with K folds. Given a
general moment M with mean zero at the truth, assume [the truth-evaluated score is
square-integrable (finite variance)](hyp:_hFV), that [there are at least two folds,
`K > 1`](hyp:_hK_pos), and a sequence of per-fold cross-fitted nuisance estimators η̂.
Suppose [the population moment at η̂, trained on each fold's complement, is bounded by a
constant times the product of the two bilinear-remainder seminorms, at every fold count,
fold index, and sample point](hyp:_hBR_at). Assume the technical regularity package that
[the moment at η̂ is jointly measurable at every fold](hyp:_h_m_meas),
[uncurried product-measurable with respect to the fold's training
complement](hyp:_h_m_train_uncurry), and is accompanied by [a curried
training-complement witness retained for compatibility](hyp:_h_m_train). At every fold
count, fold index, and
sample point, [integrable](hyp:_h_m_int) and [square-integrable](hyp:_h_m_sq_int).
Finally suppose that, at every fold, [the L² score difference between the fold's
estimated and true nuisance is o_P(1)](hyp:_h_score_diff_rate), [each individual
nuisance-error rate is o_P(1), as retained compatibility
data](hyp:_h_indiv_rate_ρ₁,_h_indiv_rate_ρ₂), and
[their product decays at the parametric rate `o_P(n^{-1/2})`](hyp:_h_product_rate). Then
[the K-fold cross-fitted estimator is asymptotically linear at the truth `M.θ₀` with
influence function `−linScale⁻¹ · m(η₀, ·, θ₀)`, indexed over the full sample
(the fold-level
sub-aggregations sum to a full-sample average asymptotically)](goal).

The proof uses the uncurried measurability witness and the product rate; it does not use
the separate curried witness or either individual nuisance rate. -/
private theorem crossFitOneStepOracleDML_isAsymLinear_on_highProbEvent
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (_hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (goodSet : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (_hΔ : Tendsto Δ atTop (𝓝 0))
    (_hfail : ∀ n, μ (goodSet n)ᶜ ≤ Δ n)
    {Crem : ℝ}
    (_hBR_at :
      ∀ n k ω, ω ∈ goodSet n →
        |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
          Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
                 ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas :
      ∀ n k, Measurable (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_train :
      ∀ n k,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
          (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (_h_m_train_uncurry :
      ∀ n k,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_int :
      ∀ n k ω, ω ∈ goodSet n →
        Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (_h_m_sq_int :
      ∀ n k ω, ω ∈ goodSet n →
        Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate :
      ∀ k, IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₁ :
      ∀ k, IsLittleOp
        (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₂ :
      ∀ k, IsLittleOp
        (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) μ)
    (_h_product_rate :
      ∀ k, IsLittleOp
        (fun n ω =>
          ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (crossFitOneStepOracleDML M sample split η_hat)
      M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample
      (fun n => Finset.range n) := by
  classical
  let ψ₀ : Z → ℝ := fun z => M.m M.η₀ z M.θ₀
  have hMZ_int : ∫ z, ψ₀ z ∂P_Z = 0 := _hMZ
  refine ⟨?_, ?_, ?_⟩
  · -- Mean zero: multiply `MeanZero M` by the fixed inverse scale.
    show ∫ z, -M.linScaleInv * M.m M.η₀ z M.θ₀ ∂P_Z = 0
    calc
      ∫ z, -M.linScaleInv * M.m M.η₀ z M.θ₀ ∂P_Z
          = -M.linScaleInv * ∫ z, ψ₀ z ∂P_Z := by
            simp only [ψ₀, neg_mul, integral_neg, integral_const_mul]
      _ = 0 := by rw [hMZ_int]; ring
  · -- Finite variance: fixed scalar multiplication preserves square
    -- integrability of the Chernozhukov score.
    show Integrable (fun z => (-M.linScaleInv * M.m M.η₀ z M.θ₀) ^ 2) P_Z
    have h_eq : ∀ z,
        (-M.linScaleInv * M.m M.η₀ z M.θ₀) ^ 2 =
          M.linScaleInv ^ 2 * (M.m M.η₀ z M.θ₀) ^ 2 := by
      intro z; ring
    simp_rw [h_eq]
    exact _hFV.const_mul (M.linScaleInv ^ 2)
  · -- Remainder: separate the K-fold reduction into the
    -- stochastic fold terms, the population bias terms, and the final
    -- full-sample reweighting from fold averages.
    let foldScoreDiff : ℕ → Fin K → Ω → Z → ℝ := fun n k ω z =>
      M.m (η_hat n k ω) z M.θ₀ - ψ₀ z
    let foldCentered : ℕ → Fin K → Ω → ℝ := fun n k ω =>
      (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k,
          (foldScoreDiff n k ω (sample.Z i ω) -
            ∫ z, foldScoreDiff n k ω z ∂P_Z)
    let foldBias : ℕ → Fin K → Ω → ℝ := fun n k ω =>
      Real.sqrt ((split.fold n k).card : ℝ) *
        ∫ z, foldScoreDiff n k ω z ∂P_Z
    haveI : IsProbabilityMeasure P_Z := by
      rw [← sample.law]
      exact Measure.isProbabilityMeasure_map (sample.meas 0).aemeasurable
    have htruth_L2 : MemLp (fun z => M.m M.η₀ z M.θ₀) 2 P_Z :=
      (memLp_two_iff_integrable_sq
        (M.m_meas M.η₀ M.θ₀).aestronglyMeasurable).2 _hFV
    have h_fold_centered :
        ∀ k, IsLittleOp (fun n ω => foldCentered n k ω) (fun _ => (1 : ℝ)) μ := by
      intro k
      let f : ℕ → Ω → Z → ℝ := fun n ω z =>
        M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀
      have hf_meas : ∀ n, Measurable (Function.uncurry (f n)) := by
        intro n
        change Measurable (fun p : Ω × Z =>
          M.m (η_hat n k p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
        exact (_h_m_meas n k).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
      have hf_train :
          ∀ n,
            Measurable[MeasurableSpace.comap
              (fun ω (i : split.trainComplement n k) => sample.Z i ω)
              inferInstance]
              (fun ω => f n ω) := by
        intro n
        change Measurable[MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance]
          (fun ω z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
        exact (_h_m_train n k).sub measurable_const
      have hf_uncurry_train :
          ∀ n,
            Measurable[(MeasurableSpace.comap
                (fun ω (i : split.trainComplement n k) => sample.Z i ω)
                inferInstance).prod
              (inferInstance : MeasurableSpace Z)]
              (Function.uncurry (f n)) := by
        intro n
        change Measurable[(MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun p : Ω × Z =>
            M.m (η_hat n k p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
        exact (_h_m_train_uncurry n k).sub
          ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
      have hf_memLp : ∀ n ω, ω ∈ goodSet n → MemLp (f n ω) 2 P_Z := by
        intro n ω hω
        have hsq := _h_m_sq_int n k ω hω
        have hrand_L2 : MemLp (fun z => M.m (η_hat n k ω) z M.θ₀) 2 P_Z :=
          (memLp_two_iff_integrable_sq
            (M.m_meas (η_hat n k ω) M.θ₀).aestronglyMeasurable).2
              hsq
        simp only [f]
        exact hrand_L2.sub htruth_L2
      have hf_rate_one :
          IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P_Z).toReal)
            (fun _ => (1 : ℝ)) μ := by
        simpa [f] using _h_score_diff_rate k
      simpa [foldCentered, foldScoreDiff, ψ₀, f] using
        KFoldSplit.fold_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent
          sample split k f goodSet Δ _hΔ _hfail hf_meas hf_uncurry_train
          hf_memLp hf_rate_one
    have h_fold_bias :
        ∀ k, IsLittleOp (fun n ω => foldBias n k ω) (fun _ => (1 : ℝ)) μ := by
      intro k
      let f : ℕ → Ω → Z → ℝ := fun n ω z =>
        M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀
      have hf_meas : ∀ n, Measurable (Function.uncurry (f n)) := by
        intro n
        change Measurable (fun p : Ω × Z =>
          M.m (η_hat n k p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
        exact (_h_m_meas n k).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
      have hf_memLp : ∀ n ω, ω ∈ goodSet n → MemLp (f n ω) 2 P_Z := by
        intro n ω hω
        have hsq := _h_m_sq_int n k ω hω
        have hrand_L2 : MemLp (fun z => M.m (η_hat n k ω) z M.θ₀) 2 P_Z :=
          (memLp_two_iff_integrable_sq
            (M.m_meas (η_hat n k ω) M.θ₀).aestronglyMeasurable).2
              hsq
        simp only [f]
        exact hrand_L2.sub htruth_L2
      have h_int_eq : ∀ n ω, ω ∈ goodSet n →
          ∫ z, f n ω z ∂P_Z =
            ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z := by
        intro n ω hω
        have hf_L2 := hf_memLp n ω hω
        have hm_int := _h_m_int n k ω hω
        have hf_int : Integrable (f n ω) P_Z :=
          hf_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
        have htruth_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z :=
          htruth_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
        have hzero : (∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) = 0 := by
          simpa [MeanZero] using _hMZ
        calc
          ∫ z, f n ω z ∂P_Z =
              ∫ z, (M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) ∂P_Z := by rfl
          _ = ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z -
              ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z :=
            integral_sub hm_int htruth_int
          _ = ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z := by
            rw [hzero]
            ring
      let mGood : ℕ → Ω → ℝ := fun n ω =>
        if ω ∈ goodSet n then ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z else 0
      have h_int_good_rate :
          IsLittleOp mGood
            (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
        intro ε hε
        rw [ENNReal.tendsto_nhds_zero]
        intro δ hδ
        let Kc : ℝ := |Crem| + 1
        have hKpos : 0 < Kc := by
          dsimp [Kc]
          linarith [abs_nonneg Crem]
        have htarget := (ENNReal.tendsto_nhds_zero.mp
          (_h_product_rate k (ε / Kc) (div_pos hε hKpos))) δ hδ
        filter_upwards [htarget, eventually_ge_atTop (1 : ℕ)] with n hn hn_one
        exact (measure_mono (by
          intro ω hω
          change ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ ‖mGood n ω‖ at hω
          by_cases hgood : ω ∈ goodSet n
          · have hbr := _hBR_at n k ω hgood
            rw [show mGood n ω = ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z by
              simp [mGood, hgood]] at hω
            rw [Real.norm_eq_abs] at hω
            let prodρ : ℝ :=
              ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
                ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ)
            have hprod_nonneg : 0 ≤ prodρ := by
              dsimp [prodρ]
              exact mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
            have hbr0 :
                |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤ Crem * prodρ := by
              simpa [prodρ, mul_assoc] using hbr
            have hle_abs :
                |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤ |Crem| * prodρ :=
              hbr0.trans (mul_le_mul_of_nonneg_right (le_abs_self Crem) hprod_nonneg)
            have hKbound :
                |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤ Kc * prodρ := by
              refine hle_abs.trans ?_
              exact mul_le_mul_of_nonneg_right (by dsimp [Kc]; linarith) hprod_nonneg
            have hthreshold_le_bound :
                ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Kc * prodρ :=
              hω.trans hKbound
            have hdiv_le :
                (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / Kc ≤ prodρ := by
              rw [div_le_iff₀ hKpos]
              simpa [mul_comm, mul_left_comm, mul_assoc] using hthreshold_le_bound
            have hsmall :
                (ε / Kc) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ |prodρ| := by
              have hdiv_eq :
                  (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / Kc =
                    (ε / Kc) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
                ring
              rw [← hdiv_eq]
              simpa [abs_of_nonneg hprod_nonneg] using hdiv_le
            exact hsmall
          · have hn_pos : 0 < (n : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
            have hthreshold_pos :
                0 < ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) :=
              mul_pos hε (Real.rpow_pos_of_pos hn_pos _)
            exact False.elim ((not_le_of_gt hthreshold_pos) (by
                simpa [mGood, hgood, Real.norm_eq_abs] using hω))
          )).trans hn
      have h_int_raw_rate :
          IsLittleOp (fun n ω => ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z)
            (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
        apply isLittleOp_of_isLittleOp_on_highProbEvent
          (Xn := fun n ω => ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z)
          (Yn := mGood) goodSet Δ _hΔ _hfail
        · intro n ω hω
          rw [show mGood n ω = ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z by
            simp [mGood, hω]]
        · exact h_int_good_rate
      have h_int_rate :
          IsLittleOp (fun n ω => ∫ z, f n ω z ∂P_Z)
            (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
        apply isLittleOp_of_isLittleOp_on_highProbEvent
          (Xn := fun n ω => ∫ z, f n ω z ∂P_Z)
          (Yn := fun n ω => ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z)
          goodSet Δ _hΔ _hfail
        · exact h_int_eq
        · exact h_int_raw_rate
      -- Inline bias bound: mirrors OneShot's `hB` (lines 302-367) with
      -- `split.foldB n` replaced by `split.fold n k` and the ratio limit
      -- `c` replaced by `K⁻¹` (from `split.ratio k`).
      have hK_pos_real : 0 < (K : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hK_pos.le)
      have hK_one_lt_real : (1 : ℝ) < (K : ℝ) := by exact_mod_cast _hK_pos
      have hc_pos : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hK_pos_real
      have hc_lt : (K : ℝ)⁻¹ < 1 := by
        rw [inv_lt_one_iff₀]
        exact Or.inr hK_one_lt_real
      have h_split_rate := split.ratio k
      have hbias :
          IsLittleOp (fun n ω => foldBias n k ω) (fun _ => (1 : ℝ)) μ := by
        intro ε' hε'
        rw [ENNReal.tendsto_nhds_zero]
        intro δ hδ
        let C : ℝ := Real.sqrt ((K : ℝ)⁻¹) + 1
        have hCpos : 0 < C := by
          dsimp [C]
          linarith [Real.sqrt_nonneg ((K : ℝ)⁻¹)]
        have hCnonneg : 0 ≤ C := le_of_lt hCpos
        have hC2 : (K : ℝ)⁻¹ < C ^ 2 := by
          dsimp [C]
          nlinarith [Real.sq_sqrt (le_of_lt hc_pos),
            Real.sqrt_nonneg ((K : ℝ)⁻¹)]
        have hratio_event :
            ∀ᶠ n in atTop, ((split.fold n k).card : ℝ) / n < C ^ 2 :=
          h_split_rate.eventually_lt_const hC2
        have hn_event : ∀ᶠ n : ℕ in atTop, n ≠ 0 := eventually_ne_atTop 0
        have hint_event := (ENNReal.tendsto_nhds_zero.mp
          (h_int_rate (ε' / C) (div_pos hε' hCpos))) δ hδ
        filter_upwards [hratio_event, hn_event, hint_event]
          with n hratio hn_ne hn
        refine (measure_mono ?_).trans hn
        intro ω hω
        have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn_ne
        have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
        have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
        have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
        have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrtn_pos
        have hcard_le : ((split.fold n k).card : ℝ) ≤ C ^ 2 * (n : ℝ) := by
          have hlt : ((split.fold n k).card : ℝ) < C ^ 2 * (n : ℝ) := by
            field_simp [hn_pos.ne'] at hratio ⊢
            nlinarith
          exact le_of_lt hlt
        have hsqrt_le :
            Real.sqrt ((split.fold n k).card : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
          calc
            Real.sqrt ((split.fold n k).card : ℝ) ≤ Real.sqrt (C ^ 2 * (n : ℝ)) :=
              Real.sqrt_le_sqrt hcard_le
            _ = Real.sqrt (C ^ 2) * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_mul (sq_nonneg C)]
            _ = C * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_sq hCnonneg]
        have hsqrtcard_nonneg : 0 ≤ Real.sqrt ((split.fold n k).card : ℝ) :=
          Real.sqrt_nonneg _
        have hthreshold_le_prod :
            ε' ≤ Real.sqrt ((split.fold n k).card : ℝ) *
              |∫ z, f n ω z ∂P_Z| := by
          simpa [foldBias, foldScoreDiff, ψ₀, f, abs_mul,
            abs_of_nonneg hsqrtcard_nonneg] using hω
        have hle_prod :
            Real.sqrt ((split.fold n k).card : ℝ) * |∫ z, f n ω z ∂P_Z| ≤
              (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| :=
          mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
        have hthreshold_le_bound :
            ε' ≤ (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| :=
          hthreshold_le_prod.trans hle_prod
        have hrn_eq : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
          rw [Real.rpow_neg hn_nonneg]
          rw [← Real.sqrt_eq_rpow]
        have hdiv_le :
            ε' / (C * Real.sqrt (n : ℝ)) ≤ |∫ z, f n ω z ∂P_Z| := by
          rw [div_le_iff₀ (mul_pos hCpos hsqrtn_pos)]
          nlinarith [hthreshold_le_bound]
        have hsmall :
            (ε' / C) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
              |∫ z, f n ω z ∂P_Z| := by
          rw [hrn_eq]
          convert hdiv_le using 1
          field_simp [hCpos.ne', hsqrtn_pos.ne']
        exact hsmall
      exact hbias
    -- Prerequisites for the K-fold algebra (used by the helpers below).
    have hK_pos_real : 0 < (K : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hK_pos.le)
    have hK_one_lt_real : (1 : ℝ) < (K : ℝ) := by exact_mod_cast _hK_pos
    have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt hK_pos_real
    have hK_inv_pos : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hK_pos_real
    have hψ_meas_glob : Measurable ψ₀ := M.m_meas M.η₀ M.θ₀
    -- Reusable O_p(1) helper for `(1/√n) Σ_{fold n k} ψ₀(Z_i)`.
    have _hfoldNormPsi_isBigOp : ∀ k : Fin K,
        IsBigOp
          (fun n ω => (Real.sqrt (n : ℝ))⁻¹ *
              ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω))
          (fun _ => (1 : ℝ)) μ := by
      intro k
      exact foldNormalizedSumOverN_isBigOp sample ψ₀ hψ_meas_glob hMZ_int _hFV
        split k
    -- ## Final algebraic decomposition.
    --
    -- After unfolding `crossFitOneStepOracleDML` and using `cover` + `partition` to
    -- rewrite `∑_{i ∈ range n} ψ₀(Z_i) = ∑_k ∑_{i ∈ fold n k} ψ₀(Z_i)`, the
    -- residual factorises as
    --   R_n = -linScale⁻¹ · ∑_{k : Fin K} D_k(n, ω)
    -- where each `D_k(n, ω)` decomposes as a sum of:
    --   ratio_piece_k = (n / (K · |fold n k|) - 1) · (1/√n) · ∑_{fold n k} ψ₀,
    --   score_piece_k = (1/K) · (√n / √|fold n k|) ·
    --                     (foldCentered n k ω + foldBias n k ω).
    -- `ratio_piece_k` is `o_p(1)` via `IsBigOp.const_mul_tendsto_zero`
    --   (deterministic factor → 0, stochastic factor `O_p(1)` from
    --   `_hfoldNormPsi_isBigOp k`).
    -- `score_piece_k` is `o_p(1)` via `IsBigOp.mul_isLittleOp_one_isLittleOp`
    --   (deterministic factor `√n/√|fold n k| → √K` is `O_p(1)`,
    --   `foldCentered + foldBias` is `o_p(1)` from `h_fold_centered`,
    --   `h_fold_bias`).
    -- Sum K copies of `o_p(1)` and multiply by the fixed inverse scale.
    -- gives the desired `o_p(1)`.
    have h_full_reweighting :
        IsLittleOp
          (fun n ω =>
            Real.sqrt ((Finset.range n).card : ℝ) *
                (crossFitOneStepOracleDML M sample split η_hat n ω - M.θ₀) -
              (Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
                ∑ i ∈ Finset.range n,
                  (-M.linScaleInv * M.m M.η₀ (sample.Z i ω) M.θ₀))
          (fun _ => (1 : ℝ)) μ := by
      classical
      let ratioRaw : Fin K → ℕ → Ω → ℝ := fun k n ω =>
        Real.sqrt (n : ℝ) * (K : ℝ)⁻¹ *
            (((split.fold n k).card : ℝ)⁻¹ *
              ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)) -
          (Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)
      let scoreRaw : Fin K → ℕ → Ω → ℝ := fun k n ω =>
        Real.sqrt (n : ℝ) * (K : ℝ)⁻¹ *
          (((split.fold n k).card : ℝ)⁻¹ *
            ∑ i ∈ split.fold n k,
              foldScoreDiff n k ω (sample.Z i ω))
      let ratioLimit : Fin K → ℕ → ℝ := fun k n =>
        (n : ℝ) / ((K : ℝ) * ((split.fold n k).card : ℝ)) - 1
      let scoreScale : Fin K → ℕ → ℝ := fun k n =>
        (K : ℝ)⁻¹ *
          Real.sqrt ((n : ℝ) / ((split.fold n k).card : ℝ))
      have hratio_limit :
          ∀ k : Fin K, Tendsto (ratioLimit k) atTop (𝓝 0) := by
        intro k
        have h_n_over_card :
            Tendsto
              (fun n : ℕ => (n : ℝ) / ((split.fold n k).card : ℝ))
              atTop (𝓝 (K : ℝ)) := by
          have h_inv :
              Tendsto
                (fun n : ℕ =>
                  (((split.fold n k).card : ℝ) / (n : ℝ))⁻¹)
                atTop (𝓝 (K : ℝ)) := by
            have hlim_ne : ((K : ℝ)⁻¹) ≠ 0 := inv_ne_zero hK_ne
            have h := (split.ratio k).inv₀ hlim_ne
            simpa [inv_inv] using h
          refine h_inv.congr' ?_
          filter_upwards [eventually_ne_atTop 0,
            (split.grow k).eventually_gt_atTop 0] with n hn hcard
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have hcR : ((split.fold n k).card : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hcard)
          field_simp [hnR, hcR]
        have h_scaled :
            Tendsto
              (fun n : ℕ =>
                ((K : ℝ)⁻¹) *
                  ((n : ℝ) / ((split.fold n k).card : ℝ)))
              atTop (𝓝 1) := by
          have := Tendsto.const_mul ((K : ℝ)⁻¹) h_n_over_card
          simpa [hK_ne] using this
        have h_sub :
            Tendsto
              (fun n : ℕ =>
                ((K : ℝ)⁻¹) *
                    ((n : ℝ) / ((split.fold n k).card : ℝ)) - 1)
              atTop (𝓝 (1 - 1)) :=
          h_scaled.sub (tendsto_const_nhds (x := (1 : ℝ)))
        simpa [ratioLimit, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc]
          using h_sub
      have hratio_raw :
          ∀ k : Fin K, IsLittleOp (ratioRaw k) (fun _ => (1 : ℝ)) μ := by
        intro k
        have hcanonical :
            IsLittleOp
              (fun n ω =>
                ratioLimit k n *
                  ((Real.sqrt (n : ℝ))⁻¹ *
                    ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)))
              (fun _ => (1 : ℝ)) μ :=
          IsBigOp.const_mul_tendsto_zero (_hfoldNormPsi_isBigOp k)
            (hratio_limit k)
        refine IsLittleOp_congr_eventually hcanonical ?_
        filter_upwards [eventually_ne_atTop 0,
          (split.grow k).eventually_gt_atTop 0] with n hn hcard ω
        have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn)
        have hcard_pos : 0 < ((split.fold n k).card : ℝ) := by
          exact_mod_cast hcard
        have hsqrtn_sq :
            Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt hn_pos.le
        have hsqrtn_pow : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := by
          rw [sq, hsqrtn_sq]
        unfold ratioRaw ratioLimit
        field_simp [hK_ne, hn_pos.ne', hcard_pos.ne',
          (Real.sqrt_pos.mpr hn_pos).ne', hsqrtn_sq]
        rw [hsqrtn_pow]
      have hscore_scale_limit :
          ∀ k : Fin K, Tendsto (scoreScale k) atTop
            (𝓝 ((K : ℝ)⁻¹ * Real.sqrt (K : ℝ))) := by
        intro k
        have h_n_over_card :
            Tendsto
              (fun n : ℕ => (n : ℝ) / ((split.fold n k).card : ℝ))
              atTop (𝓝 (K : ℝ)) := by
          have h_inv :
              Tendsto
                (fun n : ℕ =>
                  (((split.fold n k).card : ℝ) / (n : ℝ))⁻¹)
                atTop (𝓝 (K : ℝ)) := by
            have hlim_ne : ((K : ℝ)⁻¹) ≠ 0 := inv_ne_zero hK_ne
            have h := (split.ratio k).inv₀ hlim_ne
            simpa [inv_inv] using h
          refine h_inv.congr' ?_
          filter_upwards [eventually_ne_atTop 0,
            (split.grow k).eventually_gt_atTop 0] with n hn hcard
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have hcR : ((split.fold n k).card : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hcard)
          field_simp [hnR, hcR]
        have hsqrt :
            Tendsto
              (fun n : ℕ =>
                Real.sqrt ((n : ℝ) / ((split.fold n k).card : ℝ)))
              atTop (𝓝 (Real.sqrt (K : ℝ))) :=
          (Real.continuous_sqrt.tendsto (K : ℝ)).comp h_n_over_card
        have hscaled := Tendsto.const_mul ((K : ℝ)⁻¹) hsqrt
        simpa [scoreScale] using hscaled
      have hscore_raw :
          ∀ k : Fin K, IsLittleOp (scoreRaw k) (fun _ => (1 : ℝ)) μ := by
        intro k
        have hdet :
            IsBigOp (fun n (_ : Ω) => scoreScale k n)
              (fun _ => (1 : ℝ)) μ :=
          deterministic_tendsto_isBigOp (μ := μ) (hscore_scale_limit k)
        have hcenter_bias :
            IsLittleOp
              (fun n ω => foldCentered n k ω + foldBias n k ω)
              (fun _ => (1 : ℝ)) μ :=
          IsLittleOp_add_one (h_fold_centered k) (h_fold_bias k)
        have hcanonical :
            IsLittleOp
              (fun n ω =>
                scoreScale k n *
                  (foldCentered n k ω + foldBias n k ω))
              (fun _ => (1 : ℝ)) μ :=
          IsBigOp.mul_isLittleOp_one_isLittleOp hdet hcenter_bias
        refine IsLittleOp_congr_eventually hcanonical ?_
        filter_upwards [eventually_ne_atTop 0,
          (split.grow k).eventually_gt_atTop 0] with n hn hcard ω
        have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn)
        have hcard_pos : 0 < ((split.fold n k).card : ℝ) := by
          exact_mod_cast hcard
        have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
        have hsqrtc_pos : 0 < Real.sqrt ((split.fold n k).card : ℝ) :=
          Real.sqrt_pos.mpr hcard_pos
        have hsqrt_div :
            Real.sqrt ((n : ℝ) / ((split.fold n k).card : ℝ)) =
              Real.sqrt (n : ℝ) /
                Real.sqrt ((split.fold n k).card : ℝ) := by
          rw [Real.sqrt_div hn_pos.le]
        have hsqrtc_sq :
            Real.sqrt ((split.fold n k).card : ℝ) *
                Real.sqrt ((split.fold n k).card : ℝ) =
              ((split.fold n k).card : ℝ) :=
          Real.mul_self_sqrt hcard_pos.le
        have hsqrtc_pow :
            Real.sqrt ((split.fold n k).card : ℝ) ^ 2 =
              ((split.fold n k).card : ℝ) := by
          rw [sq, hsqrtc_sq]
        have hsum_center :
            ∑ i ∈ split.fold n k,
                (foldScoreDiff n k ω (sample.Z i ω) -
                  ∫ z, foldScoreDiff n k ω z ∂P_Z) =
              ∑ i ∈ split.fold n k,
                  foldScoreDiff n k ω (sample.Z i ω) -
                ((split.fold n k).card : ℝ) *
                  ∫ z, foldScoreDiff n k ω z ∂P_Z := by
          simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        unfold scoreRaw scoreScale foldCentered foldBias
        rw [hsum_center, hsqrt_div]
        field_simp [hK_ne, hcard_pos.ne', hsqrtn_pos.ne', hsqrtc_pos.ne',
          hsqrtc_sq]
        rw [hsqrtc_pow]
        ring
      have hfold_piece :
          ∀ k : Fin K,
            IsLittleOp
              (fun n ω => ratioRaw k n ω + scoreRaw k n ω)
              (fun _ => (1 : ℝ)) μ := by
        intro k
        exact IsLittleOp_add_one (hratio_raw k) (hscore_raw k)
      have hsum_pieces :
          IsLittleOp
            (fun n ω =>
              ∑ k : Fin K, (ratioRaw k n ω + scoreRaw k n ω))
            (fun _ => (1 : ℝ)) μ := by
        simpa using
          IsLittleOp_finset_sum_one (Finset.univ : Finset (Fin K))
            (fun k n ω => ratioRaw k n ω + scoreRaw k n ω)
            (by intro k hk; exact hfold_piece k)
      have hdecomp :
          (fun n ω =>
            Real.sqrt ((Finset.range n).card : ℝ) *
                (crossFitOneStepOracleDML M sample split η_hat n ω - M.θ₀) -
              (Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
                ∑ i ∈ Finset.range n,
                  (-M.linScaleInv * M.m M.η₀ (sample.Z i ω) M.θ₀))
          =
          (fun n ω =>
            -M.linScaleInv *
              ∑ k : Fin K, (ratioRaw k n ω + scoreRaw k n ω)) := by
        funext n ω
        have hif_sum :
            (∑ i ∈ Finset.range n,
                -M.linScaleInv * M.m M.η₀ (sample.Z i ω) M.θ₀) =
              ∑ k : Fin K,
                -M.linScaleInv *
                  ∑ i ∈ split.fold n k,
                    M.m M.η₀ (sample.Z i ω) M.θ₀ := by
          calc
            (∑ i ∈ Finset.range n,
                -M.linScaleInv * M.m M.η₀ (sample.Z i ω) M.θ₀)
                =
              ∑ k : Fin K, ∑ i ∈ split.fold n k,
                -M.linScaleInv * M.m M.η₀ (sample.Z i ω) M.θ₀ := by
                rw [← split.cover n]
                rw [Finset.sum_biUnion]
                intro k hk l hl hkl
                exact split.partition n k l hkl
            _ =
              ∑ k : Fin K,
                -M.linScaleInv *
                  ∑ i ∈ split.fold n k,
                    M.m M.η₀ (sample.Z i ω) M.θ₀ := by
                simp_rw [← Finset.mul_sum]
        have hscore_decomp : ∀ k : Fin K,
            (∑ i ∈ split.fold n k,
              M.m (η_hat n k ω) (sample.Z i ω) M.θ₀) =
              (∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)) +
                ∑ i ∈ split.fold n k,
                  foldScoreDiff n k ω (sample.Z i ω) := by
          intro k
          unfold foldScoreDiff
          simp [Finset.sum_sub_distrib, ψ₀]
        have hweighted_decomp :
            (∑ k : Fin K,
              ((split.fold n k).card : ℝ)⁻¹ *
                ∑ i ∈ split.fold n k,
                  M.m (η_hat n k ω) (sample.Z i ω) M.θ₀) =
              ∑ k : Fin K,
                ((split.fold n k).card : ℝ)⁻¹ *
                  ((∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)) +
                    ∑ i ∈ split.fold n k,
                      foldScoreDiff n k ω (sample.Z i ω)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hscore_decomp k]
        unfold crossFitOneStepOracleDML ratioRaw scoreRaw
        rw [Finset.card_range, hif_sum]
        rw [hweighted_decomp]
        simp only [ψ₀, Finset.mul_sum, Finset.sum_neg_distrib,
          Finset.sum_add_distrib, mul_add,
          neg_mul, mul_neg, sub_eq_add_neg]
        ring_nf
      rw [hdecomp]
      exact IsLittleOp_const_mul_one (-M.linScaleInv) hsum_pieces
    simpa using h_full_reweighting

/-- **Asymptotic linearity of cross-fitted DML on a deterministic nuisance
good set.** Given [a moment system and its mean-zero and finite-variance
conditions](hyp:M,_hMZ,_hFV), [a sample, at least two folds, a split, and
nuisance fits](hyp:sample,_hK_pos,split,η_hat), assume [a uniform bilinear
remainder bound on the nuisance set](hyp:_hBR), [a failure-probability
sequence](hyp:Δ) that [vanishes](hyp:_hΔ), [all foldwise fits belong to that set
outside an event bounded by that sequence](hyp:_hT), [joint and uncurried
training-complement product measurability](hyp:_h_m_meas,_h_m_train_uncurry),
[a curried measurability witness retained for compatibility](hyp:_h_m_train),
[integrability and
square-integrability throughout the set](hyp:_h_m_int,_h_m_sq_int), and [the
score and product rates used by the proof](hyp:_h_score_diff_rate,_h_product_rate), plus
[individual nuisance rates retained for
compatibility](hyp:_h_indiv_rate_ρ₁,_h_indiv_rate_ρ₂).
Then [the cross-fitted estimator is asymptotically linear with the
inverse-scale-weighted true score](goal).

The compatibility measurability witness and individual rates do not enter the proof. -/
theorem crossFitOneStepOracleDML_isAsymLinear_of_goodSet
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (_hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (Δ : ℕ → ℝ≥0∞)
    (_hΔ : Tendsto Δ atTop (𝓝 0))
    {Crem : ℝ}
    (_hBR : BilinearRemainder M Crem)
    (_hT : ∀ n, μ {ω | ∃ k, η_hat n k ω ∉ M.H_ε} ≤ Δ n)
    (_h_m_meas :
      ∀ n k, Measurable (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_train :
      ∀ n k,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
          (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (_h_m_train_uncurry :
      ∀ n k,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => M.m η z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => (M.m η z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate :
      ∀ k, IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₁ :
      ∀ k, IsLittleOp
        (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₂ :
      ∀ k, IsLittleOp
        (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) μ)
    (_h_product_rate :
      ∀ k, IsLittleOp
        (fun n ω =>
          ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (crossFitOneStepOracleDML M sample split η_hat)
      M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample
      (fun n => Finset.range n) := by
  classical
  apply crossFitOneStepOracleDML_isAsymLinear_on_highProbEvent M _hMZ _hFV sample
    _hK_pos split η_hat (fun n => {ω | ∀ k, η_hat n k ω ∈ M.H_ε}) Δ _hΔ
  · intro n
    calc
      μ ({ω | ∀ k, η_hat n k ω ∈ M.H_ε} : Set Ω)ᶜ =
          μ {ω | ∃ k, η_hat n k ω ∉ M.H_ε} := by
        congr 1
        ext ω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
      _ ≤ Δ n := _hT n
  · intro n k ω hω
    exact _hBR (η_hat n k ω) (hω k)
  · exact _h_m_meas
  · exact _h_m_train
  · exact _h_m_train_uncurry
  · intro n k ω hω
    exact _h_m_int (η_hat n k ω) (hω k)
  · intro n k ω hω
    exact _h_m_sq_int (η_hat n k ω) (hω k)
  · exact _h_score_diff_rate
  · exact _h_indiv_rate_ρ₁
  · exact _h_indiv_rate_ρ₂
  · exact _h_product_rate

/-- Given [the cross-fitted DML setup and uniform deterministic-good-set
conditions](hyp:M,_hMZ,_hFV,sample,_hK_pos,split,η_hat,_hBR), [the
measurability, integrability, and rates used by the
proof](hyp:_h_m_meas,_h_m_train_uncurry,_h_m_int,_h_m_sq_int,_h_score_diff_rate,_h_product_rate),
[a curried measurability witness retained for compatibility](hyp:_h_m_train),
and [individual nuisance rates retained for
compatibility](hyp:_h_indiv_rate_ρ₁,_h_indiv_rate_ρ₂),
if [every foldwise nuisance fit belongs to the set almost surely at every
sample size](hyp:_hT), then [the cross-fitted estimator is asymptotically
linear](goal).

This is the zero-failure-probability corollary of
`crossFitOneStepOracleDML_isAsymLinear_of_goodSet`. The compatibility inputs do
not enter the proof. -/
theorem crossFitOneStepOracleDML_isAsymLinear_of_goodSet_ae
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (_hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    {Crem : ℝ}
    (_hBR : BilinearRemainder M Crem)
    (_hT : ∀ n k, ∀ᵐ ω ∂μ, η_hat n k ω ∈ M.H_ε)
    (_h_m_meas : ∀ n k,
      Measurable (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (_h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => M.m η z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => (M.m η z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₁ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₂ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (_h_product_rate : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear (crossFitOneStepOracleDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample
      (fun n => Finset.range n) := by
  classical
  apply crossFitOneStepOracleDML_isAsymLinear_of_goodSet M _hMZ _hFV sample
    _hK_pos split η_hat (fun _ => 0) tendsto_const_nhds _hBR
  · intro n
    have hall : ∀ᵐ ω ∂μ, ∀ k, η_hat n k ω ∈ M.H_ε := by
      exact Filter.eventually_all.2 fun k => _hT n k
    have hz : μ {ω | ∃ k, η_hat n k ω ∉ M.H_ε} = 0 := by
      simpa only [not_forall] using (ae_iff.mp hall)
    simpa [hz]
  · exact _h_m_meas
  · exact _h_m_train
  · exact _h_m_train_uncurry
  · exact _h_m_int
  · exact _h_m_sq_int
  · exact _h_score_diff_rate
  · exact _h_indiv_rate_ρ₁
  · exact _h_indiv_rate_ρ₂
  · exact _h_product_rate

/-- **Everywhere-good cross-fitted DML interface.** Under [pointwise nuisance
regularity](hyp:_hBR_at,_h_m_int,_h_m_sq_int)
and [the remaining moment and sampling
conditions](hyp:M,_hMZ,_hFV,sample,_hK_pos,split,η_hat), [joint and uncurried
product measurability](hyp:_h_m_meas,_h_m_train_uncurry), and [the score and
product rates](hyp:_h_score_diff_rate,_h_product_rate),
plus [a curried measurability witness](hyp:_h_m_train) and [individual nuisance
rates](hyp:_h_indiv_rate_ρ₁,_h_indiv_rate_ρ₂) retained for compatibility, [the
cross-fitted estimator is asymptotically linear](goal).

The compatibility inputs do not enter the proof. -/
theorem crossFitOneStepOracleDML_isAsymLinear_of_everywhere
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (_hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    {Crem : ℝ}
    (_hBR_at : ∀ n k ω,
      |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas : ∀ n k,
      Measurable (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (_h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω)
          inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_int : ∀ n k ω,
      Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ n k ω,
      Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate : ∀ k, IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₁ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₂ : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) μ)
    (_h_product_rate : ∀ k, IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear (crossFitOneStepOracleDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample
      (fun n => Finset.range n) := by
  apply crossFitOneStepOracleDML_isAsymLinear_on_highProbEvent M _hMZ _hFV sample
    _hK_pos split η_hat (fun _ => Set.univ) (fun _ => 0) tendsto_const_nhds
  · simp
  · exact fun n k ω _ => _hBR_at n k ω
  · exact _h_m_meas
  · exact _h_m_train
  · exact _h_m_train_uncurry
  · exact fun n k ω _ => _h_m_int n k ω
  · exact fun n k ω _ => _h_m_sq_int n k ω
  · exact _h_score_diff_rate
  · exact _h_indiv_rate_ρ₁
  · exact _h_indiv_rate_ρ₂
  · exact _h_product_rate

end OrthogonalMoments
end Estimation
end Causalean
