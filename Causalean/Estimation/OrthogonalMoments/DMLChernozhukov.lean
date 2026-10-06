/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract one-shot DML in **classical Chernozhukov form**

This file proves the general Chernozhukov form of the one-shot DML theorem:
the moment is evaluated at the truth `M.θ₀`, the estimator is a one-step
scaled step `θ̂ = θ₀ − s⁻¹ · Pₙ m(η̂, ·, θ₀)`, and the conclusion's influence
function is `−s⁻¹ · m(η₀, ·, θ₀)`.

For the AIPW linear score (`m(η, z, θ) = ψ(η, z) − θ`, `s = −1`), the
estimator reduces to `Pₙ ψ(η̂, ·)` and the influence function reduces to
`m(η₀, ·, θ₀)` — recovering the existing AIPW production proof.

The proof uses the standard G+B decomposition (centered fold-B sum + bias)
with the Chernozhukov-form score `m(η̂, ·, θ₀)` and influence function
`−s⁻¹ · m(η₀, ·, θ₀)`.
The bilinear-remainder hypothesis bounds `|∫ m(η̂, z, θ₀) dP_Z|`, matching
`MeanZero` at `θ = θ₀` directly (no `hθ_zero` reduction needed).

References:
* Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins (2018).
  *Double/Debiased Machine Learning for Treatment and Structural
  Parameters*.  Econometrics Journal 21(1), C1–C68.  Theorem 3.1
  (linear-score) and Theorem 3.3 (non-linear-score); Theorem 3.2 concerns
  variance estimation.
* See `doc/basic_concepts/Semi-parametric Inference/
  semi_parametric_inference.tex`, `thm:sp-generic-dml`.
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLGoodSet
public import Causalean.Estimation.OrthogonalMoments.RemainderBound
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Sample
public import Causalean.Stat.SampleSplit
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
public import Causalean.Stat.SampleSplit.PartialFoldCLT

/-! # Chernozhukov-Form Double Machine Learning

This file proves the abstract one-shot double machine learning theorem in the
classical Chernozhukov form. The estimator evaluates the moment at the true
target, rescales by the inverse linearization scale, and yields asymptotic linearity with
the corresponding influence function. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- For [a measurable population space with a population measure, a measurable observed-data
space with its observed-data law, and a real vector space of nuisance values](hyp:Ω,μ,Z,P_Z,H),
[a general moment system](hyp:M), [an independent and identically distributed
sample](hyp:sample), [a one-shot evaluation-fold split of that
sample](hyp:split), [a sequence of nuisance estimators](hyp:η_hat), and [a
sample-size index](hyp:n), the [Chernozhukov one-step double-machine-learning
estimator](goal)
maps each population state to the true target minus the inverse linearization
scale times the evaluation-fold empirical mean of the moment at that target and
the estimated nuisance.

Evaluates the score at the truth `M.θ₀` and rescales by the supplied scale inverse:

    θ̂_n := M.θ₀ − M.linScale⁻¹ ·
      ((1/|B(n)|) Σ_{i ∈ B(n)} m(η̂(n), Z_i, M.θ₀))

This is an oracle proof device in the DML argument. For linear scores
`m(η, z, θ) = m_a(η, z) θ + m_b(η, z)` (the AIPW family),
the empirical mean of `m(η̂, ·, θ₀)` collapses to a clean expression in
`m_b` and recentering with the identified scale recovers the standard sample-mean
form. -/
noncomputable def oneStepOracleDML
    (M : GeneralMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → H)
    (n : ℕ) : Ω → ℝ :=
  fun ω =>
    M.θ₀ - M.linScaleInv * (((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n, M.m (η_hat n ω) (sample.Z i ω) M.θ₀)

/-- **Asymptotic linearity of the Chernozhukov DML estimator on high-probability
events.** Given [a general moment system with mean-zero and finite-variance
truth score](hyp:M,_hMZ,_hFV), [an i.i.d. sample and one-shot split whose
evaluation fraction converges to a positive limit](hyp:sample,split,c,_hc_pos,_h_split_rate),
[nuisance fits and good events](hyp:η_hat,goodSet), [vanishing failure bounds
for those events](hyp:Δ,_hΔ,_hfail), [a remainder constant and a bilinear
bound on each good event](hyp:Crem,_hBR_at), [joint and uncurried
training-fold product measurability](hyp:_h_m_meas,_h_m_foldA_uncurry), [a
curried training-fold witness retained for interface
compatibility](hyp:_h_m_foldA), [score
integrability and square-integrability on the good events](hyp:_h_m_int,_h_m_sq_int),
and [vanishing score-difference and product rates](hyp:_h_score_diff_rate,_h_product_rate),
[the one-step estimator is asymptotically linear with the
inverse-scale-weighted true score](goal).

The proof uses the uncurried product-measurability witness; the separate
curried witness is accepted by the interface but does not enter the argument.

Hypotheses (mirroring `dml_asymptoticLinear`):

* `hMZ`         — `MeanZero M`, i.e., `∫ m(η₀, z, M.θ₀) dP_Z = 0`;
* `hFV`         — `Integrable (m(η₀, ·, θ₀))² P_Z`;
* `hBR_at`      — per-`η̂_n` bilinear remainder bound on the good event:
                  `|∫ m(η̂_n, z, θ₀) dP_Z| ≤ Crem · ρ₁(η̂_n, η₀) · ρ₂(η̂_n, η₀)`.
                  The public good-set theorem below derives this low-level form
                  from `BilinearRemainder M Crem` and high-probability good-set
                  membership. Neyman orthogonality is implicitly required for
                  the bound and is checked when constructing that predicate;
* one-shot split with rate `|B(n)|/n → c ∈ (0, ∞)` (`hc_pos`, `h_split_rate`);
* joint and uncurried fold-A product measurability; the separate curried
  witness is retained for interface compatibility and is not used by the proof;
* product rate `ρ₁ · ρ₂ = o_p(n^{-1/2})`;
* `h_score_diff_rate` — abstract analogue of AIPW's
  `aipw_score_diff_isLittleOp_one`.

Conclusion: the estimator is asymptotically linear at `M.θ₀` with influence
function `fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀`, indexed over `split.foldB`. -/
theorem oneStepOracleDML_isAsymLinear_on_highProbEvent
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (_hc_pos : 0 < c)
    (_h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H)
    (goodSet : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (_hΔ : Tendsto Δ atTop (𝓝 0))
    (_hfail : ∀ n, μ (goodSet n)ᶜ ≤ Δ n)
    {Crem : ℝ}
    (_hBR_at :
      ∀ n ω, ω ∈ goodSet n →
        |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤
          Crem * ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
                 ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas :
      ∀ n, Measurable (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (_h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_int :
      ∀ n ω, ω ∈ goodSet n → Integrable (fun z => M.m (η_hat n ω) z M.θ₀) P_Z)
    (_h_m_sq_int :
      ∀ n ω, ω ∈ goodSet n →
        Integrable (fun z => (M.m (η_hat n ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (_h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (oneStepOracleDML M sample split η_hat)
      M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample
      split.foldB := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero
    rw [integral_const_mul]
    rw [show (∫ a, M.m M.η₀ a M.θ₀ ∂P_Z) = 0 by
      simpa [MeanZero] using _hMZ]
    ring
  · -- finite_var
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
      (_hFV.const_mul (M.linScaleInv ^ 2))
  · -- remainder: centered fold-B fluctuation plus population remainder.
    let f : ℕ → Ω → Z → ℝ := fun n ω z =>
      M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀
    let G : ℕ → Ω → ℝ := fun n ω =>
      (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n, (f n ω (sample.Z i ω) -
          ∫ z, f n ω z ∂P_Z)
    let B : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt ((split.foldB n).card : ℝ) * ∫ z, f n ω z ∂P_Z
    let R : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt ((split.foldB n).card : ℝ) *
          (oneStepOracleDML M sample split η_hat n ω - M.θ₀) -
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n, (-M.linScaleInv * M.m M.η₀ (sample.Z i ω) M.θ₀)
    haveI : IsProbabilityMeasure P_Z := by
      rw [← sample.law]
      exact Measure.isProbabilityMeasure_map (sample.meas 0).aemeasurable
    have htruth_L2 : MemLp (fun z => M.m M.η₀ z M.θ₀) 2 P_Z :=
      (memLp_two_iff_integrable_sq
        (M.m_meas M.η₀ M.θ₀).aestronglyMeasurable).2 _hFV
    have hf_meas : ∀ n, Measurable (Function.uncurry (f n)) := by
      intro n
      change Measurable (fun p : Ω × Z =>
        M.m (η_hat n p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
      exact (_h_m_meas n).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
    have hf_foldA :
        ∀ n,
          Measurable[MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
            (fun ω => f n ω) := by
      intro n
      change Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
      exact (_h_m_foldA n).sub measurable_const
    have hf_uncurry_foldA :
        ∀ n,
          Measurable[(MeasurableSpace.comap
              (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
            (inferInstance : MeasurableSpace Z)]
            (Function.uncurry (f n)) := by
      intro n
      change Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace Z)]
        (fun p : Ω × Z => M.m (η_hat n p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
      exact (_h_m_foldA_uncurry n).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
    have hf_memLp : ∀ n ω, ω ∈ goodSet n → MemLp (f n ω) 2 P_Z := by
      intro n ω hω
      have hsq := _h_m_sq_int n ω hω
      have hrand_L2 : MemLp (fun z => M.m (η_hat n ω) z M.θ₀) 2 P_Z :=
        (memLp_two_iff_integrable_sq
          (M.m_meas (η_hat n ω) M.θ₀).aestronglyMeasurable).2 hsq
      exact hrand_L2.sub htruth_L2
    have hf_rate_one :
        IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P_Z).toReal)
          (fun _ => (1 : ℝ)) μ := by
      simpa [f] using _h_score_diff_rate
    have hG : IsLittleOp G (fun _ => (1 : ℝ)) μ := by
      simpa [G] using
        foldB_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent
          sample split f goodSet Δ _hΔ _hfail hf_meas hf_uncurry_foldA
          hf_memLp hf_rate_one
    have h_int_eq : ∀ n ω, ω ∈ goodSet n →
        ∫ z, f n ω z ∂P_Z =
          ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z := by
      intro n ω hω
      have hf_L2 := hf_memLp n ω hω
      have hm_int := _h_m_int n ω hω
      have hf_int : Integrable (f n ω) P_Z :=
        hf_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      have htruth_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z :=
        htruth_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      have hzero : (∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) = 0 := by
        simpa [MeanZero] using _hMZ
      calc
        ∫ z, f n ω z ∂P_Z =
            ∫ z, (M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) ∂P_Z := by rfl
        _ = ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z -
            ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z :=
          integral_sub hm_int htruth_int
        _ = ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z := by
          rw [hzero]
          ring
    let mGood : ℕ → Ω → ℝ := fun n ω =>
      if ω ∈ goodSet n then ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z else 0
    have h_int_good_rate :
        IsLittleOp mGood
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
      intro ε hε
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      let K : ℝ := |Crem| + 1
      have hKpos : 0 < K := by
        dsimp [K]
        linarith [abs_nonneg Crem]
      have htarget := (ENNReal.tendsto_nhds_zero.mp
        (_h_product_rate (ε / K) (div_pos hε hKpos))) δ hδ
      filter_upwards [htarget, eventually_ge_atTop (1 : ℕ)] with n hn hn_one
      exact (measure_mono (by
        intro ω hω
        change ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ ‖mGood n ω‖ at hω
        by_cases hgood : ω ∈ goodSet n
        · have hbr := _hBR_at n ω hgood
          rw [show mGood n ω = ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z by
            simp [mGood, hgood]] at hω
          rw [Real.norm_eq_abs] at hω
          let prodρ : ℝ :=
            ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
              ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ)
          have hprod_nonneg : 0 ≤ prodρ := by
            dsimp [prodρ]
            exact mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
          have hbr0 :
              |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤ Crem * prodρ := by
            simpa [prodρ, mul_assoc] using hbr
          have hle_abs :
              |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤ |Crem| * prodρ :=
            hbr0.trans (mul_le_mul_of_nonneg_right (le_abs_self Crem) hprod_nonneg)
          have hKbound :
              |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤ K * prodρ := by
            refine hle_abs.trans ?_
            exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hprod_nonneg
          have hthreshold_le_bound :
              ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ K * prodρ :=
            hω.trans hKbound
          have hdiv_le :
              (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / K ≤ prodρ := by
            rw [div_le_iff₀ hKpos]
            simpa [mul_comm, mul_left_comm, mul_assoc] using hthreshold_le_bound
          have hsmall :
              (ε / K) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ |prodρ| := by
            have hdiv_eq :
                (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / K =
                  (ε / K) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
              ring
            rw [← hdiv_eq]
            simpa [abs_of_nonneg hprod_nonneg] using hdiv_le
          exact hsmall
        · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
          have hthreshold_pos :
              0 < ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_pos hε (Real.rpow_pos_of_pos hn_pos _)
          exact False.elim ((not_le_of_gt hthreshold_pos) (by
            simpa [mGood, hgood, Real.norm_eq_abs] using hω))
        )).trans hn
    have h_int_raw_rate :
        IsLittleOp (fun n ω => ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
      apply isLittleOp_of_isLittleOp_on_highProbEvent goodSet Δ _hΔ _hfail
      · intro n ω hω
        change (∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z) =
          (if ω ∈ goodSet n then ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z else 0)
        rw [if_pos hω]
      · exact h_int_good_rate
    have h_int_rate :
        IsLittleOp (fun n ω => ∫ z, f n ω z ∂P_Z)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
      apply isLittleOp_of_isLittleOp_on_highProbEvent goodSet Δ _hΔ _hfail
      · exact h_int_eq
      · exact h_int_raw_rate
    have hB : IsLittleOp B (fun _ => (1 : ℝ)) μ := by
      intro ε' hε'
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      let C : ℝ := Real.sqrt c + 1
      have hCpos : 0 < C := by
        dsimp [C]
        linarith [Real.sqrt_nonneg c]
      have hCnonneg : 0 ≤ C := le_of_lt hCpos
      have hC2 : c < C ^ 2 := by
        dsimp [C]
        nlinarith [Real.sq_sqrt (le_of_lt _hc_pos), Real.sqrt_nonneg c]
      have hratio_event : ∀ᶠ n in atTop, ((split.foldB n).card : ℝ) / n < C ^ 2 := by
        exact _h_split_rate.eventually_lt_const hC2
      have hn_event : ∀ᶠ n : ℕ in atTop, n ≠ 0 := by
        exact eventually_ne_atTop 0
      have hint_event := (ENNReal.tendsto_nhds_zero.mp
        (h_int_rate (ε' / C) (div_pos hε' hCpos))) δ hδ
      filter_upwards [hratio_event, hn_event, hint_event] with n hratio hn_ne hn
      refine (measure_mono ?_).trans hn
      intro ω hω
      have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn_ne
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
      have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
      have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrtn_pos
      have hcard_le : ((split.foldB n).card : ℝ) ≤ C ^ 2 * (n : ℝ) := by
        have hlt : ((split.foldB n).card : ℝ) < C ^ 2 * (n : ℝ) := by
          field_simp [hn_pos.ne'] at hratio ⊢
          nlinarith
        exact le_of_lt hlt
      have hsqrt_le :
          Real.sqrt ((split.foldB n).card : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
        calc
          Real.sqrt ((split.foldB n).card : ℝ) ≤ Real.sqrt (C ^ 2 * (n : ℝ)) :=
            Real.sqrt_le_sqrt hcard_le
          _ = Real.sqrt (C ^ 2) * Real.sqrt (n : ℝ) := by
            rw [Real.sqrt_mul (sq_nonneg C)]
          _ = C * Real.sqrt (n : ℝ) := by
            rw [Real.sqrt_sq hCnonneg]
      have hsqrtcard_nonneg : 0 ≤ Real.sqrt ((split.foldB n).card : ℝ) :=
        Real.sqrt_nonneg _
      have hthreshold_le_prod :
          ε' ≤ Real.sqrt ((split.foldB n).card : ℝ) * |∫ z, f n ω z ∂P_Z| := by
        simpa [B, abs_mul, abs_of_nonneg hsqrtcard_nonneg] using hω
      have hle_prod :
          Real.sqrt ((split.foldB n).card : ℝ) * |∫ z, f n ω z ∂P_Z| ≤
            (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| := by
        exact mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
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
    have hsum : IsLittleOp (fun n ω => G n ω + B n ω) (fun _ => (1 : ℝ)) μ := by
      intro ε' hε'
      rw [ENNReal.tendsto_nhds_zero]
      intro η hη
      by_cases hηtop : η = ⊤
      · filter_upwards with n
        simp [hηtop]
      have hηpos : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hηtop
      let α : ℝ := η.toReal / 4
      have hαpos : 0 < α := by
        dsimp [α]
        linarith
      let A : ℕ → Set Ω := fun n => {ω | (ε' / 2) * 1 ≤ |G n ω|}
      let Cset : ℕ → Set Ω := fun n => {ω | (ε' / 2) * 1 ≤ |B n ω|}
      let Dset : ℕ → Set Ω := fun n => {ω | ε' * 1 ≤ |G n ω + B n ω|}
      have hGevent_le := (ENNReal.tendsto_nhds_zero.mp (hG (ε' / 2) (by linarith)))
        (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
      have hBevent_le := (ENNReal.tendsto_nhds_zero.mp (hB (ε' / 2) (by linarith)))
        (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
      have htwo_alpha_lt_eta : ENNReal.ofReal (2 * α) < η := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal]
        · dsimp [α]
          linarith
        · dsimp [α]
          linarith [le_of_lt hηpos]
        · exact hηtop
      filter_upwards [hGevent_le, hBevent_le] with n hGA hBC
      have hsubset : Dset n ⊆ A n ∪ Cset n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ (ε' / 2) * 1 ≤ |G n ω| := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotC : ¬ (ε' / 2) * 1 ≤ |B n ω| := by
          intro hy
          exact hnot (Or.inr hy)
        have hGlt : |G n ω| < (ε' / 2) * 1 := lt_of_not_ge hnotA
        have hBlt : |B n ω| < (ε' / 2) * 1 := lt_of_not_ge hnotC
        have hsum_lt : |G n ω + B n ω| < ε' * 1 :=
          calc
            |G n ω + B n ω| ≤ |G n ω| + |B n ω| :=
              abs_add_le (G n ω) (B n ω)
            _ < (ε' / 2) * 1 + (ε' / 2) * 1 := add_lt_add hGlt hBlt
            _ = ε' * 1 := by ring
        exact (not_le_of_gt hsum_lt) hω
      exact le_of_lt <| calc
        μ {ω | ε' * 1 ≤ |G n ω + B n ω|} = μ (Dset n) := by
          simp [Dset]
        _ ≤ μ (A n ∪ Cset n) := measure_mono hsubset
        _ ≤ μ (A n) + μ (Cset n) := MeasureTheory.measure_union_le (A n) (Cset n)
        _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hGA hBC
        _ = ENNReal.ofReal (2 * α) := by
          rw [← ENNReal.ofReal_add]
          · congr 1
            ring
          · linarith
          · linarith
        _ < η := htwo_alpha_lt_eta
    have const_mul_isLittleOp_one : ∀ (a : ℝ) (X : ℕ → Ω → ℝ),
        IsLittleOp X (fun _ => (1 : ℝ)) μ →
          IsLittleOp (fun n ω => a * X n ω) (fun _ => (1 : ℝ)) μ := by
      intro a X hX ε hε
      by_cases ha : a = 0
      · subst a
        have hzero :
            (fun n => μ {ω | ε * (fun _ => (1 : ℝ)) n ≤ ‖0 * X n ω‖}) =
              fun _ => (0 : ENNReal) := by
          funext n
          simp [not_le_of_gt hε]
        rw [hzero]
        exact tendsto_const_nhds
      · have hscale_pos : 0 < ε / |a| := div_pos hε (abs_pos.mpr ha)
        have hXt := hX (ε / |a|) hscale_pos
        refine hXt.congr' ?_
        filter_upwards with n
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, mul_one, norm_mul, Real.norm_eq_abs]
        rw [div_le_iff₀ (abs_pos.mpr ha)]
        ring_nf
    have hdecomp : R = fun n ω => -M.linScaleInv * (G n ω + B n ω) := by
      funext n ω
      unfold R G B f oneStepOracleDML
      by_cases hcard : (split.foldB n).card = 0
      · simp [hcard]
      · have hcard_pos : 0 < ((split.foldB n).card : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hcard
        have hsqrt_pos : 0 < Real.sqrt ((split.foldB n).card : ℝ) :=
          Real.sqrt_pos.mpr hcard_pos
        have hsqrt_sq :
            Real.sqrt ((split.foldB n).card : ℝ) *
                Real.sqrt ((split.foldB n).card : ℝ) =
              ((split.foldB n).card : ℝ) :=
          Real.mul_self_sqrt hcard_pos.le
        field_simp [hsqrt_pos.ne', hsqrt_sq]
        simp [Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_const, nsmul_eq_mul, sub_eq_add_neg, ← Finset.mul_sum]
        ring
    change IsLittleOp R (fun _ => (1 : ℝ)) μ
    rw [hdecomp]
    exact const_mul_isLittleOp_one (-M.linScaleInv) (fun n ω => G n ω + B n ω) hsum

/-- Given [a moment system with its mean-zero and finite-variance
conditions](hyp:M,_hMZ,_hFV), [a one-shot sample split with a positive limiting
evaluation fraction](hyp:sample,split,_hc_pos,_h_split_rate), and [nuisance
fits](hyp:η_hat), assume the population remainder, score integrability, and
score square-integrability conditions [hold almost
surely](hyp:_hBR_at,_h_m_int,_h_m_sq_int), the score has [joint and uncurried
training-fold product measurability](hyp:_h_m_meas,_h_m_foldA_uncurry), the
interface also accepts [a compatibility curried
witness](hyp:_h_m_foldA), and [the score and
product rates vanish](hyp:_h_score_diff_rate,_h_product_rate). Then [the
one-step estimator is asymptotically linear](goal).

The compatibility witness does not enter the proof. -/
theorem oneStepOracleDML_isAsymLinear_of_ae
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (_hc_pos : 0 < c)
    (_h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H)
    {Crem : ℝ}
    (_hBR_at : ∀ n, ∀ᵐ ω ∂μ,
      |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas : ∀ n,
      Measurable (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_foldA : ∀ n,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (_h_m_foldA_uncurry : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace Z)]
        (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_int : ∀ n, ∀ᵐ ω ∂μ,
      Integrable (fun z => M.m (η_hat n ω) z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ n, ∀ᵐ ω ∂μ,
      Integrable (fun z => (M.m (η_hat n ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (_h_product_rate : IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear (oneStepOracleDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB := by
  let goodSet : ℕ → Set Ω := fun n => {ω |
    |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ) ∧
    Integrable (fun z => M.m (η_hat n ω) z M.θ₀) P_Z ∧
    Integrable (fun z => (M.m (η_hat n ω) z M.θ₀) ^ 2) P_Z}
  have hgood : ∀ n, ∀ᵐ ω ∂μ, ω ∈ goodSet n := by
    intro n
    filter_upwards [_hBR_at n, _h_m_int n, _h_m_sq_int n] with ω hbr hint hsq
    exact ⟨hbr, hint, hsq⟩
  apply oneStepOracleDML_isAsymLinear_on_highProbEvent M _hMZ _hFV sample split
    _hc_pos _h_split_rate η_hat goodSet (fun _ => 0) tendsto_const_nhds
  · intro n
    have hz : μ (goodSet n)ᶜ = 0 := by
      apply ae_iff.mp
      filter_upwards [hgood n] with ω hω
      exact hω
    simp [hz]
  · intro n ω hω
    exact hω.1
  · exact _h_m_meas
  · exact _h_m_foldA
  · exact _h_m_foldA_uncurry
  · intro n ω hω
    exact hω.2.1
  · intro n ω hω
    exact hω.2.2
  · exact _h_score_diff_rate
  · exact _h_product_rate

/-- **Asymptotic linearity of one-shot DML on a deterministic nuisance good
set.** Given [a moment system and its mean-zero and finite-variance
conditions](hyp:M,_hMZ,_hFV), [a sample and split, a positive split limit, and
nuisance fits](hyp:sample,split,_hc_pos,_h_split_rate,η_hat),
assume [a uniform bilinear remainder bound on the nuisance set](hyp:_hBR), [a
failure-probability sequence](hyp:Δ) that [vanishes](hyp:_hΔ), [the fits miss that set with
probability at most the stated bound](hyp:_hT), [the score has joint and
uncurried training-fold product
measurability](hyp:_h_m_meas,_h_m_foldA_uncurry), and the interface accepts [a
compatibility curried witness](hyp:_h_m_foldA),
[every nuisance value in the set gives an integrable square-integrable
score](hyp:_h_m_int,_h_m_sq_int), and [the score and product rates
vanish](hyp:_h_score_diff_rate,_h_product_rate). Then [the one-step estimator is
asymptotically linear with the inverse-scale-weighted true score](goal).

The compatibility witness does not enter the proof. -/
theorem oneStepOracleDML_isAsymLinear_of_goodSet
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (_hc_pos : 0 < c)
    (_h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H)
    (Δ : ℕ → ℝ≥0∞)
    (_hΔ : Tendsto Δ atTop (𝓝 0))
    {Crem : ℝ}
    (_hBR : BilinearRemainder M Crem)
    (_hT : ∀ n, μ {ω | η_hat n ω ∉ M.H_ε} ≤ Δ n)
    (_h_m_meas :
      ∀ n, Measurable (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (_h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => M.m η z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => (M.m η z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (_h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (oneStepOracleDML M sample split η_hat)
      M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀)
      sample
      split.foldB := by
  apply oneStepOracleDML_isAsymLinear_on_highProbEvent M _hMZ _hFV sample split
    _hc_pos _h_split_rate η_hat (fun n => {ω | η_hat n ω ∈ M.H_ε}) Δ _hΔ
  · intro n
    simpa only [Set.compl_setOf, Set.mem_setOf_eq] using _hT n
  · intro n ω hω
    exact _hBR (η_hat n ω) hω
  · exact _h_m_meas
  · exact _h_m_foldA
  · exact _h_m_foldA_uncurry
  · intro n ω hω
    exact _h_m_int (η_hat n ω) hω
  · intro n ω hω
    exact _h_m_sq_int (η_hat n ω) hω
  · exact _h_score_diff_rate
  · exact _h_product_rate

/-- Given [the one-shot DML setup and uniform deterministic-good-set
conditions](hyp:M,_hMZ,_hFV,sample,split,_hc_pos,_h_split_rate,η_hat,_hBR),
[the measurability, integrability, and rate inputs used by the
proof](hyp:_h_m_meas,_h_m_foldA_uncurry,_h_m_int,_h_m_sq_int,_h_score_diff_rate,_h_product_rate),
and [a curried training-fold witness retained for
compatibility](hyp:_h_m_foldA),
if [the nuisance fit belongs to the set almost surely at every sample
size](hyp:_hT), then [the one-step estimator is asymptotically linear](goal).

This is the zero-failure-probability corollary of
`oneStepOracleDML_isAsymLinear_of_goodSet`. The compatibility witness does not
enter the proof. -/
theorem oneStepOracleDML_isAsymLinear_of_goodSet_ae
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (_hc_pos : 0 < c)
    (_h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H)
    {Crem : ℝ}
    (_hBR : BilinearRemainder M Crem)
    (_hT : ∀ n, ∀ᵐ ω ∂μ, η_hat n ω ∈ M.H_ε)
    (_h_m_meas : ∀ n,
      Measurable (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_foldA : ∀ n,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (_h_m_foldA_uncurry : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace Z)]
        (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => M.m η z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => (M.m η z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (_h_product_rate : IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear (oneStepOracleDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB := by
  apply oneStepOracleDML_isAsymLinear_of_goodSet M _hMZ _hFV sample split
    _hc_pos _h_split_rate η_hat (fun _ => 0) tendsto_const_nhds _hBR
  · intro n
    have hz : μ {ω | η_hat n ω ∉ M.H_ε} = 0 := by
      apply ae_iff.mp
      filter_upwards [_hT n] with ω hω
      exact hω
    simpa [hz]
  · exact _h_m_meas
  · exact _h_m_foldA
  · exact _h_m_foldA_uncurry
  · exact _h_m_int
  · exact _h_m_sq_int
  · exact _h_score_diff_rate
  · exact _h_product_rate

/-- **Everywhere-good one-shot DML interface.** Under [pointwise nuisance
regularity](hyp:_hBR_at,_h_m_int,_h_m_sq_int) and
[the remaining moment and sampling
conditions](hyp:M,_hMZ,_hFV,sample,split,_hc_pos,_h_split_rate,η_hat), [joint
and uncurried product measurability](hyp:_h_m_meas,_h_m_foldA_uncurry), and
[the score and product rates](hyp:_h_score_diff_rate,_h_product_rate),
plus [a curried training-fold witness retained for
compatibility](hyp:_h_m_foldA), [the one-step estimator is asymptotically
linear](goal).

The compatibility witness does not enter the proof. -/
theorem oneStepOracleDML_isAsymLinear_of_everywhere
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (_hc_pos : 0 < c)
    (_h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H)
    {Crem : ℝ}
    (_hBR_at : ∀ n ω,
      |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤
        Crem * ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
          ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas :
      ∀ n, Measurable (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_foldA : ∀ n,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (_h_m_foldA_uncurry : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace Z)]
        (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_int : ∀ n ω,
      Integrable (fun z => M.m (η_hat n ω) z M.θ₀) P_Z)
    (_h_m_sq_int : ∀ n ω,
      Integrable (fun z => (M.m (η_hat n ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
      (fun _ => (1 : ℝ)) μ)
    (_h_product_rate : IsLittleOp
      (fun n ω => ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
        ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear (oneStepOracleDML M sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB := by
  apply oneStepOracleDML_isAsymLinear_of_ae M _hMZ _hFV sample split
    _hc_pos _h_split_rate η_hat
  · exact fun n => Filter.Eventually.of_forall (_hBR_at n)
  · exact _h_m_meas
  · exact _h_m_foldA
  · exact _h_m_foldA_uncurry
  · exact fun n => Filter.Eventually.of_forall (_h_m_int n)
  · exact fun n => Filter.Eventually.of_forall (_h_m_sq_int n)
  · exact _h_score_diff_rate
  · exact _h_product_rate

end OrthogonalMoments
end Estimation
end Causalean
