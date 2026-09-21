/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract TRAE-DR asymptotic-linearity criterion

This file proves an abstract, unconditional remainder-transfer criterion. It
does not encode fold-A training, primal or dual L² consistency, or the
conditional and operator-side sufficient conditions in the source note.

The headline statement: under an abstract sufficient bundle of range,
mixed-bias, empirical-process, and finite-variance conditions, the TRAE-DR
estimator is asymptotically linear at `θ₀` with influence function
`ρ₀(w) := φ_{h₀, q₀}(w) − θ₀`, indexed over the estimation fold
`split.foldB`.

The bundled hypothesis structure `TRAEDRRemainderHyps` records exactly the
conditions consumed by this expansion:

* `candidate_mem` — `(ĥ_n, q̂_n)` lie in the candidate sets `(Hbar, Qbar)`;
* `mixed_bias`   — the mixed-bias integral, scaled by
                   `√|B(n)|`, is `o_p(1)`;
* `ep_remainder` — empirical-process / mean-squared-continuity remainder
                   from replacing `(h₀, q₀)` by `(ĥ_n, q̂_n)` in the
                   estimation-fold average is `o_p(1)` after `√|B(n)|`
                   scaling;
* `finite_var`   — `E[ρ₀² ] < ∞` under `P_W`.

The mean-zero condition `E[ρ₀] = 0` is derived below from the primal and
dual moment identities by `mean_zero_of_DualSolution`; it is not an
independent hypothesis.

A generic order-transfer lemma
`mixed_bias_isLittleOp_of_pointwise_bound` is also stated: it turns any
pointwise upper bound whose scaled version is `o_p(1)` into the required
mixed-bias rate. It does not prove the note's two operator-side
Cauchy–Schwarz bounds. The concrete conditional-expectation operator `T`, its
adjoint `T*`, and spectral calculus support live in the `NPIV/Operator`
modules; this DR criterion deliberately depends only on a supplied scalar
mixed-bias bound.
-/

module
public import Causalean.Estimation.NPIV.MixedBias
public import Causalean.Estimation.NPIV.DR.Estimator
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
public import Causalean.Stat.SampleSplit
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.SampleSplit.PartialFoldCLT

/-!
States and proves an asymptotic-linearity criterion for the doubly robust NPIV
estimator.  Its hypothesis bundle contains exactly the candidate-membership,
mixed-bias, empirical-process, and finite-variance conditions used to isolate
the leading oracle-score term.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

/-! ## Oracle score -/

/-- [The oracle score](goal) for [an inverse-problem system on a measured sample
space](hyp:Ω,μ,S), [a dual nuisance](hyp:q₀), and [an observation](hyp:w) is the true-primal
pseudo-outcome minus the scalar target.

Oracle score `ρ₀(w) := φ_{h₀, q₀}(w) − θ₀`.

This is the oracle score used by the abstract asymptotic-linearity criterion. -/
noncomputable def ρ₀
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) (q₀ : S.𝒵 → ℝ) (w : S.𝒲) : ℝ :=
  S.phiVal S.h₀ q₀ w - S.θ₀

/-- Mean-zero of the oracle score under the structural law `μ`.

This is the population identity behind the influence-function centering:
`Θ(h₀, q₀) = θ₀` by the dual moment identity, hence
`E[φ_{h₀,q₀}(W) − θ₀] = 0`. -/
theorem mean_zero_of_DualSolution_mu
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀) :
    ∫ ω, ρ₀ S q₀ (S.W ω) ∂μ = 0 := by
  have hphi_int : Integrable (fun ω => S.phiVal S.h₀ q₀ (S.W ω)) μ := by
    unfold InverseProblemSystem.phiVal
    exact ((S.integrable_m_e S.h₀ S.h₀_mem).add
      (S.integrable_m q₀ hq₀.mem)).sub
      (S.integrable_qh S.h₀ S.h₀_mem q₀ hq₀.mem)
  have htheta_int : Integrable (fun _ : Ω => S.θ₀) μ := integrable_const _
  have hzero := Θ_q₀_eq_θ₀ S hq₀ S.h₀_mem
  unfold ρ₀
  rw [integral_sub hphi_int htheta_int]
  unfold InverseProblemSystem.Θ InverseProblemSystem.phi at hzero
  rw [hzero]
  simp

/-- Mean-zero of the oracle score under the observation law `P_W`.

The law bridge `μ.map S.W = P_W` records the standard statistical convention
that `P_W` is the distribution of the observed random variable `W`. -/
theorem mean_zero_of_DualSolution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲}
    (h_law_W : μ.map S.W = P_W)
    (hρ₀_meas : Measurable (ρ₀ S q₀)) :
    ∫ w, ρ₀ S q₀ w ∂P_W = 0 := by
  rw [← h_law_W]
  rw [MeasureTheory.integral_map S.meas_W.aemeasurable
    hρ₀_meas.aestronglyMeasurable]
  exact mean_zero_of_DualSolution_mu S hq₀

/-! ## Bundled sufficient remainder hypotheses -/

/-- The **TRAE-DR remainder hypotheses** state that [both fitted nuisances stay in their
candidate classes](hyp:candidate_mem), [their √-scaled mixed-bias integral is
negligible](hyp:mixed_bias), [the centered plug-in empirical-process remainder vanishes at
the √-rate](hyp:ep_remainder), and [the oracle score has finite variance](hyp:finite_var).
These are precisely the inputs consumed by the asymptotic-linearity criterion. -/
structure TRAEDRRemainderHyps
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (_hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲}
    [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ)) : Prop where
  /-- Support condition for the formal mixed-bias identity: the fitted primal
      and dual nuisance functions lie in the candidate classes for every
      sample size and outcome. -/
  candidate_mem : ∀ n ω, h_hat n ω ∈ S.Hbar ∧ q_hat n ω ∈ S.Qbar
  /-- Unconditional mixed-bias sufficient criterion: scaling the mixed-bias
      integral by `√|B(n)|` is `o_p(1)` under `μ`. This is the unconditional
      assumption used here rather than the conditional-on-training-fold
      hypothesis from the paper statement. -/
  mixed_bias :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
                  (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ)
      (fun _ => (1 : ℝ)) μ
  /-- Empirical-process / mean-squared-continuity remainder (iii):
        the centered fold-B sum of `φ̂_n − φ₀` is `o_p(1)` after `√|B(n)|`
        scaling. -/
  ep_remainder :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n,
            (S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω)
              - S.phiVal S.h₀ q₀ (sample.Z i ω))
            -
            Real.sqrt ((split.foldB n).card : ℝ) *
              ∫ ω', (S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')
                       - S.phiVal S.h₀ q₀ (S.W ω')) ∂μ)
      (fun _ => (1 : ℝ)) μ
  /-- (iv) Finite oracle-score variance: `E[ρ₀² ] < ∞` under `P_W`. -/
  finite_var :
    Integrable (fun w => (ρ₀ S q₀ w) ^ 2) P_W

/-! ## Headline asymptotic-linearity theorem -/

/-- **Abstract TRAE-DR asymptotic-linearity criterion.** For [an inverse-problem
system](hyp:S), [a dual solution](hyp:hq₀), [an i.i.d. sample](hyp:sample), [a one-shot
split](hyp:split), [primal nuisance functions](hyp:h_hat), and [dual nuisance
functions](hyp:q_hat), suppose [the candidate-membership, unconditional mixed-bias,
empirical-process, and finite-variance conditions hold](hyp:_hyps). Given [the observation-law
bridge](hyp:h_law_W) and [measurability of the oracle score](hyp:hρ₀_meas), [the TRAE-DR
estimator is asymptotically linear at the structural target, with the oracle score as its
mean-zero, finite-variance influence function](goal).

Conclusion: the TRAE-DR estimator is asymptotically linear at `θ₀` with
influence function `ρ₀`, indexed over the estimation fold `split.foldB`.

The sufficient remainder hypotheses are supplied by `TRAEDRRemainderHyps`.
They directly assume unconditional mixed-bias and empirical-process remainder bounds; they do
not impose fold-A training, nuisance consistency, or conditional operator-side bounds.
The law bridge `μ.map S.W = P_W` and oracle-score measurability are the
standard observation-law assumptions needed to derive the mean-zero
influence-function condition under `P_W`. -/
theorem trae_dr_isAsymLinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲}
    [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (hρ₀_meas : Measurable (ρ₀ S q₀)) :
    IsAsymLinear
      (trae_dr_estimator S sample split h_hat q_hat)
      S.θ₀
      (ρ₀ S q₀)
      sample
      split.foldB := by
  refine ⟨mean_zero_of_DualSolution S hq₀ h_law_W hρ₀_meas, _hyps.finite_var, ?_⟩
  have h_add_one : ∀ {Xn Yn : ℕ → Ω → ℝ},
      IsLittleOp Xn (fun _ => (1 : ℝ)) μ →
        IsLittleOp Yn (fun _ => (1 : ℝ)) μ →
          IsLittleOp (fun n ω => Xn n ω + Yn n ω) (fun _ => (1 : ℝ)) μ := by
    intro Xn Yn hX hY ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    by_cases hδtop : δ = ⊤
    · filter_upwards with n
      simp [hδtop]
    have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
    let α : ℝ := δ.toReal / 4
    have hαpos : 0 < α := by
      dsimp [α]
      linarith
    let A : ℕ → Set Ω := fun n => {ω | (ε / 2) * (1 : ℝ) ≤ |Xn n ω|}
    let B : ℕ → Set Ω := fun n => {ω | (ε / 2) * (1 : ℝ) ≤ |Yn n ω|}
    let C : ℕ → Set Ω := fun n => {ω | ε * (1 : ℝ) ≤ |Xn n ω + Yn n ω|}
    have hXevent_le := (ENNReal.tendsto_nhds_zero.mp (hX (ε / 2) (by linarith)))
      (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
    have hYevent_le := (ENNReal.tendsto_nhds_zero.mp (hY (ε / 2) (by linarith)))
      (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
    have htwo_alpha_lt_delta : ENNReal.ofReal (2 * α) < δ := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal]
      · dsimp [α]
        linarith
      · dsimp [α]
        linarith [le_of_lt hδpos]
      · exact hδtop
    filter_upwards [hXevent_le, hYevent_le] with n hXA hYB
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ ε / 2 ≤ |Xn n ω| := by
        intro hx
        exact hnot (Or.inl (by simpa [A] using hx))
      have hnotB : ¬ ε / 2 ≤ |Yn n ω| := by
        intro hy
        exact hnot (Or.inr (by simpa [B] using hy))
      have hXlt : |Xn n ω| < ε / 2 := lt_of_not_ge hnotA
      have hYlt : |Yn n ω| < ε / 2 := lt_of_not_ge hnotB
      have hsum : |Xn n ω + Yn n ω| < ε := by
        calc
          |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| := abs_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add hXlt hYlt
          _ = ε := by ring
      exact (not_le_of_gt hsum) (by simpa [C] using hω)
    exact le_of_lt <| calc
      μ {ω | ε * (fun _ => (1 : ℝ)) n ≤ |Xn n ω + Yn n ω|}
          = μ (C n) := by simp [C]
      _ ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hXA hYB
      _ = ENNReal.ofReal (2 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · linarith
        · linarith
      _ < δ := htwo_alpha_lt_delta
  let EP : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
      ∑ i ∈ split.foldB n,
        (S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω)
          - S.phiVal S.h₀ q₀ (sample.Z i ω))
      -
      Real.sqrt ((split.foldB n).card : ℝ) *
        ∫ ω', (S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')
                 - S.phiVal S.h₀ q₀ (S.W ω')) ∂μ
  let MB : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((split.foldB n).card : ℝ) *
      ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
              (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ
  have hsum : IsLittleOp (fun n ω => EP n ω + MB n ω) (fun _ => (1 : ℝ)) μ := by
    exact h_add_one _hyps.ep_remainder _hyps.mixed_bias
  have h_eq : ∀ n ω,
      Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
        - (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
            ∑ i ∈ split.foldB n, ρ₀ S q₀ (sample.Z i ω)
        = EP n ω + MB n ω := by
    intro n ω
    have hrange := _hyps.candidate_mem n ω
    have hphi_hat_int :
        Integrable
          (fun ω' => S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')) μ := by
      unfold InverseProblemSystem.phiVal
      exact ((S.integrable_m_e (h_hat n ω) hrange.1).add
        (S.integrable_m (q_hat n ω) hrange.2)).sub
        (S.integrable_qh (h_hat n ω) hrange.1 (q_hat n ω) hrange.2)
    have hphi_zero_int :
        Integrable
          (fun ω' => S.phiVal S.h₀ q₀ (S.W ω')) μ := by
      unfold InverseProblemSystem.phiVal
      exact ((S.integrable_m_e S.h₀ S.h₀_mem).add
        (S.integrable_m q₀ hq₀.mem)).sub
        (S.integrable_qh S.h₀ S.h₀_mem q₀ hq₀.mem)
    have h_int_eq :
        (∫ ω', (S.phiVal (h_hat n ω) (q_hat n ω) (S.W ω')
                 - S.phiVal S.h₀ q₀ (S.W ω')) ∂μ)
          =
        ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
                (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ := by
      rw [integral_sub hphi_hat_int hphi_zero_int]
      have hmb := mixed_bias_identity S hq₀ hrange.1 hrange.2
      have hzero := Θ_q₀_eq_θ₀ S hq₀ S.h₀_mem
      unfold InverseProblemSystem.Θ InverseProblemSystem.phi at hmb hzero
      rw [hzero]
      simpa [InverseProblemSystem.X, InverseProblemSystem.Z] using hmb
    by_cases hcard : (split.foldB n).card = 0
    · have hempty : split.foldB n = ∅ := Finset.card_eq_zero.mp hcard
      simp [EP, MB, h_int_eq, trae_dr_estimator, ρ₀, hempty]
    · have hcard_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hcard
      have hcard_pos_real : 0 < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos_nat
      have hsqrt_ne :
          Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 := by
        intro hsqrt_zero
        have hzero_real : ((split.foldB n).card : ℝ) = 0 := by
          rw [← Real.mul_self_sqrt (le_of_lt hcard_pos_real), hsqrt_zero, zero_mul]
        exact (ne_of_gt hcard_pos_real) hzero_real
      have hsqrt_sq :
          Real.sqrt ((split.foldB n).card : ℝ) *
              Real.sqrt ((split.foldB n).card : ℝ)
            = ((split.foldB n).card : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have h_sqrt_mul_inv_card :
          Real.sqrt ((split.foldB n).card : ℝ) *
              (((split.foldB n).card : ℝ)⁻¹)
            = (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ := by
        let r : ℝ := Real.sqrt ((split.foldB n).card : ℝ)
        let c : ℝ := ((split.foldB n).card : ℝ)
        have hr : r ≠ 0 := by simpa [r] using hsqrt_ne
        have hsq : r * r = c := by simp [r, c, hsqrt_sq]
        change r * c⁻¹ = r⁻¹
        rw [← hsq]
        field_simp [hr]
      have h_inv_sqrt_mul_card :
          (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ((split.foldB n).card : ℝ)
            = Real.sqrt ((split.foldB n).card : ℝ) := by
        let r : ℝ := Real.sqrt ((split.foldB n).card : ℝ)
        let c : ℝ := ((split.foldB n).card : ℝ)
        have hr : r ≠ 0 := by simpa [r] using hsqrt_ne
        have hsq : r * r = c := by simp [r, c, hsqrt_sq]
        change r⁻¹ * c = r
        rw [← hsq]
        field_simp [hr]
      simp [EP, MB, h_int_eq, trae_dr_estimator, ρ₀, Finset.sum_sub_distrib]
      rw [mul_sub]
      rw [← mul_assoc (Real.sqrt ((split.foldB n).card : ℝ))
        (((split.foldB n).card : ℝ)⁻¹)
        (∑ i ∈ split.foldB n,
          S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω))]
      rw [h_sqrt_mul_inv_card]
      rw [mul_sub]
      rw [← mul_assoc (Real.sqrt ((split.foldB n).card : ℝ))⁻¹
        ((split.foldB n).card : ℝ) S.θ₀]
      rw [h_inv_sqrt_mul_card]
      ring
  convert hsum using 1
  ext n ω
  exact h_eq n ω

/-! ## Pointwise-bound transfer for the mixed-bias rate -/

/-- For [an inverse-problem system](hyp:S), [an i.i.d. sample](hyp:sample),
[a one-shot sample split](hyp:split), [primal nuisance estimators](hyp:h_hat),
[dual nuisance estimators](hyp:q_hat), and [a real upper-bound
sequence](hyp:bnd), if [the absolute mixed-bias integral is bounded pointwise
by that sequence](hyp:_h_dom) and [the fold-scaled bound is
`o_p(1)`](hyp:_h_rate), then [the fold-scaled mixed-bias integral is
`o_p(1)`](goal).

This order-transfer lemma is operator-agnostic. In particular, it does not
establish either operator-side Cauchy–Schwarz inequality from the source note;
a caller must supply such an inequality through `_h_dom`. -/
theorem mixed_bias_isLittleOp_of_pointwise_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    {P_W : Measure S.𝒲}
    [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (bnd : ℕ → Ω → ℝ)
    (_h_dom : ∀ n ω,
      |∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
              (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ|
        ≤ bnd n ω)
    (_h_rate :
      IsLittleOp (fun n ω => Real.sqrt ((split.foldB n).card : ℝ) * bnd n ω)
        (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
                  (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ)
      (fun _ => (1 : ℝ)) μ := by
  -- Reference to `sample` is intentional: the conclusion is the precise
  -- form of the `mixed_bias` field above, indexed by `split.foldB`.
  let _ := sample
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hrate := (ENNReal.tendsto_nhds_zero.mp (_h_rate ε hε)) δ hδ
  filter_upwards [hrate] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  simp only [Set.mem_setOf_eq, mul_one, Real.norm_eq_abs] at hω ⊢
  let bias : ℝ :=
    ∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
            (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ
  have h_bnd_nonneg : 0 ≤ bnd n ω := le_trans (abs_nonneg bias) (_h_dom n ω)
  have h_sqrt_nonneg : 0 ≤ Real.sqrt ((split.foldB n).card : ℝ) := Real.sqrt_nonneg _
  have h_abs_bias :
      |Real.sqrt ((split.foldB n).card : ℝ) * bias|
        = Real.sqrt ((split.foldB n).card : ℝ) * |bias| := by
    rw [abs_mul, abs_of_nonneg h_sqrt_nonneg]
  have h_abs_bnd :
      |Real.sqrt ((split.foldB n).card : ℝ) * bnd n ω|
        = Real.sqrt ((split.foldB n).card : ℝ) * bnd n ω := by
    rw [abs_of_nonneg (mul_nonneg h_sqrt_nonneg h_bnd_nonneg)]
  rw [show
      (∫ ω', (q₀ (S.zOf (S.W ω')) - q_hat n ω (S.zOf (S.W ω'))) *
              (h_hat n ω (S.xOf (S.W ω')) - S.h₀ (S.xOf (S.W ω'))) ∂μ)
        = bias from rfl, h_abs_bias] at hω
  rw [h_abs_bnd]
  exact hω.trans (mul_le_mul_of_nonneg_left (_h_dom n ω) h_sqrt_nonneg)

end DR
end NPIV
end Estimation
end Causalean
