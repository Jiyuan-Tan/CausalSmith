/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Inference.VarianceEstimation
public import Causalean.Stat.Inference.Studentize

/-! # Wald intervals with the influence-function standard error

For an asymptotically linear estimator with influence function `ψ`, the asymptotic standard
deviation of `√n (θ̂ₙ − θ₀)` is `√(∫ ψ² dP)`.  This file estimates it by the square root of the
plug-in variance of `ψ(Z₁), …, ψ(Zₙ)` and proves the resulting studentized CLT and Wald
coverage.

The standard error is an **oracle**: it evaluates the true influence function `ψ`, which
generally depends on the unknown distribution.  A feasible interval replaces `ψ` by an
estimate and needs an extra consistency argument, which is not given here.

Main declarations: `IIDSample.oracleInfluenceSE`, its consistency
`IIDSample.oracleInfluenceSE_tendsto_inProb`, the studentized statistic
`IIDSample.oracleStudentized`, the limit law `oracleStudentized_tendsto`, and the coverage
theorem `oracle_wald_coverage`. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- For [a measurable sample space, measurable observation space, sample-space measure, and
observation-space measure](hyp:Ω,X,μ,P), [an independent, identically distributed
sample](hyp:S), [a real-valued influence function](hyp:ψ), and [a sample size](hyp:n), the
[oracle influence-function standard error](goal) is the square root of the plug-in variance of
the influence function over the first `n` observations.

It estimates the asymptotic standard deviation `√(∫ ψ² dP)`; it is an oracle because it uses
the true influence function `ψ`. -/
noncomputable def oracleInfluenceSE (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => Real.sqrt (empiricalVar S ψ n ω)

/-- **Consistency of the oracle influence-function standard error.** Along an i.i.d. sample
`S`, if the influence function `ψ` is [measurable](hyp:hψ_meas), [integrable](hyp:hψ_int),
[square-integrable](hyp:hψ_sq_int), and [has population mean zero](hyp:hmean), then [the oracle
standard error converges in probability to the asymptotic standard deviation $\sqrt{\int
\psi^2\,dP}$](goal).

    Square root (continuous) applied to `empiricalVar_tendsto_inProb`. -/
theorem oracleInfluenceSE_tendsto_inProb (S : IIDSample Ω X μ P)
    [IsProbabilityMeasure P] {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hmean : ∫ x, ψ x ∂P = 0) :
    Tendsto_inProb (oracleInfluenceSE S ψ)
      (fun _ => Real.sqrt (∫ x, (ψ x) ^ 2 ∂P)) μ :=
  Tendsto_inProb.sqrt
    (empiricalVar_tendsto_inProb S hψ_meas hψ_int hψ_sq_int hmean)

/-- For [a measurable sample space, measurable observation space, sample-space measure, and
observation-space measure](hyp:Ω,X,μ,P), [a sequence of real-valued estimators](hyp:θn), [a
target real value](hyp:θ₀), [an independent, identically distributed sample](hyp:S), [a
real-valued influence function](hyp:ψ), and [a sample size](hyp:n), the [oracle studentized
statistic](goal) is $\sqrt n(\widehat\theta_n-\theta_0)/\widehat\sigma_n$, where the
denominator is the oracle influence-function standard error computed from the full sample of
that size.

The full-sample index family `I n = Finset.range n` is used. -/
noncomputable def oracleStudentized (θn : ℕ → Ω → ℝ) (θ₀ : ℝ)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω =>
    IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n ω
      / oracleInfluenceSE S ψ n ω

end IIDSample

/-! ## Studentized CLT and Wald coverage -/

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- **Studentized CLT with the oracle standard error.** Let [`θ̂ₙ` be asymptotically linear at
`θ₀` with influence function `ψ` along the i.i.d. sample `S`](hyp:h), where `ψ` is
[measurable](hyp:hψ_meas), [integrable](hyp:hψ_int), and [square-integrable](hyp:hψ_sq_int);
suppose further that [the influence function is nondegenerate, $\int \psi^2\,dP >
0$](hyp:hpos), [the rescaled estimator is a.e. measurable at every sample size](hyp:hθn_meas),
and [the oracle studentized statistic is a.e. measurable at every sample size](hyp:hStud_meas).
Then [the oracle-studentized statistic $\sqrt n(\hat\theta_n-\theta_0)/\hat\sigma_n$ converges
in distribution to the standard normal law](goal), where $\hat\sigma_n$ is the oracle
influence-function standard error.

    Combines `IsAsymLinear.tendsto_normal` (numerator `⇒ N(0, ∫ ψ²)`),
`oracleInfluenceSE_tendsto_inProb` (`σ̂ₙ →ₚ √(∫ ψ²)`), and the generic studentized CLT
`Tendsto_dist.div_tendsto_inProb_gaussian`. -/
theorem oracleStudentized_tendsto
    (h : IsAsymLinear θn θ₀ ψ S (fun m => Finset.range m))
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hpos : 0 < ∫ x, (ψ x) ^ 2 ∂P)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ)
    (hStud_meas : ∀ n,
      AEMeasurable (IIDSample.oracleStudentized θn θ₀ S ψ n) μ) :
    Tendsto_dist (IIDSample.oracleStudentized θn θ₀ S ψ)
      (gaussianMeasure 0 1) μ hStud_meas := by
  set σ₀ : ℝ := Real.sqrt (∫ x, (ψ x) ^ 2 ∂P) with hσ₀
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpos
  have hσ₀sq : σ₀ ^ 2 = ∫ x, (ψ x) ^ 2 ∂P := Real.sq_sqrt (le_of_lt hpos)
  -- numerator ⇒ N(0, σ₀²)
  have hXn :
      Tendsto_dist (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m))
        (gaussianMeasure 0 (σ₀ ^ 2)) μ hθn_meas := by
    rw [hσ₀sq]
    exact IsAsymLinear.tendsto_normal h hψ_meas hθn_meas
  -- oracle SE ⇒ σ₀ in probability
  have hSE : Tendsto_inProb (IIDSample.oracleInfluenceSE S ψ) (fun _ => σ₀) μ :=
    IIDSample.oracleInfluenceSE_tendsto_inProb S hψ_meas hψ_int hψ_sq_int h.mean_zero
  -- generic studentized CLT
  exact Tendsto_dist.div_tendsto_inProb_gaussian hσ₀_pos hθn_meas hXn hSE hStud_meas

/-- **Wald asymptotic coverage with the oracle standard error.** Under [the asymptotic-linearity
hypothesis](hyp:h), [measurability](hyp:hψ_meas), [integrability](hyp:hψ_int), and
[square-integrability](hyp:hψ_sq_int) of `ψ`, [influence-function nondegeneracy](hyp:hpos), and
[measurability of the rescaled estimator](hyp:hθn_meas) and [of the studentized
statistic](hyp:hStud_meas) at every sample size — the hypotheses of
`oracleStudentized_tendsto` — fix [a positive critical value `z`](hyp:hz) and a
coverage-probability sequence `coverProb` that [asymptotically tracks the studentized
interval's true coverage event](hyp:h_bridge); then [`coverProb` converges to the standard
normal probability of the interval `[-z, z]`](goal), so the oracle studentized interval has
asymptotic $N(0,1)$-coverage.

    Specializing `z = z_{1-α/2}` gives the `1 − α` confidence interval
`θ̂ₙ ± z_{1-α/2} · σ̂ₙ / √n`.  The bridge hypothesis isolates the event-rewrite /
exceptional-set step (matching `trae_dr_wald_coverage_of_event_bridge`); it holds with
`coverProb`
the natural interval-coverage probability whenever `σ̂ₙ > 0` a.e. -/
theorem oracle_wald_coverage
    (h : IsAsymLinear θn θ₀ ψ S (fun m => Finset.range m))
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hpos : 0 < ∫ x, (ψ x) ^ 2 ∂P)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ)
    (hStud_meas : ∀ n,
      AEMeasurable (IIDSample.oracleStudentized θn θ₀ S ψ n) μ)
    {z : ℝ} (hz : 0 < z) (coverProb : ℕ → ℝ)
    (h_bridge : Tendsto
      (fun n => coverProb n
        - (μ {ω | IIDSample.oracleStudentized θn θ₀ S ψ n ω
            ∈ Set.Icc (-z) z}).toReal) atTop (𝓝 0)) :
    Tendsto coverProb atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  have hStud := oracleStudentized_tendsto h hψ_meas hψ_int hψ_sq_int hpos
    hθn_meas hStud_meas
  exact Tendsto_dist.wald_coverage hStud_meas hStud hz coverProb h_bridge

end Causalean.Stat
