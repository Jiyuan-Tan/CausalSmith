/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Asymptotic linearity of estimators

Predicate `IsAsymLinear θn θ₀ ψ S` matching `def:est-asym-linear` in
`doc/basic_concepts/po/estimation.tex`, plus the headline corollary that
asymptotic linearity implies `√n`-asymptotic normality
(`prop:est-al-implies-an`).

`gaussianMeasure m σ²` is a real-typed wrapper around Mathlib's
`ProbabilityTheory.gaussianReal` so the rest of the project does not need to
juggle `NNReal` for the variance.  The CLT contact-point lemma
`IIDSample.clt_normalized_sum` consumes the upstream CLT formalisation and
packages it as convergence in distribution for the project's normalized
i.i.d. sums.
-/

module
public import Causalean.Stat.Limit.ConvergenceVec
public import Causalean.Stat.Sample
public import Causalean.Tactic.Attr
public import Mathlib.Probability.CentralLimitTheorem

/-! # Scalar Asymptotic Linearity

This file provides the scalar asymptotic-linearity interface used by the
estimation and inference layers. `gaussianMeasure` is the project's real-valued
Gaussian wrapper, and `IsAsymLinear` records a mean-zero influence function,
finite second moment, and an `o_p(1)` linearization remainder along a chosen
finite index family.

The namespace also exposes `IsAsymLinear.normalizedSum` and
`IsAsymLinear.rescaledEstimator`. The main limit results are
`IIDSample.clt_normalized_sum`, the CLT contact point for normalized i.i.d.
sums, `Modes.TendstoInLaw.add_isLittleOp_one` and related Slutsky/congruence
wrappers, and `IsAsymLinear.tendsto_normal`, which turns full-sample scalar
asymptotic linearity into asymptotic normality. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Gaussian measure on ℝ

Real-typed alias for `ProbabilityTheory.gaussianReal`.  Negative variances
collapse to `0` (Dirac mass at `m`) via `Real.toNNReal`. -/

/-- For [a real-valued mean](hyp:m) and [a real-valued variance input](hyp:v), the [Gaussian probability measure on the real line](goal) has the specified mean and variance $max(v,0)$; thus a negative variance input is replaced by zero and yields a point mass at the mean.

This is a real-valued wrapper around `ProbabilityTheory.gaussianReal`. -/
noncomputable def gaussianMeasure (m v : ℝ) : Measure ℝ :=
  gaussianReal m v.toNNReal

/-- For every [real-valued mean](hyp:m) and [real-valued variance input](hyp:v), the
[Gaussian measure on the real line is a probability measure](goal). -/
instance instIsProbabilityMeasureGaussianMeasure (m v : ℝ) :
    IsProbabilityMeasure (gaussianMeasure m v) := by
  unfold gaussianMeasure
  infer_instance

/-! ## Asymptotic linearity -/

/-- An estimator is asymptotically linear when its scaled estimation error equals the
normalized empirical average of an influence function that is [mean zero](hyp:mean_zero)
and [square-integrable](hyp:finite_var) under the population law, up to
[a term that is negligible in probability](hyp:remainder).

The finite index set attached to each sample size chooses which observations
enter the empirical average:

* `mean_zero`  : `∫ ψ dP = 0`.
* `finite_var` : `∫ ψ² dP < ∞`.
* `remainder`  : `√|I n| (θn n − θ₀) − (1/√|I n|) Σ_{i ∈ I n} ψ (Z_i) = o_p(1)`.

The full-sample case is `I n = Finset.range n` and recovers the classical
asymptotic-linearity definition (`prop:est-al-implies-an`).  For sample-split
estimators, `I n = split.foldB n` gives the fold-B asymptotic linearity
(`thm:est-plug-in-ate-al`, `thm:est-dml-ate-al`); under a fixed split ratio
`|B(n)|/n → c ∈ (0, 1)`, the fold-B form implies √n-asymptotic normality
with variance `σ²/c` (the standard sample-splitting cost). -/
structure IsAsymLinear {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    (θn : ℕ → Ω → ℝ) (θ₀ : ℝ) (ψ : X → ℝ)
    (S : IIDSample Ω X μ P) (I : ℕ → Finset ℕ) : Prop where
  mean_zero  : ∫ x, ψ x ∂P = 0
  finite_var : Integrable (fun x => (ψ x) ^ 2) P
  remainder  :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((I n).card : ℝ) * (θn n ω - θ₀)
          - (Real.sqrt ((I n).card : ℝ))⁻¹ *
            ∑ i ∈ I n, ψ (S.Z i ω))
      (fun _ => (1 : ℝ)) μ

namespace IsAsymLinear

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
  {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- For [a measurable sample space carrying a measure](hyp:Ω,μ), [a measurable observation space carrying a population measure](hyp:X,P), [an independent and identically distributed sample from that population](hyp:S), [a real-valued influence function](hyp:ψ), [a finite index set selected for every nonnegative integer](hyp:I), and [a nonnegative integer index](hyp:n), the [normalized partial sum](goal) maps each sample-space outcome to $|I_n|^{-1/2}\sum_{i\in I_n}\psi(Z_i)$.

The normalization uses the reciprocal square root of the selected block's cardinality. -/
noncomputable def normalizedSum (S : IIDSample Ω X μ P) (ψ : X → ℝ)
    (I : ℕ → Finset ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Real.sqrt ((I n).card : ℝ))⁻¹ * ∑ i ∈ I n, ψ (S.Z i ω)

/-- The normalised partial sum at sample size index `n` sends a unit to the sum of the
influence-function values over the index block, rescaled by the reciprocal square root of the
block size. -/
@[causal_defs_simps]
lemma normalizedSum_def (S : IIDSample Ω X μ P) (ψ : X → ℝ)
    (I : ℕ → Finset ℕ) (n : ℕ) :
    normalizedSum S ψ I n =
      fun ω => (Real.sqrt ((I n).card : ℝ))⁻¹ * ∑ i ∈ I n, ψ (S.Z i ω) :=
  rfl

/-- For [a sample space](hyp:Ω), [a sequence of real-valued estimators on that space](hyp:θn), [a real-valued target parameter](hyp:θ₀), [a finite index set selected for every nonnegative integer](hyp:I), and [a nonnegative integer index](hyp:n), the [rescaled estimator](goal) maps each sample-space outcome to $\sqrt{|I_n|}\,[\widehat\theta_n-\theta_0]$ at that outcome.

The scale is the square root of the selected block's cardinality. -/
noncomputable def rescaledEstimator (θn : ℕ → Ω → ℝ) (θ₀ : ℝ)
    (I : ℕ → Finset ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.sqrt ((I n).card : ℝ) * (θn n ω - θ₀)

end IsAsymLinear

/-! ## CLT contact point

`IIDSample.clt_normalized_sum` is the only place where the upstream CLT
dependency is consumed.  It says: along an i.i.d. sample with mean-zero,
square-integrable transform `ψ`, the normalised partial sum
`(1/√n) Σ_{i<n} ψ(Z_i)` converges in distribution to `N(0, ∫ ψ² dP)` under the
ambient measure `μ`.
-/
/-- **Central limit theorem for normalised sample sums.** Along the i.i.d. sample `S`, if the
transform `ψ` of the observations is [measurable](hyp:hψ_meas), [has population mean
zero](hyp:hψ_mean), and [is square-integrable](hyp:hψ_sq_int), then [the normalised partial sum
— the sum of the transformed observations over the first `n` indices, divided by $\sqrt
n$ — converges in distribution to the centred normal law with variance equal to the
population second moment $\int \psi^2\,dP$](goal).

    This is the single contact point through which the
upstream CLT enters the estimation theory. -/
theorem IIDSample.clt_normalized_sum
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ x, ψ x ∂P = 0)
    (hψ_sq_int : Integrable (fun x => (ψ x) ^ 2) P) :
    @Modes.TendstoInLaw ℕ (fun _ => Ω) _ ℝ _ _ _ (fun _ => μ)
      (fun _ => S.indep.isProbabilityMeasure)
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m)) atTop
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P))
      (instIsProbabilityMeasureGaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n) μ := by
    intro n
    simp only [causal_defs_simps]
    exact ((Finset.measurable_sum _
      (fun i _ => hψ_meas.comp (S.meas i))).const_mul _).aemeasurable
  -- The transformed sample `W i = ψ ∘ Z i` is i.i.d., centred, and square integrable.
  have hW_meas : ∀ i, Measurable (fun ω => ψ (S.Z i ω)) := fun i => hψ_meas.comp (S.meas i)
  have hlaw0 : μ.map (S.Z 0) = P := S.law
  have hmean : ∫ ω, ψ (S.Z 0 ω) ∂μ = 0 := by
    rw [← integral_map (S.meas 0).aemeasurable hψ_meas.aestronglyMeasurable, hlaw0, hψ_mean]
  have hsq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ := by
    have h : Integrable (fun x => (ψ x) ^ 2) (μ.map (S.Z 0)) := by
      rw [hlaw0]; exact hψ_sq_int
    exact h.comp_measurable (S.meas 0)
  have hmemLp : MemLp (fun ω => ψ (S.Z 0 ω)) 2 μ :=
    (memLp_two_iff_integrable_sq (hW_meas 0).aestronglyMeasurable).2 hsq_int
  have hsq_mean : ∫ ω, (ψ (S.Z 0 ω)) ^ 2 ∂μ = ∫ x, (ψ x) ^ 2 ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable (hψ_meas.pow_const 2).aestronglyMeasurable,
      hlaw0]
  have hvar : Var[fun ω => ψ (S.Z 0 ω); μ] = ∫ x, (ψ x) ^ 2 ∂P := by
    have h := variance_eq_sub hmemLp
    simp only [Pi.pow_apply] at h
    rw [h, hmean, hsq_mean]
    ring
  have hindep : iIndepFun (fun i ω => ψ (S.Z i ω)) μ := by
    simpa [Function.comp_def] using S.indep.comp (fun _ x => ψ x) (fun _ => hψ_meas)
  have hident : ∀ i, IdentDistrib (fun ω => ψ (S.Z i ω)) (fun ω => ψ (S.Z 0 ω)) μ μ := by
    intro i
    simpa [Function.comp_def] using ((S.identDist i).comp hψ_meas).symm
  -- Mathlib's CLT, with the Gaussian limit realised on its own probability space.
  haveI hPG : IsProbabilityMeasure (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)) :=
    instIsProbabilityMeasureGaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)
  have hY : HasLaw (id : ℝ → ℝ)
      (gaussianReal 0 (Var[fun ω => ψ (S.Z 0 ω); μ]).toNNReal)
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)) := by
    rw [hvar]
    exact HasLaw.id
  have hCLT := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ω => ψ (S.Z i ω)) (P := μ)
    (P' := gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)) hY hmemLp hindep hident
  -- Since `ψ` is centred, Mathlib's centred normalised sum is literally ours.
  have hfun : ∀ n : ℕ,
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ *
          (∑ k ∈ Finset.range n, ψ (S.Z k ω) - (n : ℝ) * ∫ ω, ψ (S.Z 0 ω) ∂μ))
        = IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n := by
    intro n
    funext ω
    simp [causal_defs_simps, hmean, Finset.card_range]
  refine (Tendsto_dist_iff _ _ _ hSum_meas).2 ?_
  have htgt : (⟨gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P),
        instIsProbabilityMeasureGaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)⟩ : ProbabilityMeasure ℝ)
      = ⟨(gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)).map id,
          Measure.isProbabilityMeasure_map hCLT.aemeasurable_limit⟩ :=
    Subtype.ext Measure.map_id.symm
  rw [htgt]
  refine Filter.Tendsto.congr' ?_ hCLT.tendsto
  filter_upwards with n
  exact Subtype.ext (congrArg (fun f : Ω → ℝ => Measure.map f μ) (hfun n))

/-- If [a real sequence converges in distribution to a centered Gaussian law](hyp:hX)
and [deterministic scalar multipliers converge to a constant](hyp:ha), then
[the scaled sequence converges to the centered Gaussian law with variance
multiplied by the square of that constant](goal).

If `Xn ⇒ N(0, v)` and deterministic scalars `a n → a₀`, then
`a n • Xn ⇒ N(0, a₀² v)`.  This is the Gaussian specialization of the
measure-level deterministic-scalar Slutsky wrapper. -/
theorem Modes.TendstoInLaw.const_mul_tendsto_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {a : ℕ → ℝ} {a₀ v : ℝ}
    (hX : Modes.TendstoInLaw (fun _ : ℕ => μ) Xn atTop (gaussianMeasure 0 v))
    (ha : Tendsto a atTop (𝓝 a₀)) :
    Modes.TendstoInLaw (fun _ : ℕ => μ) (fun n ω => a n * Xn n ω) atTop
        (gaussianMeasure 0 (a₀ ^ 2 * v)) := by
  have hXn : ∀ n, AEMeasurable (Xn n) μ := hX.forall_aemeasurable
  have hScaled : ∀ n, AEMeasurable (fun ω => a n * Xn n ω) μ := fun n =>
    (measurable_const.mul measurable_id).aemeasurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure ((gaussianMeasure 0 v).map (fun x : ℝ => a₀ * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hscaled_dist :
      Modes.TendstoInLaw (fun _ : ℕ => μ) (fun n ω => a n * Xn n ω) atTop
          ((gaussianMeasure 0 v).map (fun x : ℝ => a₀ * x)) :=
    (Tendsto_dist_iff _ _ _ hScaled).2
      (Modes.TendstoInLaw.const_mul_tendsto hX ha)
  have hmap :
      (gaussianMeasure 0 v).map (fun x : ℝ => a₀ * x)
        = gaussianMeasure 0 (a₀ ^ 2 * v) := by
    simp [gaussianMeasure, gaussianReal_map_const_mul, mul_zero,
      Real.toNNReal_mul (sq_nonneg a₀), Real.toNNReal_of_nonneg (sq_nonneg a₀)]
  simpa [hmap] using hscaled_dist
/-! ## Asymptotic linearity ⇒ asymptotic normality

The headline statement.  Combines `IIDSample.clt_normalized_sum` (the CLT
contact point) with `Modes.TendstoInLaw.add_isLittleOp_one` (Slutsky). -/

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- Given [that `θn` is asymptotically linear at `θ₀` with influence function `ψ` along the
i.i.d. sample `S`](hyp:h), where `ψ` is [measurable](hyp:hψ_meas) and [the rescaled estimator
$\sqrt n(\theta_n-\theta_0)$ is a.e. measurable at every sample size](hyp:hθn_meas), then [the
rescaled estimator converges in distribution to the centred normal law with variance $\int
\psi^2\,dP$](goal).

    The Gaussian target is `gaussianMeasure 0 σ²` where `σ² = ∫ ψ² dP`.  The
measurability hypothesis on the rescaled estimator is imposed at the call
site; measurability of the partial sum follows from that of `ψ` and the sample
coordinates. -/
theorem IsAsymLinear.tendsto_normal
    (h : IsAsymLinear θn θ₀ ψ S (fun m => Finset.range m))
    (hψ_meas : Measurable ψ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ) :
    @Modes.TendstoInLaw ℕ (fun _ => Ω) _ ℝ _ _ _ (fun _ => μ)
      (fun _ => S.indep.isProbabilityMeasure)
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m)) atTop
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P))
      (instIsProbabilityMeasureGaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n) μ := by
    intro n
    simp only [causal_defs_simps]
    exact ((Finset.measurable_sum _
      (fun i _ => hψ_meas.comp (S.meas i))).const_mul _).aemeasurable
  have hCLT :=
    IIDSample.clt_normalized_sum S hψ_meas h.mean_zero h.finite_var
  refine Modes.TendstoInLaw.add_isLittleOp_one hCLT hθn_meas ?_
  -- `IsAsymLinear.remainder` uses `(I n).card` with `I = Finset.range`, which
  -- equals `n`; the resulting `IsLittleOp` matches the Slutsky absorption form.
  have := h.remainder
  simpa [IsAsymLinear.normalizedSum, IsAsymLinear.rescaledEstimator,
    Finset.card_range] using this

end Causalean.Stat
