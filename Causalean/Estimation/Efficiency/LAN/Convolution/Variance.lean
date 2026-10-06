/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.LAN.Convolution.Convolution
public import Mathlib.Probability.Moments.Variance

/-!
# Variance consequence of the scalar convolution theorem

This module derives the scalar asymptotic variance lower bound from convolution factorization.
The only finiteness hypothesis is a finite second moment of the estimator limit.  In particular,
finite variance of the residual is derived from the factorization rather than assumed.
-/

public section

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory ProbabilityTheory Topology

/-- If the convolution of two probability laws has a finite second moment and the left law has
a finite second moment, then the right law also has a finite second moment. -/
theorem memLp_two_right_of_conv
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hconv : MemLp id 2 (μ.conv ν)) :
    MemLp id 2 ν := by
  -- Realize convolution as the law of `x+y` under `μ.prod ν`; since `y=(x+y)-x`, pull
  -- `MemLp` across the relevant measure maps and use closure under subtraction.
  unfold Measure.conv at hconv
  have hsum : MemLp (fun z : ℝ × ℝ => z.1 + z.2) 2 (μ.prod ν) := by
    have h := (memLp_map_measure_iff
      (g := id) (f := fun z : ℝ × ℝ => z.1 + z.2) (μ := μ.prod ν)
      (by fun_prop) (by fun_prop)).1 hconv
    simpa [Function.comp_def] using h
  have hfst : MemLp (fun z : ℝ × ℝ => z.1) 2 (μ.prod ν) := by
    simpa using hμ.comp_fst ν
  have hsnd : MemLp (fun z : ℝ × ℝ => z.2) 2 (μ.prod ν) := by
    convert hsum.sub hfst using 1
    ext z
    dsimp
    ring
  have hmap : MemLp id 2 (Measure.map Prod.snd (μ.prod ν)) := by
    apply (memLp_map_measure_iff
      (g := id) (f := Prod.snd) (μ := μ.prod ν) (by fun_prop) (by fun_prop)).2
    simpa [Function.comp_def] using hsnd
  rw [measurePreserving_snd.map_eq] at hmap
  exact hmap

/-- For probability laws with finite second moments, the variance of their convolution is the
sum of their variances. -/
theorem variance_id_conv
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    variance id (μ.conv ν) = variance id μ + variance id ν := by
  -- Represent the convolution by coordinate addition on `μ.prod ν` and apply
  -- `ProbabilityTheory.variance_add_prod` plus `HasLaw.variance_eq`.
  unfold Measure.conv
  calc
    variance id (Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (μ.prod ν)) =
        variance (id ∘ fun z : ℝ × ℝ => z.1 + z.2) (μ.prod ν) :=
      variance_map (X := id) (Y := fun z : ℝ × ℝ => z.1 + z.2)
        (μ := μ.prod ν) (by fun_prop) (by fun_prop)
    _ = variance id μ + variance id ν := by
      simpa [Function.comp_def] using
        (ProbabilityTheory.variance_add_prod (X := id) (Y := id) hμ hν)

/-- The efficient centered Gaussian law has a finite second moment. -/
theorem efficientGaussianLaw_memLp_two
    {K : Type*} [NormedAddCommGroup K] (gradient : K) :
    MemLp id 2 (efficientGaussianLaw gradient) := by
  -- Unfold to `gaussianReal` and use the Gaussian finite-moment theorem.
  unfold efficientGaussianLaw
  exact ProbabilityTheory.memLp_id_gaussianReal 2

/-- The variance of the efficient centered Gaussian law is exactly the squared norm of the
canonical gradient. -/
theorem efficientGaussianLaw_variance
    {K : Type*} [NormedAddCommGroup K] (gradient : K) :
    variance id (efficientGaussianLaw gradient) = ‖gradient‖ ^ 2 := by
  -- Apply `ProbabilityTheory.variance_id_gaussianReal` and simplify `Real.toNNReal` using
  -- nonnegativity of the squared norm.
  simp [efficientGaussianLaw]

/-- **Variance bound from convolution.**  If a probability limit law with finite second moment
factors as the convolution of the efficient `N(0, ‖gradient‖²)` law and a residual probability
law, then its variance is at least `‖gradient‖²`. -/
theorem asymptoticVariance_ge_gradientNormSq_of_factorization
    {K : Type*} [NormedAddCommGroup K] (gradient : K)
    (limitLaw residualLaw : Measure ℝ)
    [IsProbabilityMeasure limitLaw] [IsProbabilityMeasure residualLaw]
    (hfactor : limitLaw = (efficientGaussianLaw gradient).conv residualLaw)
    (hfinite : MemLp id 2 limitLaw) :
    ‖gradient‖ ^ 2 ≤ variance id limitLaw := by
  -- Rewrite by `hfactor`, derive residual `MemLp` with `memLp_two_right_of_conv`, expand
  -- variance with `variance_id_conv`, and use nonnegativity of variance.
  have hefficient := efficientGaussianLaw_memLp_two gradient
  have hconvFinite : MemLp id 2
      ((efficientGaussianLaw gradient).conv residualLaw) := by
    simpa [hfactor] using hfinite
  have hresidual := memLp_two_right_of_conv
    (efficientGaussianLaw gradient) residualLaw hefficient hconvFinite
  rw [hfactor, variance_id_conv _ _ hefficient hresidual,
    efficientGaussianLaw_variance]
  exact le_add_of_nonneg_right (variance_nonneg _ _)

/-- Compatibility with a paper's tangent-density argument: if every finite score collection gives
a variance lower bound for an approximating gradient and those gradients converge in norm to the
canonical gradient, then the limiting variance is bounded below by the full gradient norm. -/
theorem variance_ge_gradientNormSq_of_dense_scores
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (gradient : K) (finiteGradient : ℕ → K) (v : ℝ)
    (hfiniteBound : ∀ j, ‖finiteGradient j‖ ^ 2 ≤ v)
    (hdense : Tendsto finiteGradient Filter.atTop (𝓝 gradient)) :
    ‖gradient‖ ^ 2 ≤ v := by
  -- Continuity of `x ↦ ‖x‖²` gives convergence of the left sides; pass the pointwise
  -- inequalities to the limit through the closed interval `Set.Iic v`.
  apply le_of_tendsto ((continuous_norm.pow 2).continuousAt.tendsto.comp hdense)
  exact Filter.Eventually.of_forall hfiniteBound

/-- In a finite-dimensional experiment with [local asymptotic normality](hyp:lan), [a regular scalar estimator](hyp:regular), [a canonical-gradient representation](hyp:canonical), and [a finite second moment for its limit law](hyp:hfinite), [the limit variance is at least the squared canonical-gradient norm](goal). -/
theorem regular_asymptoticVariance_ge_gradientNormSq
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H}
    {statistic : (n : ℕ) → Ω n → ℝ} {targetDerivative : H →ₗ[ℝ] ℝ}
    {scoreMap : H →ₗ[ℝ] K} {gradient : K} {limitLaw : Measure ℝ}
    {scoreLimit : Measure H}
    (lan : IsLAN E centralSequence information scoreLimit)
    (regular : IsRegularEstimator E statistic targetDerivative limitLaw)
    (canonical : CanonicalGradientPairing information targetDerivative scoreMap gradient)
    (hfinite : MemLp id 2 limitLaw) :
    ‖gradient‖ ^ 2 ≤ variance id limitLaw := by
  -- Obtain the residual factorization from `regular_convolution_limit`, install the probability
  -- instance for `limitLaw` from regularity, and invoke the factorization variance lemma.
  obtain ⟨residualLaw, hresidualProbability, hfactor⟩ :=
    regular_convolution_limit lan regular canonical
  let _ : IsProbabilityMeasure limitLaw := regular.limit_probability
  let _ : IsProbabilityMeasure residualLaw := hresidualProbability
  exact asymptoticVariance_ge_gradientNormSq_of_factorization
    gradient limitLaw residualLaw hfactor hfinite

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
