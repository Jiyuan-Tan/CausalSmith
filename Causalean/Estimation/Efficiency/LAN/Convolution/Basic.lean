/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.Modes
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Moments.Variance

/-!
# Local experiments and local asymptotic normality

This module gives a paper-independent interface for triangular local experiments.  A local
experiment consists of a base law and one local-alternative law for each finite-dimensional
direction.  Its log likelihood ratio is the logarithm of the Radon--Nikodym derivative of the
absolutely continuous part of the local law with respect to the base law.

Weak convergence is formulated by bounded continuous test functions so that the sample space
may vary with the row.  `IsLAN` records the Gaussian central-sequence limit and the quadratic
log-likelihood expansion.  No survival-analysis or paper-run objects occur in this layer.
-/

@[expose] public section

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory Topology
open scoped RealInnerProductSpace

variable {Ω : ℕ → Type*} [mΩ : ∀ n, MeasurableSpace (Ω n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A row-indexed random element converges weakly to `Q` when its expectation against every
bounded continuous real test function converges to the corresponding expectation under `Q`.

The definition permits a different measurable sample space and probability law in every row.
Probability and measurability assumptions are carried by the surrounding experiment and the
theorems using this predicate. -/
def WeaklyConverges [TopologicalSpace H] [MeasurableSpace H]
    (P : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → H) (Q : Measure H) : Prop :=
  (∀ n, AEMeasurable (X n) (P n)) ∧
    ∀ f : BoundedContinuousFunction H ℝ,
      Tendsto (fun n => ∫ ω, f (X n ω) ∂P n) atTop (𝓝 (∫ x, f x ∂Q))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- For [row probability laws](hyp:P), [row random elements](hyp:X), and [a target probability
law](hyp:Q), [bounded-continuous weak convergence is equivalent to convergence in law](goal). -/
theorem weaklyConverges_iff_tendstoInLaw [TopologicalSpace H] [MeasurableSpace H]
    [OpensMeasurableSpace H]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : (n : ℕ) → Ω n → H) (Q : Measure H) [IsProbabilityMeasure Q] :
    WeaklyConverges P X Q ↔ Causalean.Stat.Modes.TendstoInLaw P X atTop Q :=
  (Causalean.Stat.Modes.tendstoInLaw_iff_boundedContinuous P X atTop Q).symm

/-- A real triangular array converges in probability to `c` when, for every positive tolerance,
the probability of an absolute error at least that tolerance tends to zero. -/
@[deprecated "Use Causalean.Stat.Modes.TendstoInProbability." (since := "2026-09-18")]
abbrev TendstoInProbability
    (P : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → ℝ) (c : ℝ) : Prop :=
  Causalean.Stat.Modes.TendstoInProbability P X atTop (fun _ _ => c)

/-- For [row measures](hyp:P), [real row variables](hyp:X), and [a constant target](hyp:c),
[convergence in probability is equivalent to vanishing real absolute-error tails](goal). -/
lemma tendstoInProbability_iff_real
    (P : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → ℝ) (c : ℝ) :
    TendstoInProbability P X c ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => P n {ω | ε ≤ |X n ω - c|}) atTop (𝓝 0) := by
  simpa only [Real.norm_eq_abs] using
    (Causalean.Stat.Modes.tendstoInProbability_iff_norm P X atTop (fun _ _ => c))

/-- A sequence of local statistical experiments with finite-dimensional direction space `H`.
For row `n`, `baseLaw n` is the law at the base point and `localLaw n h` is the law at the fixed
local direction `h` (normally the original parameter is displaced by `h / sqrt n`). -/
structure LocalExperiment (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (H : Type*) [Zero H] where
  /-- Probability law at the base point in each row. -/
  baseLaw : (n : ℕ) → Measure (Ω n)
  /-- Probability law at local direction `h` in each row. -/
  localLaw : (n : ℕ) → H → Measure (Ω n)
  /-- Every base law has total mass one. -/
  base_probability : ∀ n, IsProbabilityMeasure (baseLaw n)
  /-- Every local-alternative law has total mass one. -/
  local_probability : ∀ n h, IsProbabilityMeasure (localLaw n h)
  /-- Local direction zero is the base law in every row. -/
  local_zero : ∀ n, localLaw n 0 = baseLaw n

namespace LocalExperiment

/-- The generalized log likelihood ratio of local direction `h` against the base law is the
logarithm of the real Radon--Nikodym derivative of the local law's absolutely continuous part.
Where that derivative is zero, the extended-real value `-∞` is represented by the diverging
finite truncation `-n`; DQM makes this exceptional event asymptotically negligible. -/
noncomputable def logLikelihoodRatio (E : LocalExperiment Ω H)
    (n : ℕ) (h : H) (ω : Ω n) : ℝ :=
  let r := ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
  if r = 0 then -(n : ℝ) else Real.log r

end LocalExperiment

/-- A local experiment is locally asymptotically normal with central sequence `centralSequence`
and information form `information` when the central sequence has the centered Gaussian
characteristic function determined by `information`, and every fixed-direction log likelihood
ratio equals the linear score term minus half the information quadratic form up to a remainder
converging to zero in base-law probability. -/
structure IsLAN [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (E : LocalExperiment Ω H)
    (centralSequence : (n : ℕ) → Ω n → H)
    (information : LinearMap.BilinForm ℝ H) (gaussianLimit : Measure H) : Prop where
  /-- The central sequence is measurable in every row. -/
  central_measurable : ∀ n, AEMeasurable (centralSequence n) (E.baseLaw n)
  /-- The information form is symmetric. -/
  information_symmetric : information.IsSymm
  /-- The information quadratic form is nonnegative. -/
  information_nonnegative : ∀ h, 0 ≤ information h h
  /-- The Gaussian limit has total mass one. -/
  gaussian_probability : IsProbabilityMeasure gaussianLimit
  /-- The Gaussian limit has characteristic function `exp (-information(t,t)/2)`. -/
  gaussian_charFun : ∀ t : H,
    charFun gaussianLimit t = Complex.exp (-((information t t : ℂ) / 2))
  /-- The central sequence converges weakly to the specified Gaussian law. -/
  central_converges : WeaklyConverges E.baseLaw centralSequence gaussianLimit
  /-- The LAN quadratic expansion holds in base-law probability for every fixed direction. -/
  expansion : ∀ h : H,
    TendstoInProbability E.baseLaw
      (fun n ω => E.logLikelihoodRatio n h ω -
        inner ℝ h (centralSequence n ω) + (1 / 2 : ℝ) * information h h) 0

/-- A scalar estimator has regular limit `limitLaw` with derivative `targetDerivative` when,
under every fixed local direction `h`, its base-centered statistic minus the deterministic local
target shift converges weakly to the same law. -/
structure IsRegularEstimator [TopologicalSpace H]
    (E : LocalExperiment Ω H) (statistic : (n : ℕ) → Ω n → ℝ)
    (targetDerivative : H →ₗ[ℝ] ℝ) (limitLaw : Measure ℝ) : Prop where
  /-- The statistic is a.e. measurable under every local law. -/
  measurable : ∀ n h, AEMeasurable (statistic n) (E.localLaw n h)
  /-- The common centered limit is a probability law. -/
  limit_probability : IsProbabilityMeasure limitLaw
  /-- Centering by the local derivative gives the same weak limit in every fixed direction. -/
  regular : ∀ h : H,
    WeaklyConverges (fun n => E.localLaw n h)
      (fun n ω => statistic n ω - targetDerivative h) limitLaw

/-- A canonical-gradient pairing for a finite-dimensional LAN experiment.  The map `scoreMap`
embeds parameter directions into an ambient `L²`-type Hilbert space `K`; `gradient` belongs to
the score range, the information is the score inner product, and target derivatives are inner
products with the gradient.  Consequently its efficient variance is `‖gradient‖²`. -/
structure CanonicalGradientPairing
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (information : LinearMap.BilinForm ℝ H)
    (targetDerivative : H →ₗ[ℝ] ℝ) (scoreMap : H →ₗ[ℝ] K) (gradient : K) : Prop where
  /-- The canonical gradient belongs to the finite-dimensional score range. -/
  gradient_mem_range : gradient ∈ LinearMap.range scoreMap
  /-- Fisher information is the inner product of embedded scores. -/
  information_eq_inner : ∀ h g, information h g = inner ℝ (scoreMap h) (scoreMap g)
  /-- The pathwise derivative is pairing with the canonical gradient. -/
  derivative_eq_inner : ∀ h, targetDerivative h = inner ℝ gradient (scoreMap h)

/-- Given an information form, a target derivative, a score embedding, and a candidate gradient, [proof that the gradient is in the score range](hyp:hgradient), [that information is the score inner product](hyp:hinfo), and [that the derivative pairs with the gradient](hyp:hderiv) [yield a canonical-gradient pairing](goal). -/
theorem canonicalGradientPairing_of_mem_range
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (information : LinearMap.BilinForm ℝ H) (targetDerivative : H →ₗ[ℝ] ℝ)
    (scoreMap : H →ₗ[ℝ] K) (gradient : K)
    (hgradient : gradient ∈ LinearMap.range scoreMap)
    (hinfo : ∀ h g, information h g = inner ℝ (scoreMap h) (scoreMap g))
    (hderiv : ∀ h, targetDerivative h = inner ℝ gradient (scoreMap h)) :
    CanonicalGradientPairing information targetDerivative scoreMap gradient :=
  { gradient_mem_range := hgradient
    information_eq_inner := hinfo
    derivative_eq_inner := hderiv }

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
