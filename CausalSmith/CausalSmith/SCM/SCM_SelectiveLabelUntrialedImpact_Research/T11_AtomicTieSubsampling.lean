import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T7_ProjectionDirectionalLimit
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T9_FanBerryEsseen
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T10_AtomicTieCertificate
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.AtomicTieSubsampling
import Mathlib.Order.LiminfLimsup

set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! # Atomic-tie subsampling validity with the global-sign argument -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter

variable {O T OBlind K R : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [Fintype K] [Fintype R] [DecidableEq O] [DecidableEq T]
  [DecidableEq OBlind] [DecidableEq K] [DecidableEq R]

/-- The effective support of a multinomial fluctuation. -/
def multinomialEffectiveSpace (p : O → ℝ) : Set (O → ℝ) :=
  {g | (∑ o, g o = 0) ∧ ∀ o, p o = 0 → g o = 0}

/-- Nondegeneracy of the multinomial covariance on its effective support. -/
def MultinomialNondegenerate (p : O → ℝ) : Prop :=
  ∀ v ∈ multinomialEffectiveSpace p, v ≠ 0 →
    0 < ∑ i, ∑ j, v i * multinomialCovariance p i j * v j

/-- The local finite-polyhedral fan assumptions made explicitly in the atomic
theorem: exact local representation, linearity cone by cone, and nonzero
retained restrictions on the effective support. -/
def AtomicTieFanConditions (G : SLCCIncidence O T OBlind) (p : O → ℝ)
    (fan : Finset (Set (O → ℝ))) (restrictions : Finset (O → ℝ)) : Prop :=
  (∃ epsilon : ℝ, 0 < epsilon ∧ ∀ x, ‖x‖ < epsilon →
    sharpEndpointPrograms G (metricProjection (observablePolytope G) (p + x)) -
      sharpEndpointPrograms G p = projectionComposedDerivative G p x) ∧
  (∀ cone ∈ fan, ∃ lower upper : (O → ℝ) →ₗ[ℝ] ℝ,
    ∀ x ∈ cone, projectionComposedDerivative G p x = (lower x, upper x)) ∧
  (∀ r ∈ restrictions, ∃ v ∈ multinomialEffectiveSpace p,
    (∑ o, r o * v o) ≠ 0)

/-- Empirical law computed on a chosen subset of the first `n` observations. -/
noncomputable def subsampleEmpiricalLaw
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) {n : ℕ}
    (A : Finset (Fin n)) (ω : Ω) (o : O) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ i ∈ A, if S.Z i ω = o then 1 else 0

/-- The max of the two centered projected-endpoint subsampling statistics. -/
noncomputable def subsampleEndpointStatistic
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (G : SLCCIncidence O T OBlind)
    (n : ℕ) (A : Finset (Fin n)) (ω : Ω) : ℝ :=
  let sub := projectionEndpointEstimator G (subsampleEmpiricalLaw S A ω)
  let full := projectionEndpointEstimator G (empiricalLaw S n ω)
  max (Real.sqrt A.card * (sub.1 - full.1))
    (Real.sqrt A.card * (full.2 - sub.2))

/-- The finite conditional law obtained by uniformly ranging over all
size-`m_n` subsets without replacement. -/
noncomputable def conditionalSubsamplingLaw
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (G : SLCCIncidence O T OBlind)
    (n : ℕ) (ω : Ω) : Measure ℝ :=
  let choices := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun A => A.card = subsampleSize n)
  if h : choices.Nonempty then
    (choices.card : ℝ≥0∞)⁻¹ • ∑ A ∈ choices, Measure.dirac (subsampleEndpointStatistic S G n A ω)
  else Measure.dirac 0

/-- The lower conditional quantile at the paper's explicit slackened level. -/
noncomputable def atomicSubsamplingCriticalValue
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (G : SLCCIncidence O T OBlind)
    (alpha : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sInf {x | ENNReal.ofReal (1 - alpha + quantileSlack n alpha) ≤
    conditionalSubsamplingLaw S G n ω (Set.Iic x)}
  -- @realizes c_sub(lower conditional (1-alpha+eta_n)-quantile)

/-- The event that the subsampling-expanded plug-in interval covers both
sharp endpoints. -/
def atomicSubsamplingCoverageEvent
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) (alpha : ℝ) (n : ℕ) : Set Ω :=
  {ω | lowerEndpoint G p ≥
      (projectionEndpointEstimator G (empiricalLaw S n ω)).1 -
        atomicSubsamplingCriticalValue S G alpha n ω / Real.sqrt n ∧
    upperEndpoint G p ≤
      (projectionEndpointEstimator G (empiricalLaw S n ω)).2 +
        atomicSubsamplingCriticalValue S G alpha n ω / Real.sqrt n}

/-- Pointwise validity at polyhedral ties.  The only paper assumption threaded
into the signature is the reused i.i.d. sampling atom; the Berry--Esseen cited
gate is exposed on its direct consumer in `T9_FanBerryEsseen`. -/
-- @node: thm:atomic-tie-subsampling-validity-global-sign
theorem atomic_tie_subsampling_validity_global_sign
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [MeasurableSingletonClass O] {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) (hIID : IidFiniteSampling μ P S G p)
    (fan : Finset (Set (O → ℝ))) (restrictions : Finset (O → ℝ))
    (M : K → Matrix R O ℝ) (alpha : ℝ) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hFan : AtomicTieFanConditions G p fan restrictions)
    (hNondegenerate : MultinomialNondegenerate p) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
      fanApproximationError S p (multinomialGaussianLaw p) M m ≤
        C * (Real.sqrt m)⁻¹) ∧
    (∀ x : ℝ, (multinomialGaussianLaw p)
      {g | endpointLimitStatistic
        (fun z => (projectionComposedDerivative G p z).1)
        (fun z => (projectionComposedDerivative G p z).2) g = x} ≠ 0 → x = 0) ∧
    1 - alpha ≤ Filter.liminf (fun n => ENNReal.toReal
      (μ (atomicSubsamplingCoverageEvent S G p alpha n))) Filter.atTop ∧
    0 < ENNReal.toReal ((multinomialGaussianLaw witness32PDagger)
      {g | witness32LimitStatistic g = 0}) ∧
    ENNReal.toReal ((multinomialGaussianLaw witness32PDagger)
      {g | witness32LimitStatistic g = 0}) < 1 := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
