import Mathlib.Probability.Distributions.Gaussian.Basic
import Causalean.Mathlib.StandardGaussian
import Causalean.Mathlib.Probability.StdNormalCDF
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Sampling

/-! # Geometry-indexed Gaussian local power envelope

The Gaussian shift experiment, honest randomized certification rules, their
optimal focal power, and the scalar nearest-opposite summary.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @env: S4
variable {k : ℕ}

/-- Tangent geometry retained by the local experiment. -/
structure TangentGeometry where
  k : ℕ
  focal : EuclideanSpace ℝ (Fin k)
  opposite : Set (EuclideanSpace ℝ (Fin k))
  -- @realizes Gtan(k-dimensional focal and opposite tangent geometry)

/-- Gaussian shift law `N(g,I_k)`. -/
noncomputable def gaussianShiftLaw (G : TangentGeometry)
    (g : EuclideanSpace ℝ (Fin G.k)) : Measure (EuclideanSpace ℝ (Fin G.k)) :=
  (Causalean.Mathlib.stdGaussian (EuclideanSpace ℝ (Fin G.k))).map (fun x => x + g)

/-- A Borel randomized rule valued in `[0,1]`. -/
def IsRandomizedRule (G : TangentGeometry)
    (φ : EuclideanSpace ℝ (Fin G.k) → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, 0 ≤ φ x ∧ φ x ≤ 1

/-- Honesty on every opposite-classification tangent. -/
def IsHonestRule (G : TangentGeometry) (α : ℝ)
    (φ : EuclideanSpace ℝ (Fin G.k) → ℝ) : Prop :=
  IsRandomizedRule G φ ∧
    ∀ g ∈ G.opposite, ∫ x, φ x ∂gaussianShiftLaw G g ≤ α

/-- Optimal correct-certification probability at the focal shift. -/
noncomputable def gaussianPowerSupremum (G : TangentGeometry) (α : ℝ) : ℝ :=
  sSup {b | ∃ φ : EuclideanSpace ℝ (Fin G.k) → ℝ,
    IsHonestRule G α φ ∧ b = ∫ x, φ x ∂gaussianShiftLaw G G.focal}

/-- Nearest-opposite tangent distance. -/
noncomputable def nearestOppositeDistance (G : TangentGeometry) : ℝ :=
  sInf {c | ∃ g ∈ G.opposite, c = ‖g - G.focal‖}
  -- @realizes clocal(nearest-opposite scalar summary c)

/-- Weak convergence, written through bounded continuous test functions. -/
def WeaklyConverges {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  ∀ f : X → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun q => ∫ x, f x ∂μ q) atTop (nhds (∫ x, f x ∂ν))

/-- Log likelihood ratio in the limiting Gaussian shift experiment, relative
to the focal shift. -/
noncomputable def gaussianLogLikelihoodRatio (G : TangentGeometry)
    (g x : EuclideanSpace ℝ (Fin G.k)) : ℝ :=
  inner ℝ (g - G.focal) (x - G.focal) - (1 / 2 : ℝ) * ‖g - G.focal‖ ^ 2

/-- A regular covariance sequence genuinely derives the asserted Gaussian
local experiment: its parameter-independent observed arrays have Gaussian
covariance laws, exact likelihood ratios, and joint finite-dimensional LAN
convergence to the Gaussian-shift likelihood-ratio process. -/
structure GaussianLocalExperimentDerivation (G : TangentGeometry) where
  ambientDim : ℕ
  environmentTotal : ℕ
  targetCount : ℕ
  lowerBound : ℝ
  upperBound : ℝ
  dimension : AdmissibleDimension ambientDim
  environmentCount : AdmissibleEnvironmentCount environmentTotal
  targetSize : AdmissibleTargetSize ambientDim targetCount
  covarianceBounds : 0 < lowerBound ∧ lowerBound < upperBound
  nSeq : ℕ → Environment environmentTotal → ℕ
  samplesPositive : ∀ q e, 0 < nSeq q e
  samplesDiverge : ∀ e, Tendsto (fun q => nSeq q e) atTop atTop
  localCovariance : ℕ → EuclideanSpace ℝ (Fin G.k) →
    CovarianceTuple ambientDim environmentTotal
  localMember : ∀ q g, g = G.focal ∨ g ∈ G.opposite →
    localCovariance q g ∈
      ThetaK ambientDim environmentTotal targetCount lowerBound upperBound
  sampleLaw : (q : ℕ) → EuclideanSpace ℝ (Fin G.k) →
    Measure (ObservedSampleArray ambientDim environmentTotal (nSeq q))
  gaussianSampling : ∀ q g, g = G.focal ∨ g ∈ G.opposite →
    IndependentEnvironmentSamples
      (observedSampleExperiment (sampleLaw q g)) (localCovariance q g)
  focalClassification : Finset (Fin ambientDim) × Finset (Fin ambientDim)
  focalClassificationStable : ∀ q,
    completeClassification (localCovariance q G.focal) targetCount = focalClassification
  oppositeClassification : ∀ q g, g ∈ G.opposite →
    completeClassification (localCovariance q g) targetCount ≠ focalClassification
  logLikelihoodRatio : (q : ℕ) → EuclideanSpace ℝ (Fin G.k) →
    ObservedSampleArray ambientDim environmentTotal (nSeq q) → ℝ
  logLikelihoodMeasurable : ∀ q g, Measurable (logLikelihoodRatio q g)
  likelihoodRatioIdentity : ∀ q g, g = G.focal ∨ g ∈ G.opposite →
    sampleLaw q g = (sampleLaw q G.focal).withDensity
      (fun y => ENNReal.ofReal (Real.exp (logLikelihoodRatio q g y)))
  likelihoodRatiosConverge : ∀
      (s : Finset (EuclideanSpace ℝ (Fin G.k))),
    (∀ g ∈ s, g = G.focal ∨ g ∈ G.opposite) →
    WeaklyConverges
      (fun q => (sampleLaw q G.focal).map (fun y (g : {g // g ∈ s}) =>
        logLikelihoodRatio q g.1 y))
      ((gaussianShiftLaw G G.focal).map (fun x (g : {g // g ∈ s}) =>
        gaussianLogLikelihoodRatio G g.1 x))

/-- The anchored power-envelope object retains its inducing regular sequence,
admissible level, nearest-boundary summary, and full geometry-indexed optimum. -/
structure PowerEnvelopeHandle (G : TangentGeometry) where
  derivation : GaussianLocalExperimentDerivation G
  level : ℝ
  levelAdmissible : AdmissibleProbabilityLevel level
  nearestBoundary : ℝ
  nearestBoundary_eq : nearestBoundary = nearestOppositeDistance G
  value : ℝ
  value_eq : value = gaussianPowerSupremum G level

-- @node: def:power-envelope-handle
noncomputable def powerEnvelope (G : TangentGeometry)
    (D : GaussianLocalExperimentDerivation G) (α : ℝ)
    (hα : AdmissibleProbabilityLevel α) : PowerEnvelopeHandle G where
  derivation := D
  level := α
  levelAdmissible := hα
  nearestBoundary := nearestOppositeDistance G
  nearestBoundary_eq := rfl
  value := gaussianPowerSupremum G α
  value_eq := rfl
  -- @realizes betastar(geometry-indexed optimal honest focal power)
  -- @realizes clocal(retained nearest-boundary summary)

end CausalSmith.ExactID.CovshiftProfilequotientTargets
