import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Selector
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Multi-sample covariance experiment and augmented regions

Independent Gaussian samples, empirical covariances, and the always-nonempty
augmented target-family confidence construction.
-/

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

variable {d E r : ℕ}

/-- A multi-environment sample on a common probability space. -/
structure SamplingExperiment (d E : ℕ) (n : Environment E → ℕ)
    (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  Y : (e : Environment E) → Fin (n e) → Ω → RealVector d -- @realizes Ye(sample observation Y_ei)

/-- The actual observed sample array.  Its coordinate projections do not
depend on the covariance parameter. -/
abbrev ObservedSampleArray (d E : ℕ) (n : Environment E → ℕ) :=
  (e : Environment E) → Fin (n e) → RealVector d

/-- The sampling experiment on the canonical observed-array space.  Only its
law varies with the covariance tuple; the observation coordinates are fixed. -/
def observedSampleExperiment (P : Measure (ObservedSampleArray d E n)) :
    SamplingExperiment d E n (ObservedSampleArray d E n) where
  P := P
  Y e i x := x e i

/-- Covariance of a not-necessarily-centered random vector. -/
noncomputable def sampleCovariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → RealVector d) : RealMatrix d :=
  fun j k => ∫ ω, Y ω j * Y ω k ∂P

-- @node: ass:independent-environment-samples
def IndependentEnvironmentSamples {Ω : Type*} [MeasurableSpace Ω]
    (X : SamplingExperiment d E n Ω) (θ : CovarianceTuple d E) : Prop :=
  ProbabilityTheory.iIndepFun (fun z : (e : Environment E) × Fin (n e) => X.Y z.1 z.2) X.P ∧
  ∀ e i, Measurable (X.Y e i) ∧
    ProbabilityTheory.IsGaussian (X.P.map (X.Y e i)) ∧
    (∀ j, ∫ ω, X.Y e i ω j ∂X.P = 0) ∧
    sampleCovariance X.P (X.Y e i) = θ.cov e

/-- Empirical covariance statistic in flattened coordinates. -/
noncomputable def empiricalCovariance {Ω : Type*} [MeasurableSpace Ω]
    (X : SamplingExperiment d E n Ω) (ω : Ω) : CovarianceStatistic d E :=
  fun p => (n p.1 : ℝ)⁻¹ * ∑ i, X.Y p.1 i ω p.2.1 * X.Y p.1 i ω p.2.2
  -- @realizes Shat(empirical covariance n_e⁻¹ sum Y_ei Y_ei^T)

/-- Uniform Wishart second-moment bound. -/
def covarianceVarianceBound (d E : ℕ) (M : ℝ) : ℝ :=
  (E + 1 : ℕ) * M ^ 2 * d * (d + 1)
  -- @realizes Vmax((E+1) M² d(d+1))

/-- Markov confidence radius. -/
noncomputable def confidenceRadius (d E : ℕ) (M α : ℝ)
    (_hα : AdmissibleProbabilityLevel α) : ℝ :=
  Real.sqrt (covarianceVarianceBound d E M / α)
  -- @realizes calpha(sqrt(Vmax/alpha)) @realizes alpha(probability level in (0,1))

/-- All sets produced by the augmented confidence construction. -/
structure AugmentedFamilyRegion (d E r : ℕ) where
  rawRegion : Set (CovarianceTuple d E)
  selected : CovarianceTuple d E
  region : Set (CovarianceTuple d E)
  outerFamily : Set (Finset (Fin d))
  classifications : Set (Finset (Fin d) × Finset (Fin d))

-- @node: def:augmented-family-region
noncomputable def augmentedFamilyRegion (d E r : ℕ) (m M α : ℝ)
    (n : Environment E → ℕ) (Shat : CovarianceStatistic d E)
    (hα : AdmissibleProbabilityLevel α)
    (cad : FixedCertifiedCAD d E r n m M 1) : AugmentedFamilyRegion d E r :=
  let Wn : Set (CovarianceTuple d E) :=
    {ζ | BoundedCovarianceMember m M ζ ∧
      weightedDistance n (covarianceCoordinates ζ) Shat ≤ confidenceRadius d E M α hα}
    -- @realizes Wn(raw Loewner-box confidence region)
  let θtilde := canonicalCADSelector cad Shat
    -- @realizes thetatilde(fixed first-cell CAD selector evaluated at Shat)
  let Rn := Wn ∪ {θtilde} -- @realizes Rn(Wn augmented by the feasible selector point)
  let Fout : Set (Finset (Fin d)) :=
    {T | ∃ ζ ∈ Rn ∩ ThetaK d E r m M, T ∈ algebraicTargetFiber ζ r}
    -- @realizes Fout(union of algebraic fibers over Rn intersect ThetaK)
  let Hn : Set (Finset (Fin d) × Finset (Fin d)) :=
    {q | ∃ ζ ∈ Rn ∩ ThetaK d E r m M, completeClassification ζ r = q}
    -- @realizes Hn(classification image over Rn intersect ThetaK)
  { rawRegion := Wn, selected := θtilde, region := Rn,
    outerFamily := Fout, classifications := Hn }

end CausalSmith.ExactID.CovshiftProfilequotientTargets
