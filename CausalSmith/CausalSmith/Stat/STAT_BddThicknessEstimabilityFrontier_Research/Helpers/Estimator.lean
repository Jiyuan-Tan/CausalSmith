import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Basic
import Causalean.Stat.Minimax.MinimaxRisk
import Causalean.Mathlib.Analysis.ClipInterval
import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Mathlib.Data.Finset.Filter

/-! # Count-adaptive estimation and minimax risk -/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @env: S2
variable (n : ℕ) (L σ h0 : ℝ)

-- @node: def:dyadic-grid
/-- The finite dyadic grid through the ceiling of `log₂ n`. -/
noncomputable def dyadicGrid (n : ℕ) (h0 : ℝ) : Finset ℝ :=
  if 1 ≤ n ∧ 0 < h0 ∧ h0 < 1 then
    (Finset.range (⌈Real.log n / Real.log 2⌉₊ + 1)).image
      (fun j : ℕ => (2 : ℝ) ^ (-(j : ℝ)) * h0)
  else ∅
  -- @realizes \mathcal H_n({2^-j h₀: 0≤j≤ceil(log₂ n)})

-- @node: def:empirical-counts
/-- The empirical number of observations in a side-specific boundary ball. -/
noncomputable def empiricalSideCount {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (t : Fin 2) (x : Score) (h : ℝ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter fun i =>
    (w i).2 ∈ P.region t ∧ dist (w i).2 x ≤ h).card
  -- @realizes N_{t,n}(sum of side-ball indicators)

-- @node: def:local-constant-side-fit
/-- The guarded local-constant side average, equal to zero for an empty disk. -/
noncomputable def localConstantSideFit {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (t : Fin 2) (x : Score) (h : ℝ) : ℝ := by
  classical
  exact ((max (empiricalSideCount P w t x h) 1 : ℕ) : ℝ)⁻¹ *
    ∑ i : Fin n, if (w i).2 ∈ P.region t ∧ dist (w i).2 x ≤ h then (w i).1 else 0
  -- @realizes \widehat g_{t,n}(guarded side-specific empirical mean)

-- @node: def:admissible-bandwidths
/-- Grid bandwidths whose empirical count clears the logarithmic threshold. -/
noncomputable def admissibleBandwidths {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (t : Fin 2) (x : Score) (h0 : ℝ) : Finset ℝ := by
  classical
  exact (dyadicGrid n h0).filter fun h =>
    8 * Real.log (Real.exp 1 + n / h) ≤ empiricalSideCount P w t x h
  -- @realizes \widehat{\mathcal H}_{t,n}(count-qualified bandwidth set)

/-- Bias-plus-noise criterion used for bandwidth selection. -/
noncomputable def bandwidthCriterion {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (t : Fin 2) (x : Score) (L σ h : ℝ) : ℝ :=
  L * h + σ * Real.sqrt (Real.log (Real.exp 1 + n / h) /
    max (empiricalSideCount P w t x h) 1)

-- @node: def:count-adaptive-bandwidth
/-- Lexicographic minimization of `(criterion,h)` gives the numerically smallest
criterion minimizer, with `h0` as the empty-set fallback. -/
noncomputable def countAdaptiveBandwidth {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (t : Fin 2) (x : Score) (L σ h0 : ℝ) : ℝ := by
  classical
  let A := admissibleBandwidths P w t x h0
  if hA : A.Nonempty then
    exact sInf {h : ℝ | h ∈ A ∧
      ∀ k ∈ A, bandwidthCriterion P w t x L σ h ≤
        bandwidthCriterion P w t x L σ k}
  else exact h0
  -- @realizes \widehat h_{t,n}(smallest argmin with h₀ fallback)

-- @node: def:mass-adaptive-estimator
/-- Difference of the two count-adaptive side fits. -/
noncomputable def massAdaptiveEstimator {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (x : Score) (L σ h0 : ℝ) : ℝ :=
  localConstantSideFit P w 1 x (countAdaptiveBandwidth P w 1 x L σ h0) -
    localConstantSideFit P w 0 x (countAdaptiveBandwidth P w 0 x L σ h0)
  -- @realizes \widehat\tau_n(difference of adaptive side fits)

/-- The side region selected from a fixed assignment geometry. -/
def fixedGeometryRegion (A0 A1 : Set Score) (t : Fin 2) : Set Score :=
  if t = 0 then A0 else A1

/-- Geometry-parametrized empirical side count. -/
noncomputable def geometrySideCount {n : ℕ} (A0 A1 : Set Score) (w : Sample n)
    (t : Fin 2) (x : Score) (h : ℝ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter fun i =>
    (w i).2 ∈ fixedGeometryRegion A0 A1 t ∧ dist (w i).2 x ≤ h).card

/-- Geometry-parametrized local-constant side fit. -/
noncomputable def geometrySideFit {n : ℕ} (A0 A1 : Set Score) (w : Sample n)
    (t : Fin 2) (x : Score) (h : ℝ) : ℝ := by
  classical
  exact ((max (geometrySideCount A0 A1 w t x h) 1 : ℕ) : ℝ)⁻¹ *
    ∑ i : Fin n,
      if (w i).2 ∈ fixedGeometryRegion A0 A1 t ∧ dist (w i).2 x ≤ h then
        (w i).1 else 0

/-- Count-qualified bandwidths computed from the fixed geometry alone. -/
noncomputable def geometryAdmissibleBandwidths {n : ℕ} (A0 A1 : Set Score)
    (w : Sample n) (t : Fin 2) (x : Score) (h0 : ℝ) : Finset ℝ := by
  classical
  exact (dyadicGrid n h0).filter fun h =>
    8 * Real.log (Real.exp 1 + n / h) ≤ geometrySideCount A0 A1 w t x h

/-- Bias-noise criterion for a geometry-parametrized side fit. -/
noncomputable def geometryBandwidthCriterion {n : ℕ} (A0 A1 : Set Score)
    (w : Sample n) (t : Fin 2) (x : Score) (L σ h : ℝ) : ℝ :=
  L * h + σ * Real.sqrt (Real.log (Real.exp 1 + n / h) /
    max (geometrySideCount A0 A1 w t x h) 1)

/-- The deterministic count-adaptive bandwidth based only on known geometry. -/
noncomputable def geometryAdaptiveBandwidth {n : ℕ} (A0 A1 : Set Score)
    (w : Sample n) (t : Fin 2) (x : Score) (L σ h0 : ℝ) : ℝ := by
  classical
  let A := geometryAdmissibleBandwidths A0 A1 w t x h0
  if hA : A.Nonempty then
    exact sInf {h : ℝ | h ∈ A ∧
      ∀ k ∈ A, geometryBandwidthCriterion A0 A1 w t x L σ h ≤
        geometryBandwidthCriterion A0 A1 w t x L σ k}
  else exact h0

/-- The paper's common estimator, parametrized only by the known geometry. -/
noncomputable def geometryMassAdaptiveEstimator (n : ℕ) (A0 A1 : Set Score)
    (L σ h0 : ℝ) : Sample n → Score → ℝ :=
  fun w x =>
    geometrySideFit A0 A1 w 1 x (geometryAdaptiveBandwidth A0 A1 w 1 x L σ h0) -
      geometrySideFit A0 A1 w 0 x (geometryAdaptiveBandwidth A0 A1 w 0 x L σ h0)

/-- The fixed clipped estimator used in every arbitrary-modulus guarantee. -/
noncomputable def clippedGeometryMassAdaptiveEstimator (n : ℕ) (A0 A1 : Set Score)
    (L σ h0 : ℝ) : Sample n → Score → ℝ :=
  fun w x => Causalean.Mathlib.Analysis.clipIcc (-2 * L) (2 * L)
    (geometryMassAdaptiveEstimator n A0 A1 L σ h0 w x)

-- @node: def:arbitrary-modulus-handle
/-- The count-adaptive estimator projected onto `[-2L,2L]`. -/
noncomputable def clippedMassAdaptiveEstimator {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (x : Score) (L σ h0 : ℝ) : ℝ :=
  Causalean.Mathlib.Analysis.clipIcc (-2 * L) (2 * L)
    (massAdaptiveEstimator P w x L σ h0)

/-- The product law of `n` observed units. -/
noncomputable def observedSampleLaw (P : BoundaryLaw) (n : ℕ) : Measure (Sample n) := by
  letI := P.isProbability_observed
  exact Measure.pi (fun _ : Fin n => P.observedLaw)

/-- Function-valued estimators used in the expected-sup risk. -/
abbrev BoundaryEstimator (n : ℕ) := Sample n → Score → ℝ

/-- Estimators measurable in the sample, pointwise on the known boundary geometry. -/
def MeasurableBoundaryEstimator {n : ℕ} (estimator : BoundaryEstimator n) : Prop :=
  ∀ x : Score, Measurable fun w => estimator w x

/-- Expected boundary supremum loss of one estimator under one law. -/
noncomputable def estimatorExpectedSupLoss {n : ℕ} (estimator : BoundaryEstimator n)
    (P : BoundaryLaw) : ℝ≥0∞ :=
  ∫⁻ w, ⨆ x : Score, ⨆ (_hx : x ∈ assignmentBoundary P),
    ENNReal.ofReal |estimator w x - traceContrast P x| ∂observedSampleLaw P n

-- @node: def:expected-sup-risk
/-- Infimum over estimators of worst-law expected boundary supremum loss. -/
noncomputable def expectedSupMinimaxRisk (n : ℕ) (laws : Set BoundaryLaw) : ℝ≥0∞ :=
  by
    classical
    exact if laws.Nonempty then
      ⨅ estimator : BoundaryEstimator n,
        ⨅ (_hmeas : MeasurableBoundaryEstimator estimator),
          ⨆ P : BoundaryLaw, ⨆ (_hP : P ∈ laws), estimatorExpectedSupLoss estimator P
    else ⊤
  -- @realizes R_n(expected-sup minimax risk)

/-- The isolated-thinning polynomial frontier rate. -/
noncomputable def isolatedRate (n : ℕ) (κ : ℝ) : ℝ :=
  n ^ (-(1 / (κ + 2)))
  -- @realizes r_{n,\kappa}^{\mathrm{iso}}(n^-1/(kappa+2))

/-- The pervasive-thinning logarithmic frontier rate. -/
noncomputable def pervasiveRate (n : ℕ) (κ : ℝ) : ℝ :=
  (Real.log n / n) ^ (1 / (κ + 2))
  -- @realizes r_{n,\kappa}^{\mathrm{perv}}((log n/n)^1/(kappa+2))

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
