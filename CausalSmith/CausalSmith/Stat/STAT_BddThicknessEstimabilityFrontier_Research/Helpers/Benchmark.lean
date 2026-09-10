import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Estimator
import Causalean.Stat.Minimax.TotalVariation
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Local benchmarks and confidence bands -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @env: S3
variable (n : ℕ) (γ : ℝ) -- @realizes \gamma(miscoverage level in (0,1))

/-- Standing domain of the simultaneous miscoverage level. -/
def AdmissibleMiscoverage (γ : ℝ) : Prop := 0 < γ ∧ γ < 1
  -- @realizes \gamma(0<gamma<1)

/-- Total variation in the paper is Causalean's event-supremum distance. -/
noncomputable def totalVariation {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : ℝ :=
  Causalean.Stat.tvDist μ ν -- @realizes \operatorname{TV}(full-law total variation)

-- @node: def:minimum-side-mass
/-- Minimum of the two one-sided local masses. -/
def minSideMass (P : BoundaryLaw) (x : Score) (h : ℝ) : ℝ≥0∞ :=
  min (localMass P 0 x h) (localMass P 1 x h)
  -- @realizes a_P(min_t q_t,P(x,h))

-- @node: def:local-effective-multiplicity
/-- At least one, or the thin-site packing number at the local mass level. -/
noncomputable def localEffectiveMultiplicity (P : BoundaryLaw) (x : Score) (h : ℝ) : ℕ∞ :=
  max 1 (thinProfile P h (minSideMass P x h))
  -- @realizes K_P(1∨J_P(h,a_P(x,h)))

-- @node: def:local-oracle-benchmark
/-- The finite-grid local bias-stochastic oracle benchmark. -/
noncomputable def localOracleBenchmark (n : ℕ) (P : BoundaryLaw)
    (x : {x // x ∈ assignmentBoundary P})
    (L σ γ h0 : ℝ) : ℝ≥0∞ :=
  ⨅ h : ℝ, ⨅ (_hh : h ∈ dyadicGrid n h0),
    if localMass P 0 x h = 0 ∨ localMass P 1 x h = 0 then ⊤ else
      ENNReal.ofReal (2 * L * h + σ * Real.sqrt ((Real.log
        (Real.exp 1 * ((localEffectiveMultiplicity P x h).getD 0 : ℝ) / γ)) / n *
        ((localMass P 0 x h).toReal⁻¹ + (localMass P 1 x h).toReal⁻¹)))
  -- @realizes r_{n,P}^{\mathrm{loc}}(finite-grid thickness-entropy benchmark)

/-- The calibrated side radius, using the trace envelope at zero count. -/
noncomputable def sideBandRadius {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (t : Fin 2) (x : Score) (L σ γ h0 : ℝ) : ℝ :=
  let h := countAdaptiveBandwidth P w t x L σ h0
  let N := empiricalSideCount P w t x h
  let Mn : ℝ := 2 * (dyadicGrid n h0).card *
    ∑ j ∈ Finset.range 4, Nat.choose n j
  if N = 0 then L else L * h + σ * Real.sqrt (2 * Real.log (2 * Mn / γ) / N)

/-- The calibrated radius computed only from a fixed assignment geometry. -/
noncomputable def geometrySideBandRadius {n : ℕ} (A0 A1 : Set Score) (w : Sample n)
    (t : Fin 2) (x : Score) (L σ γ h0 : ℝ) : ℝ :=
  let h := geometryAdaptiveBandwidth A0 A1 w t x L σ h0
  let N := geometrySideCount A0 A1 w t x h
  let Mn : ℝ := 2 * (dyadicGrid n h0).card *
    ∑ j ∈ Finset.range 4, Nat.choose n j
  if N = 0 then L else L * h + σ * Real.sqrt (2 * Real.log (2 * Mn / γ) / N)

/-- The explicit interval band parametrized by the known geometry, not by a law. -/
noncomputable def geometryHonestBand {n : ℕ} (A0 A1 : Set Score) (w : Sample n)
    (x : Score) (L σ γ h0 : ℝ) : Set ℝ :=
  let center := geometryMassAdaptiveEstimator n A0 A1 L σ h0 w x
  let radius := geometrySideBandRadius A0 A1 w 0 x L σ γ h0 +
    geometrySideBandRadius A0 A1 w 1 x L σ γ h0
  Icc (center - radius) (center + radius)

-- @node: def:honest-band-handle
/-- The explicit globally calibrated interval band. -/
noncomputable def honestBand {n : ℕ} (P : BoundaryLaw) (w : Sample n)
    (x : Score) (L σ γ h0 : ℝ) : Set ℝ :=
  let center := massAdaptiveEstimator P w x L σ h0
  let radius := sideBandRadius P w 0 x L σ γ h0 + sideBandRadius P w 1 x L σ γ h0
  Icc (center - radius) (center + radius)
  -- @realizes \mathcal C_n(boundary-indexed reported interval)

/-- A reported set is a closed interval at every point of the declared boundary. -/
def IntervalValuedOn (B : Set Score) (band : Score → Set ℝ) : Prop :=
  ∀ x ∈ B, ∃ lo hi : ℝ, lo ≤ hi ∧ band x = Icc lo hi

-- @node: def:band-half-width
/-- Half the extended diameter of a reported interval. -/
noncomputable def bandHalfWidth (band : Score → Set ℝ) (x : Score) : ℝ≥0∞ :=
  by
    classical
    exact if ∃ lo hi : ℝ, lo ≤ hi ∧ band x = Icc lo hi then
      Metric.ediam (band x) / 2 else ⊤
  -- @realizes W_n(diameter(C_n(x))/2)

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
