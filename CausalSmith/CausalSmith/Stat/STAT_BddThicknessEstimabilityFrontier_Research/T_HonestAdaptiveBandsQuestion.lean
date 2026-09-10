import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_GlobalHonestBand

/-! # Open local-oracle honest-band question -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- The component class selected by one profile triple. -/
def profileComponent {κbar : ℝ} (a : ProfileTriple κbar) (L σ cm h0 : ℝ) : Set BoundaryLaw :=
  {P | ProfileBracket P a L σ cm h0}

/-- Uniform expected pointwise width divided by the local oracle. -/
noncomputable def localWidthRatio (band : BandSequence) (n : ℕ)
    (laws : Set BoundaryLaw) (L σ γ h0 : ℝ) : ℝ≥0∞ :=
  ⨆ P : BoundaryLaw, ⨆ (_hP : P ∈ laws), ⨆ x : Score,
    ⨆ (_hx : x ∈ assignmentBoundary P),
      (∫⁻ w, bandHalfWidth (band n w) x ∂observedSampleLaw P n) /
        localOracleBenchmark n P ⟨x, _hx⟩ L σ γ h0

-- @node: oeq:honest-adaptive-bands
/-- A descriptive payload for the unresolved honest-adaptation problem.
It records the requested regimes and alternatives without inventing definitions
of benchmark separation or triangular profile-pair distinguishability. -/
def HonestAdaptiveBandsQuestion : _root_.String :=
  "Open problem on nonempty triangular profile unions: characterize whether a \
  data-measurable interval band can have simultaneous coverage 1-gamma-o(1) and \
  uniformly bounded expected half-width divided by the local thickness-entropy \
  benchmark; prove the matching universal-positive-constant honest-width lower \
  bound; and, if that upper target is impossible, define and characterize exactly \
  which eventually present triangular profile pairs are separated by their benchmark \
  functions and must have uniformly distinguishable product score laws in total \
  variation. The notions of benchmark separation and admissible triangular \
  profile-pair quantification are intentionally left to be characterized, so this \
  payload asserts no equivalence and supplies no witnesses."

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
