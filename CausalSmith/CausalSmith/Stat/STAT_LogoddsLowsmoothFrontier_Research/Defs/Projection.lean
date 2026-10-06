module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Cosine projections and original-record ordered-pair statistics -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @env: S3
variable (k n : ℕ)
/-- Cosine basis with the constant frequency separated. -/
def cosineBasis (j : ℕ) (x : Covariate) : ℝ :=
  if j = 0 then 1 else Real.sqrt 2 * Real.cos (Real.pi * j * (x : ℝ))
  -- @realizes \varphi(cosine basis) @realizes j(natural frequency index)
/-- Inner product against the public uniform design. -/
def uniformInner (f g : Covariate → ℝ) : ℝ := ∫ x, f x * g x ∂uniformLaw
/-- Rank-k cosine projection. -/
def cosineProjection (k : ℕ) (f : Covariate → ℝ) (x : Covariate) : ℝ :=
  ∑ j ∈ Finset.range k, uniformInner f (cosineBasis j) * cosineBasis j x
  -- @realizes \Pi(rank-k orthogonal projection) @realizes k(natural basis rank)
/-- Projection kernel. -/
def projectionKernel (k : ℕ) (x z : Covariate) : ℝ :=
  ∑ j ∈ Finset.range k, cosineBasis j x * cosineBasis j z -- @realizes H(cosine projection kernel)
/-- Borel marks valued in the unit interval. -/
structure BoundedMark where
  value : Record → ℝ -- @realizes W(real mark) @realizes V(real mark)
  measurable_value : Measurable value
  range_value : ∀ o, 0 ≤ value o ∧ value o ≤ 1
/-- Conditional mean computed from the actual four-cell kernel. -/
def conditionalMarkMean (P : ObservedLaw) (W : BoundedMark) (x : Covariate) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, P.cells a y x * W.value (x, a, y)
  -- @realizes w(conditional mark mean) @realizes v(conditional second-mark mean)
-- @node: def:projection-statistic
/-- Ordered distinct pairs, with the asymmetric marked kernel. -/
def projectionStatistic (n k : ℕ) (W V : Record → ℝ) (o : Fin n → Record) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
    ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2),
      projectionKernel k (covariate (o ij.1)) (covariate (o ij.2)) * W (o ij.1) * V (o ij.2)
  -- @realizes \mathbb U(ordered-pair statistic)
/-- Uniform L2 norm, with extended semantics. -/
def uniformL2Norm (f : Covariate → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂uniformLaw).rpow (1 / 2)
end CausalSmith.Stat.LogoddsLowsmoothFrontier
