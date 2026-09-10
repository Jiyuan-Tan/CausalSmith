import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import Causalean.Stat.Minimax.Pinsker

set_option linter.style.openClassical false

/-!
# Least-favourable exact-slice exponential path

The path preserves all nontarget marginals and product-couples the tilted
assignment-specific outcome marginals.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- Baseline marginal law of the realized outcome vector at assignment `z`. -/
def assignmentMarginal (P0 : Measure (Schedule n)) (z : Assignment n) : Measure (Fin n → ℝ) :=
  P0.map fun Y => Y z
-- @realizes P_{0,z}(P_0 marginal at assignment z)

/-- Assignment marginals of a bounded probability schedule law are probability
laws supported on the bounded outcome cube. -/
def WellFormedAssignmentMarginal (P0 : Measure (Schedule n)) (z : Assignment n) : Prop :=
  WellFormedScheduleLaw P0 ∧ IsProbabilityMeasure (assignmentMarginal P0 z) ∧
    ∀ᵐ y ∂(assignmentMarginal P0 z), ∀ j, y j ∈ Icc (0 : ℝ) 1
-- @realizes P_{0,z}(probability and bounded-support marginal)

/-- Log normalizer of the centered welfare tilt. -/
def logNormalizer (P0 : Measure (Schedule n)) (z : Assignment n) (a : ℝ) : ℝ :=
  Real.log (∫ y, Real.exp (a * ((n : ℝ)⁻¹ * ∑ j, y j - assignmentMean P0 z))
    ∂(assignmentMarginal P0 z))
-- @realizes \Lambda_{z,k}(log E exp{a(W-mu_z)})

/-- Assignment-specific tilted marginal; if `z` is outside every active exact
slice, the tilt exponent is zero and the baseline marginal is retained. -/
def tiltedMarginal (P0 : Measure (Schedule n)) (A : Finset (Fin K))
    (m : Fin K → ℕ) (h : Fin K → ℝ) (t : ℝ) (z : Assignment n) :
    Measure (Fin n → ℝ) :=
  let score := fun y => ∑ k ∈ A,
    if z ∈ exactSlice n (m k) then
      t * h k * ((n : ℝ)⁻¹ * ∑ j, y j - assignmentMean P0 z) /
          sliceVariance P0 (m k) -
        logNormalizer P0 z (t * h k / sliceVariance P0 (m k))
    else 0
  (assignmentMarginal P0 z).withDensity fun y => ENNReal.ofReal (Real.exp (score y))
-- @realizes P_{t,h,z}(exponential tilt on active exact slices; baseline otherwise)

/-- The exponential tilt is normalized and retains bounded support at every path point. -/
def WellFormedTiltedMarginal (P0 : Measure (Schedule n)) (A : Finset (Fin K))
    (m : Fin K → ℕ) (h : Fin K → ℝ) (t : ℝ) (z : Assignment n) : Prop :=
  WellFormedAssignmentMarginal P0 z ∧ IsProbabilityMeasure (tiltedMarginal P0 A m h t z) ∧
    (tiltedMarginal P0 A m h t z) Set.univ = 1 ∧
    ∀ᵐ y ∂(tiltedMarginal P0 A m h t z), ∀ j, y j ∈ Icc (0 : ℝ) 1
-- @realizes P_{t,h,z}(normalized probability tilt with bounded support)

-- @node: def:least-favourable-path
/-- Product-coupled least-favourable schedule law at scale `t`.  Setting
`t = C⁻¹/²` gives the local sequence used by the LAN theorems. -/
def leastFavourablePath (P0 : Measure (Schedule n)) (A : Finset (Fin K))
    (m : Fin K → ℕ) (h : Fin K → ℝ) (t : ℝ) : Measure (Schedule n) :=
  Measure.pi fun z : Assignment n => tiltedMarginal P0 A m h t z
-- @realizes \bar P_0(product coupling at t=0)
-- @realizes h(full representative local displacement, common shift retained)
-- @realizes \bar P_{t,h}(product of P_{t,h,z})
-- @realizes \bar P_{C,h}(leastFavourablePath at t=C⁻¹/²)

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
