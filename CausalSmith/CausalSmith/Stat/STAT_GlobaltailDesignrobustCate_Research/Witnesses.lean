module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Least-favorable and hostile designs

The binary witness uses a smooth one-sided cutoff on the covariate cube, with
value one at its lower corner. Support is relative to the cube, since an ambient
continuous function supported in `[0,1)^d` cannot equal one at the boundary zero.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal BigOperators

-- @env: S4
variable (d : ℕ) (q : ℝ) -- @realizes d(covariate dimension) @realizes q(positive tail exponent)

/-- Maximum covariate coordinate. -/
noncomputable def maxCoordinate {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  sSup (Set.range x)

/-- Baseline power propensity. -/
noncomputable def baselinePropensity (d : ℕ) (q : ℝ) (x : Fin d → ℝ) : ℝ :=
  (maxCoordinate x) ^ ((d : ℝ) / q) -- @realizes e0(max-coordinate power propensity)

/-- Smooth upper-face cutoff, normalized to one at zero. -/
noncomputable def bump1 (t : ℝ) : ℝ :=
  if t < 1 / 2 then Real.exp (-t / (1 / 2 - t)) else 0

/-- Tensor bump on the unit cube, equal to one at its lower corner. -/
noncomputable def witnessBump (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, bump1 (x i)

/-- Binary law with values `±M/2` and nominal plus probability `p`. -/
noncomputable def binaryMeasure (M p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (M / 2) +
    ENNReal.ofReal (1 - p) • Measure.dirac (-M / 2)

/-- Bernoulli treatment law. -/
noncomputable def treatmentMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true +
    ENNReal.ofReal (1 - p) • Measure.dirac false

/-- Signed treated mean bump. -/
noncomputable def witnessMean (d : ℕ) (β δ h : ℝ) (sign : Bool)
    (x : Fin d → ℝ) : ℝ :=
  (if sign then 1 else -1) * δ * h ^ β * witnessBump d (fun i => x i / h)

/-- Conditional probability that `Y(1)=M/2`. -/
noncomputable def treatedPlusProbability (d : ℕ) (β δ h M : ℝ)
    (sign : Bool) (x : Fin d → ℝ) : ℝ :=
  (1 + 2 * witnessMean d β δ h sign x / M) / 2

-- @node: def:lower-pair
/-- Full bounded binary-outcome witness law, indexed by the sign. The
construction samples uniform `X`, then Bernoulli treatment, then symmetric
`Y(0)` and the signed-mean binary `Y(1)`. -/
noncomputable def lowerPair (d : ℕ) (β q h δ M : ℝ) (sign : Bool) : Law d :=
  let fullMeasure : Measure (Full d) :=
    (volume.restrict (cube d)).bind (fun x =>
      (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
            (fun y1 => (x, a, y0, y1)))))
  { full := fullMeasure
    observed := fullMeasure.map observe
    observedRecord := observe
    latentSample := fun n => Measure.pi (fun _ : Fin n => fullMeasure)
    sample := fun n => Measure.pi (fun _ : Fin n => fullMeasure.map observe)
    e := baselinePropensity d q
    mu1 := witnessMean d β δ h sign
    mu0 := fun _ => 0 }
  -- @realizes Pplus(positive sign witness) @realizes Pminus(negative sign witness)

/-- Cube at hostile scale `j`. -/
noncomputable def hostileCube (d j : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i : Fin d, (4 : ℝ) ^ (-(j : ℤ)) ≤ x i ∧
    x i ≤ 2 * (4 : ℝ) ^ (-(j : ℤ))}

/-- Centered first-coordinate slab, as a fraction of cube width. -/
noncomputable def hostileSlab (d j : ℕ) (q : ℝ) : Set (Fin d → ℝ) :=
  {x | x ∈ hostileCube d j ∧
    (if hd : 0 < d then
      |(x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
        ((4 : ℝ) ^ (-(j : ℤ))) - 1 / 2| ≤
          ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) / 2
     else False)}

-- @node: def:hostile-propensity
/-- Baseline propensity raised to one on disjoint shrinking thin slabs. -/
noncomputable def hostilePropensity (d : ℕ) (q : ℝ) (x : Fin d → ℝ) : ℝ :=
  by
    classical
    exact if ∃ j : ℕ, 1 ≤ j ∧ x ∈ hostileSlab d j q then 1
      else baselinePropensity d q x
  -- @realizes ehos(thin-slab hostile propensity)

end CausalSmith.Stat.GlobalTailDesignRobustCate
