module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Basic
public import Mathlib.Data.Finset.Basic

/-! # Certified staircase support regions

The two support regimes are instances of one finite primal and strict dual
certificate predicate. The pattern numbers follow the four-bit enumeration. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

/-- For the supplied quantities and conditions, the pattern information slope is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The pattern Information Slope](goal) is determined by [the displayed parameters](hyp:θ,p,ε,s,t). -/
def patternInformationSlope (θ : TrialParameter) (p ε : ℝ)
    (s : Fin 14) (t : ℝ) : ℝ :=
  2 * projectedGradient p ε s t *
    (patternGradient p ε s 0 + patternGradient p ε s 1) /
    patternMass θ p ε s

/-- For the supplied quantities and conditions, the dual ray is the mathematical object specified below. [The dual Ray](goal) is determined by [the displayed parameters](hyp:ε,η,s). -/
def dualRay (ε : ℝ) (η : Fin 4 → ℝ) (s : Fin 14) : ℝ :=
  ∑ j : Fin 4, patternRay ε s j * η j

/-- the active support is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The active Support](goal) is determined by [the displayed parameters](hyp:α,K). -/
def activeSupport (α : StaircaseWeight) (K : Finset (Fin 14)) : Prop :=
  ∀ s, (α s ≠ 0 ↔ s ∈ K)

-- @node: def:support-regions
/-- For [the supplied quantities and conditions](hyp:distinct), the [certified region](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:K), these specify the stated inputs. -/
def certifiedRegion (K : Finset (Fin 14)) (distinct : Bool) :
    Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | let p := x.1
       let μ0 := x.2.1
       let μ1 := x.2.2.1
       let ε := x.2.2.2
       let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
       0 < p ∧ p < 1 ∧
       0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧
       ∃ α : StaircaseWeight, ∃ t : ℝ, ∃ η : Fin 4 → ℝ,
         -- @realizes \eta(four-coordinate dual certificate)
         staircaseFeasible ε α ∧
         activeSupport α K ∧
         (∀ s ∈ K, 0 < α s) ∧
         (∑ s : Fin 14, α s * patternInformationSlope θ p ε s t) = 0 ∧
         (∀ s ∈ K, dualRay ε η s = patternInformation θ p ε s t) ∧
         (∀ s ∉ K, patternInformation θ p ε s t < dualRay ε η s) ∧
         (distinct → ∀ s ∈ K, ∀ u ∈ K, s ≠ u →
            projectedScore θ p ε s t ≠ projectedScore θ p ε u t)}
  -- @realizes \mathcal R_3(primal-dual certificate);
  -- @realizes \mathcal R_5(primal-dual certificate and distinct scores)

/-- the [r3](goal) is the mathematical object specified below. -/
def R3 : Set (ℝ × ℝ × ℝ × ℝ) :=
  certifiedRegion ({0, 5, 7} : Finset (Fin 14)) false
  -- @realizes \mathcal R_3(S1,S6,S8)

/-- the [r5](goal) is the mathematical object specified below. -/
def R5 : Set (ℝ × ℝ × ℝ × ℝ) :=
  certifiedRegion ({2, 3, 5, 7, 8} : Finset (Fin 14)) true
  -- @realizes \mathcal R_5(S3,S4,S6,S8,S9)

end CausalSmith.Stat.LdpAteEfficiencySurface
