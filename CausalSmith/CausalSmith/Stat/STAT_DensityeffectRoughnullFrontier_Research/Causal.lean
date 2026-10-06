module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
Concrete causal extensions on the observed-product space and the two causal assumption atoms.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Ambient space for observed and both potential outcomes, with unit support below. -/
abbrev CausalSpace := Omega × (ℝ × ℝ) -- @realizes Ypot(pair carrier with unit support in extension)
/-- Causal covariate coordinate. -/
def causalX (o : CausalSpace) : ℝ := X o.1
/-- Potential outcome indexed by treatment. -/
def potentialY (a : Bool) (o : CausalSpace) : ℝ := if a then o.2.2 else o.2.1
    -- @realizes Ypot(binary-indexed potential coordinates)
/-- Measurability of the causal covariate coordinate. -/
-- @node: measurable_causalX
@[fun_prop] lemma measurable_causalX : Measurable causalX := by
  unfold causalX X
  fun_prop

-- @env: S5
variable (Q : Measure CausalSpace) -- @realizes Qcausal(measure on observed and potential outcomes)

/-- Probability law with observed marginal P and unit-supported potential outcomes. -/
def IsCausalExtension (P : ObsLaw) (Q : Measure CausalSpace) : Prop :=
  IsProbabilityMeasure Q ∧ Q.map Prod.fst = P.law ∧
    (∀ᵐ o ∂Q, o.2.1 ∈ Set.Icc 0 1 ∧ o.2.2 ∈ Set.Icc 0 1)
    -- @realizes Qcausal(probability, observed marginal P) @realizes Ypot(unit support)

-- @node: ass:consistency
/-- Almost-sure single-treatment consistency. -/
def CausalConsistency : Prop := ∀ᵐ o ∂Q, Y o.1 = potentialY (A o.1) o

-- @node: ass:exchangeability
/-- Conditional independence of treatment and the joint potential-outcome pair given X. -/
def CausalExchangeability (hQ : IsProbabilityMeasure Q) : Prop :=
  letI : IsProbabilityMeasure Q := hQ
  CondIndepFun (MeasurableSpace.comap causalX inferInstance) measurable_causalX.comap_le
    (fun o : CausalSpace => A o.1) Prod.snd Q

/-- Conditional independence of the two potential outcomes given X. -/
def IndependentPotentials (Q : Measure CausalSpace) (hQ : IsProbabilityMeasure Q) : Prop :=
  letI : IsProbabilityMeasure Q := hQ
  CondIndepFun (MeasurableSpace.comap causalX inferInstance) measurable_causalX.comap_le
    (potentialY false) (potentialY true) Q
/-- Marginal probability measure associated with the identified density. -/
def counterfactualMeasure (P : ObsLaw) (a : Bool) : Measure ℝ :=
  unitVolume.withDensity (fun y => ENNReal.ofReal (marginalDensity P a y))

end CausalSmith.Stat.DensityEffectRoughNull
