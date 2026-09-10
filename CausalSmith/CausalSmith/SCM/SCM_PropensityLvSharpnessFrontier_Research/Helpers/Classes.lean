import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Basic

/-! # Fixed-stratum bow and mixture classes -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set
open scoped ENNReal

/-- Mutual-support bow-model membership, with a singleton endpoint at `e = 1`. -/
-- @node: def:bow-compatible
structure BowCompatible {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P Q : Measure Y) : Prop where
  observed_probability : IsProbabilityMeasure P
  intervention_probability : IsProbabilityMeasure Q
  realization : (e = 1 ∧ Q = P) ∨ ∃ w : BowWitness Y,
    StrictPositivity e ∧ BowStructure w ∧ POConsistency w ∧ MutualAbsCont w a ∧
      armPropensity w a = e ∧ armLaw w a = P ∧ interventionalLaw w a = Q
  bow_structure : e = 1 ∨ ∃ w : BowWitness Y, BowStructure w
  consistency : e = 1 ∨ ∃ w : BowWitness Y, POConsistency w
  positivity : e = 1 ∨ StrictPositivity e
  mutual_ac : e = 1 ∨ ∃ w : BowWitness Y, MutualAbsCont w a
  boundary : e = 1 → Q = P

/-- The compatible interventional-law set, including the singleton endpoint at `e = 1`. -/
def bowCompatibleSet {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  {Q | BowCompatible a e P Q}
  -- @realizes \mathfrak M_e(P)(compatible-law set; singleton at e=1)

/-- Dominated-residual mixture membership, including the singleton endpoint. -/
-- @node: def:mixture-class
structure MixtureClass {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) : Prop where
  positivity : e = 1 ∨ StrictPositivity e
  observed_probability : IsProbabilityMeasure P
  candidate_probability : IsProbabilityMeasure Q
  representation : e ≠ 1 → ∃ R : Measure Y, IsProbabilityMeasure R ∧
    R.AbsolutelyContinuous P ∧
    Q = ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R
  boundary : e = 1 → Q = P

/-- Propensity mixtures with a residual law dominated by `P`. -/
def mixtureClassSet {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  {Q | MixtureClass e P Q}
  -- @realizes \mathfrak L_e(P)(dominated-residual mixture set)
  -- @realizes R(probability residual with R≪P)

/-- Unrestricted bow-model membership, with a singleton endpoint at `e = 1`. -/
-- @node: def:bow-compatible-one-sided
structure BowCompatibleOneSided {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P Q : Measure Y) : Prop where
  observed_probability : IsProbabilityMeasure P
  intervention_probability : IsProbabilityMeasure Q
  realization : (e = 1 ∧ Q = P) ∨ ∃ w : BowWitness Y,
    StrictPositivity e ∧ BowStructure w ∧ POConsistency w ∧
      armPropensity w a = e ∧ armLaw w a = P ∧ interventionalLaw w a = Q
  bow_structure : e = 1 ∨ ∃ w : BowWitness Y, BowStructure w
  consistency : e = 1 ∨ ∃ w : BowWitness Y, POConsistency w
  positivity : e = 1 ∨ StrictPositivity e
  boundary : e = 1 → Q = P

/-- The unrestricted compatible interventional-law set. -/
def bowCompatibleOneSidedSet {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  {Q | BowCompatibleOneSided a e P Q}
  -- @realizes \mathfrak M^{\to}_e(P)(one-sided compatible-law set)

/-- Arbitrary-residual mixture membership, including the singleton endpoint. -/
-- @node: def:mixture-class-one-sided
structure MixtureClassOneSided {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) : Prop where
  positivity : e = 1 ∨ StrictPositivity e
  observed_probability : IsProbabilityMeasure P
  candidate_probability : IsProbabilityMeasure Q
  representation : e ≠ 1 → ∃ R : Measure Y, IsProbabilityMeasure R ∧
    Q = ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R
  boundary : e = 1 → Q = P

/-- Propensity mixtures with an arbitrary residual probability law. -/
def mixtureClassOneSidedSet {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  {Q | MixtureClassOneSided e P Q}
  -- @realizes \mathfrak L^{\to}_e(P)(arbitrary-residual mixture set)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
