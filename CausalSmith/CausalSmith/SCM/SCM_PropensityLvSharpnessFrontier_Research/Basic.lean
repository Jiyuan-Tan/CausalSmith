import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.CondDistrib
import Causalean.Stat.Sample

/-!
# Propensity sharpness frontier: ambient models

This file gives the fixed-stratum and covariate-conditional bow-model carriers
and the paper's explicitly threaded assumptions.
-/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-- A bow-model witness is an arbitrary probability law of `(A,Y(0),Y(1))`. -/
structure BowWitness (Y : Type*) [MeasurableSpace Y] where
  law : Measure (Bool × Y × Y)
  probability : IsProbabilityMeasure law
  realizedOutcome : Bool × Y × Y → Y
  -- @realizes A(binary treatment coordinate)
  -- @realizes Y(0),Y(1)(potential-outcome coordinates in Y²)
  -- @realizes \mathcal Y(outcome measurable-space carrier)

/-- For [a bow witness](hyp:w), [its latent law is a probability measure](goal). -/
instance {Y : Type*} [MeasurableSpace Y] (w : BowWitness Y) :
    IsProbabilityMeasure w.law := w.probability

/-- The treatment coordinate of a bow witness. -/
def treatment {Y : Type*} (z : Bool × Y × Y) : Bool := z.1

/-- The potential outcome selected by an arm. -/
def potentialOutcome {Y : Type*} (a : Bool) (z : Bool × Y × Y) : Y :=
  if a then z.2.2 else z.2.1

/-- The observed-outcome coordinate of a bow witness. -/
def observedOutcome {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (z : Bool × Y × Y) : Y :=
  w.realizedOutcome z
  -- @realizes Y(Y = Y(A))

/-- The probability of a treatment arm. -/
def armPropensity {Y : Type*} [MeasurableSpace Y] (w : BowWitness Y) (a : Bool) : ℝ :=
  (w.law {z | treatment z = a}).toReal
  -- @realizes e(e = Pr(A=a); range constrained by StrictPositivity)

/-- The interventional arm law. -/
noncomputable def interventionalLaw {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (a : Bool) : Measure Y :=
  w.law.map (potentialOutcome a)
  -- @realizes Q(candidate law of Y(a))

/-- The observational arm law, represented by normalized restriction. -/
noncomputable def armLaw {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (a : Bool) : Measure Y :=
  (w.law {z | treatment z = a})⁻¹ •
    (w.law.restrict {z | treatment z = a}).map (observedOutcome w)
  -- @realizes P(observational conditional arm law)

/-- The conditional law of the potential outcome `Y(a)` given `A = a`,
represented by normalized restriction. -/
noncomputable def conditionalPotentialOutcomeLaw {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (a : Bool) : Measure Y :=
  (w.law {z | treatment z = a})⁻¹ •
    (w.law.restrict {z | treatment z = a}).map (potentialOutcome a)

/-- The observed joint law of treatment and selected outcome. -/
noncomputable def observedLaw {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) : Measure (Bool × Y) :=
  w.law.map fun z => (treatment z, observedOutcome w z)

/-- The witness has the unrestricted latent architecture of the bow ADMG. -/
-- @node: ass:bow-structure
def BowStructure {Y : Type*} [MeasurableSpace Y] (w : BowWitness Y) : Prop :=
  IsProbabilityMeasure w.law

/-- Potential-outcome consistency for the selector realization. -/
-- @node: ass:consistency
def POConsistency {Y : Type*} [MeasurableSpace Y] (w : BowWitness Y) : Prop :=
  ∀ᵐ z ∂w.law, observedOutcome w z = potentialOutcome (treatment z) z

/-- Under consistency, conditioning `Y(a)` on `A = a` gives the observed arm law.  For the specified model objects, [the stated conditions](hyp:hCons), [the stated mathematical relationship holds](goal).
-/
lemma conditionalPotentialOutcomeLaw_eq_armLaw {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (a : Bool) (hCons : POConsistency w) :
    conditionalPotentialOutcomeLaw w a = armLaw w a := by
  let E : Set (Bool × Y × Y) := {z | treatment z = a}
  have hE : MeasurableSet E := (measurableSet_singleton a).preimage measurable_fst
  have hae : observedOutcome w =ᵐ[w.law.restrict E] potentialOutcome a := by
    change ∀ᵐ z ∂w.law.restrict E, observedOutcome w z = potentialOutcome a z
    rw [ae_restrict_iff' hE]
    filter_upwards [hCons] with z hz hza
    rw [hz]
    simpa [E, treatment] using congrArg (fun b => potentialOutcome b z) hza
  change (w.law E)⁻¹ • (w.law.restrict E).map (potentialOutcome a) =
    (w.law E)⁻¹ • (w.law.restrict E).map (observedOutcome w)
  rw [Measure.map_congr hae]

/-- Strict treatment positivity at a fixed stratum. @realizes e(0<e<1) -/
-- @node: ass:positivity
def StrictPositivity (e : ℝ) : Prop :=
  0 < e ∧ e < 1

/-- Mutual absolute continuity of the conditional law of `Y(a)` given `A = a`
and the marginal law of `Y(a)`. -/
-- @node: ass:mutual-ac
def MutualAbsCont {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (a : Bool) : Prop :=
  (conditionalPotentialOutcomeLaw w a).AbsolutelyContinuous (interventionalLaw w a) ∧
    (interventionalLaw w a).AbsolutelyContinuous (conditionalPotentialOutcomeLaw w a)

/-- IID sampling of the first `n` observations from a specified observational law. -/
-- @node: ass:iid-sampling
def IidObservationalSampling {Omega Y : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Y]
    (n : ℕ) (Z : ℕ → Omega → Bool × Y) (mu : Measure Omega)
    (nu : Measure (Bool × Y)) : Prop :=
  IsProbabilityMeasure mu ∧ IsProbabilityMeasure nu ∧
    (∀ i : Fin n, Measurable (Z i)) ∧
    iIndepFun (fun i : Fin n => Z i) mu ∧
    ∀ i : Fin n, mu.map (Z i) = nu

/-- A global conditional bow witness carries one probability law and common
versions of every conditional object used by the paper. -/
structure CondBowWitness (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  law : Measure (X × Bool × Y × Y)
  probability : IsProbabilityMeasure law
  realizedOutcome : X × Bool × Y × Y → Y
  covariateLaw : Measure X -- @realizes \mu_X(covariate probability-law carrier)
  condProp : Bool → X → ℝ -- @realizes \boldsymbol e(pair of conditional propensity maps)
  condArmLaw : Bool → Kernel X Y -- @realizes \boldsymbol P(pair of observed arm kernels)
  condIntervLaw : Bool → Kernel X Y -- @realizes \boldsymbol Q(pair of interventional kernels)
  condArmLaw_markov : ∀ a, IsMarkovKernel (condArmLaw a)
  condIntervLaw_markov : ∀ a, IsMarkovKernel (condIntervLaw a)
  -- @realizes \mathcal X(covariate measurable-space carrier)
  -- @realizes X(observed covariate coordinate)
  -- @realizes U(global latent state represented by the joint tuple)

/-- For [a conditional bow witness](hyp:w), [its joint covariate-latent law is a probability measure](goal). -/
instance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (w : CondBowWitness X Y) : IsProbabilityMeasure w.law := w.probability

/-- The global latent-variable architecture with arrows `X→A`, `X→Y`, `A→Y`. -/
-- @node: ass:conditional-bow-architecture
def CondBowArchitecture {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (w : CondBowWitness X Y) : Prop :=
  IsProbabilityMeasure w.covariateLaw ∧
    (∀ C : Set X, MeasurableSet C → w.law {z | z.1 ∈ C} = w.covariateLaw C) ∧
    (∀ (C : Set X) (a : Bool), MeasurableSet C →
      w.law {z | z.1 ∈ C ∧ z.2.1 = a} =
        ∫⁻ x in C, ENNReal.ofReal (w.condProp a x) ∂w.covariateLaw) ∧
    (∀ (C : Set X) (B : Set Y) (a : Bool), MeasurableSet C → MeasurableSet B →
      w.law {z | z.1 ∈ C ∧ z.2.1 = a ∧
        w.realizedOutcome z ∈ B} =
        ∫⁻ x in C, ENNReal.ofReal (w.condProp a x) * w.condArmLaw a x B
          ∂w.covariateLaw) ∧
    (∀ (C : Set X) (B : Set Y) (a : Bool), MeasurableSet C → MeasurableSet B →
      w.law {z | z.1 ∈ C ∧ potentialOutcome a (z.2.1, z.2.2.1, z.2.2.2) ∈ B} =
        ∫⁻ x in C, w.condIntervLaw a x B ∂w.covariateLaw)

/-- A measurable normalized pair of `[0,1]`-valued propensities. -/
def PropensitySystem {X : Type*} [MeasurableSpace X]
    (e : Bool → X → ℝ) : Prop :=
  (∀ a, Measurable (e a)) ∧ -- @realizes \boldsymbol e(measurable arm maps)
    (∀ x a, e a x ∈ Set.Icc 0 1) ∧ -- @realizes \boldsymbol e(range in [0,1])
    (∀ x, e false x + e true x = 1) -- @realizes \boldsymbol e(arm probabilities sum to one)

/-- Uniform overlap for an otherwise unrestricted propensity system. -/
-- @node: ass:conditional-overlap
def CondOverlap {X : Type*} [MeasurableSpace X]
    (kappa : ℝ) (e : Bool → X → ℝ) : Prop :=
  0 < kappa ∧ -- @realizes \kappa(positive overlap constant)
    kappa ≤ (1 / 2 : ℝ) ∧ -- @realizes \kappa(kappa≤1/2)
    PropensitySystem e ∧
    (∀ x a, e a x ∈ Set.Icc kappa (1 - kappa))

/-- Consistency of the global selector model. -/
-- @node: ass:conditional-consistency
def CondConsistency {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (w : CondBowWitness X Y) : Prop :=
  ∀ᵐ z ∂w.law,
    w.realizedOutcome z =
      potentialOutcome z.2.1 (z.2.1, z.2.2.1, z.2.2.2)

/-- Reverse support holds for both arms on one measurable conull set. -/
-- @node: ass:conditional-reverse-support
def CondReverseSupport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (muX : Measure X) (P Q : Bool → Kernel X Y) : Prop :=
  ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧
    ∀ x ∈ S, ∀ a, (Q a x).AbsolutelyContinuous (P a x)

-- @env: S1
-- @realizes \mathcal Y(standard Borel outcome type)
-- @realizes a(binary arm index Bool)
-- @realizes R(residual probability-law carrier)
-- @realizes p(event probability in [0,1] via EventProbabilityCoordinate)
-- @realizes q(candidate binary probability in [0,1] via ProbabilityCoordinate)
-- @realizes q_0(boundary coordinate via BoundaryPerturbation)
-- @realizes \varepsilon(outward perturbation via BoundaryPerturbation)
-- @realizes y(real threshold)
-- @realizes F_P,F_Q(real-valued CDFs from measures on Real)
-- @realizes h(measurable essentially bounded real query)
-- @realizes \underline\theta_h,\overline\theta_h(real endpoint pair)
variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
  [BorelSpace Y] [PolishSpace Y]

-- @env: S2
-- @realizes c(propensity cap via PropensityCap)
-- @realizes f_KL(KL generator defined in Divergence)
-- @realizes f_c(cap hinge defined in Divergence)
-- @realizes p_j,q_j(finite-alphabet probabilities via FiniteAlphabetLegality)
variable (f : ℝ → ℝ) (c : ℝ)

-- @env: S3
-- @realizes n(natural sample size)
-- @realizes \alpha(miscoverage in (0,1) via MiscoverageLevel)
variable (n : ℕ) (alpha : ℝ)

-- @env: S4
-- @realizes \mathcal X(standard Borel covariate type)
-- @realizes \boldsymbol R(pair of residual Markov kernels)
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [BorelSpace X] [PolishSpace X]

end CausalSmith.SCM.PropensityLvSharpnessFrontier
