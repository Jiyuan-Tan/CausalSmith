module
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
Concrete observed density laws, the fixed benchmark model, canonical sampling and honest
interval-length frontier.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Unit-interval Lebesgue probability measure. -/
def unitVolume : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The ambient product; the law carries the unit-interval support restriction. -/
abbrev Omega := ℝ × Bool × ℝ -- @realizes Omega(product Borel space; support in ObsLaw)

/-- Identity observed record. -/
def observedRecord (o : Omega) : Omega := o -- @realizes O(identity record)

/-- Covariate coordinate. -/
def X (o : Omega) : ℝ := o.1 -- @realizes X(first coordinate; range in ObsLaw.support)
/-- Treatment coordinate. -/
def A (o : Omega) : Bool := o.2.1 -- @realizes A(binary coordinate)
/-- Outcome coordinate. -/
def Y (o : Omega) : ℝ := o.2.2 -- @realizes Y(last coordinate; range in ObsLaw.support)

/-- Arm propensity from its treatment-one version. -/
def armProbability (e : ℝ → ℝ) (a : Bool) (x : ℝ) : ℝ :=
  if a then e x else 1 - e x -- @realizes pi(pi_1=e; pi_0=1-e)

/-- A probability law with genuine normalized conditional density versions. -/
structure ObsLaw where
  law : Measure Omega -- @realizes P(observed measure)
  prob : IsProbabilityMeasure law -- @realizes P(probability normalization)
  e : ℝ → ℝ -- @realizes e(measurable real version on unit interval)
  eta : Bool → ℝ → ℝ → ℝ -- @realizes eta(arm/covariate/outcome density carrier)
  e_measurable : Measurable e -- @realizes e(measurable)
  eta_measurable : ∀ a,
    Measurable (fun z : ℝ × ℝ => eta a z.1 z.2) -- @realizes eta(joint measurable)
  e_range : ∀ x ∈ Set.Icc 0 1, e x ∈ Set.Icc 0 1 -- @realizes e(range [0,1])
  eta_nonneg : ∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
    0 ≤ eta a x y -- @realizes eta(nonnegative density)
  eta_integrable : ∀ a x, x ∈ Set.Icc 0 1 →
    Integrable (eta a x) unitVolume -- @realizes eta(outcome integrable)
  eta_normalized : ∀ a x, x ∈ Set.Icc 0 1 →
    ∫ y, eta a x y ∂unitVolume = 1 -- @realizes eta(normalized at every covariate)
  support : ∀ᵐ o ∂law, X o ∈ Set.Icc 0 1 ∧ Y o ∈ Set.Icc 0 1
    -- @realizes X(unit support) @realizes Y(unit support) @realizes Omega(unit-supported law)
  rectangles : ∀ (B D : Set ℝ), MeasurableSet B → MeasurableSet D → ∀ a,
    law.real {o | X o ∈ B ∧ A o = a ∧ Y o ∈ D} =
      ∫ x in B, armProbability e a x * (∫ y in D, eta a x y ∂unitVolume) ∂unitVolume
    -- @realizes e(propensity version) @realizes eta(conditional density representation)

instance (P : ObsLaw) : IsProbabilityMeasure P.law := P.prob

-- @env: S1
variable (P : ObsLaw) -- @realizes P(observed law with density versions)

/-- Arm propensity version. -/
def pi (a : Bool) (x : ℝ) : ℝ := armProbability P.e a x

/-- Actual outcome L² space; formulas below use measurable representatives. -/
abbrev H := Lp ℝ 2 unitVolume -- @realizes H(L2 of unit Lebesgue measure)

/-- Squared L² norm of a representative. -/
def l2Squared (f : ℝ → ℝ) : ℝ := ∫ y, (f y) ^ 2 ∂unitVolume
/-- L² norm of a representative. -/
def l2Norm (f : ℝ → ℝ) : ℝ := Real.sqrt (l2Squared f)

/-- Marginal counterfactual density. -/
def marginalDensity (a : Bool) (y : ℝ) : ℝ :=
  ∫ x, P.eta a x y ∂unitVolume -- @realizes p(integral of eta over uniform covariate)
/-- Density contrast. -/
def delta (y : ℝ) : ℝ :=
  marginalDensity P true y - marginalDensity P false y -- @realizes delta(p_1-p_0)
/-- Squared causal density effect. -/
def Psi : ℝ := l2Squared (delta P) -- @realizes Psi(integral of squared contrast)

-- @node: ass:design
/-- Uniform known covariate design. -/
def UniformDesign : Prop := P.law.map X = unitVolume -- @realizes X(uniform marginal)

-- @node: ass:overlap
/-- Fixed propensity overlap envelope. -/
def PropensityOverlap : Prop :=
  ∀ x ∈ Set.Icc 0 1, P.e x ∈ Set.Icc (1 / 4) (3 / 4) -- @realizes e(overlap)

-- @node: ass:propensity-smoothness
/-- Hölder-one-tenth propensity regularity. -/
def PropensityHolder : Prop :=
  ∀ x ∈ Set.Icc 0 1, ∀ xp ∈ Set.Icc 0 1,
    |P.e x - P.e xp| ≤ 10 * |x - xp| ^ (1 / 10 : ℝ)
    -- @realizes x(unit interval) @realizes xp(unit interval) @realizes e(Holder seminorm 10)

-- @node: ass:density-envelope
/-- Fixed positive conditional-density envelope. -/
def DensityEnvelope : Prop :=
  ∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → P.eta a x y ∈ Set.Icc (1 / 4) 4
    -- @realizes a(binary arm) @realizes y(unit interval) @realizes eta(density envelope)

-- @node: ass:density-x-smoothness
/-- Covariate Hölder regularity uniform in outcome and arm. -/
def DensityCovariateHolder : Prop :=
  ∀ a y, y ∈ Set.Icc 0 1 → ∀ x ∈ Set.Icc 0 1, ∀ xp ∈ Set.Icc 0 1,
    |P.eta a x y - P.eta a xp y| ≤ 10 * |x - xp| ^ (1 / 10 : ℝ)
    -- @realizes eta(covariate Holder seminorm 10)

-- @node: ass:density-y-smoothness
/-- Outcome Lipschitz regularity uniform in covariate and arm. -/
def DensityOutcomeLipschitz : Prop :=
  ∀ a x, x ∈ Set.Icc 0 1 → ∀ y ∈ Set.Icc 0 1, ∀ yp ∈ Set.Icc 0 1,
    |P.eta a x y - P.eta a x yp| ≤ 10 * |y - yp|
    -- @realizes yp(unit interval) @realizes eta(outcome Lipschitz seminorm 10)

-- @node: def:model
/-- The original fixed benchmark, bundled at its planned class boundary. -/
structure Model : Prop where -- @realizes M(six-atom fixed model)
  design : UniformDesign P
  overlap : PropensityOverlap P
  propensity_holder : PropensityHolder P
  density_envelope : DensityEnvelope P
  density_covariate_holder : DensityCovariateHolder P
  density_outcome_lipschitz : DensityOutcomeLipschitz P

/-- Exact equality subclass, with pointwise contrast on the outcome interval. -/
def NullModel : Prop :=
  Model P ∧ ∀ y ∈ Set.Icc 0 1, delta P y = 0 -- @realizes Mzero(model and zero contrast)

/-- Canonical observed sample. -/
abbrev Data (n : ℕ) := Fin n → Omega -- @realizes data(n records) @realizes n(natural sample size)
/-- Sample plus a public randomization coordinate. -/
abbrev SampleSpace (n : ℕ) := Data n × ℝ -- @realizes U(real coordinate; unitVolume in sampleLaw)

-- @env: S2
variable (n : ℕ)

/-- Canonical iid sample law. -/
def dataLaw : Measure (Data n) := Measure.pi (fun _ => P.law)
/-- Canonical iid sample with independent uniform public randomization. -/
def sampleLaw : Measure (SampleSpace n) :=
  (dataLaw P n).prod unitVolume -- @realizes U(independent uniform randomization in [0,1])

-- @node: ass:sampling
/-- The joint sampling law equals the canonical product with uniform randomization. -/
def SamplingLaw (ν : Measure (SampleSpace n)) : Prop := ν = sampleLaw P n

/-- Raw possibly randomized interval decision map. -/
abbrev IntervalRule (n : ℕ) := SampleSpace n → Set ℝ -- @realizes I(interval rule carrier)

/-- Admissible connected Borel interval rule with a measurable inclusion graph. -/
def IsIntervalRule (I : IntervalRule n) : Prop :=
  (∀ ω, Set.OrdConnected (I ω) ∧ I ω ⊆ Set.Icc 0 16) ∧
  MeasurableSet {p : SampleSpace n × ℝ | p.2 ∈ I p.1}
    -- @realizes I(connected bounded intervals; jointly measurable graph)

/-- Length of a bounded interval; the empty interval has length zero. -/
def intervalLength (S : Set ℝ) : ℝ :=
  if S = ∅ then 0 else sSup S - sInf S -- @realizes length(sup minus inf; zero at empty)

/-- Coverage under canonical sampling. -/
def coverage (I : IntervalRule n) : ℝ :=
  (sampleLaw P n).real {ω | Psi P ∈ I ω}
/-- Expected length under canonical sampling. -/
def expectedLength (I : IntervalRule n) : ℝ :=
  ∫ ω, intervalLength (I ω) ∂sampleLaw P n
/-- Full-class ninety-percent honesty. -/
def IsHonest (I : IntervalRule n) : Prop :=
  ∀ P : ObsLaw, Model P → (9 / 10 : ℝ) ≤ coverage P n I
/-- Worst expected length over the entire equality subclass. -/
def worstNullLength (I : IntervalRule n) : ℝ :=
  sSup {r : ℝ | ∃ P : ObsLaw, NullModel P ∧ r = expectedLength P n I}

-- @node: def:frontier
/-- Full-class honest-length infimum with exact-null evaluation. -/
def honestLengthFrontier : ℝ :=
  sInf {r : ℝ | ∃ I : IntervalRule n, IsIntervalRule n I ∧ IsHonest n I ∧
    r = worstNullLength n I} -- @realizes Jstar(fixed-n infimum of null worst lengths)

end CausalSmith.Stat.DensityEffectRoughNull
