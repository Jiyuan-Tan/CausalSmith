import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Measure.Real

/-!
# Observable capacities and threshold cuts

Finite-cell observed data, selected-complier capacity contrasts, their prefix and
tail aggregates, and the branch-free threshold endpoint formulas.
-/

open scoped BigOperators
open MeasureTheory Set

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

-- @env: S2
variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳]
variable {K : ℕ}

/-- The ordered outcome support. -/
abbrev OutcomeLevel (K : ℕ) := Fin K -- @realizes K(outcome levels) @realizes \mathcal Y(Fin K with natural order)

/-- One finite observed-data cell, with `none` recording an unobserved outcome. -/
structure ObservedDatum (𝒳 : Type*) (K : ℕ) where
  cell : 𝒳 -- @realizes X(carrier \mathcal X) @realizes \mathcal X(finite covariate support)
  instrument : Bool -- @realizes Z(binary instrument)
  treatment : Bool -- @realizes D(binary received treatment)
  selected : Bool -- @realizes S(binary selection indicator)
  outcome : Option (Fin K) -- @realizes Y(Fin K when selected; none when unobserved) @realizes O(observed tuple X,Z,D,S,SY)
  deriving DecidableEq, Fintype

/-- Observed-data cells have decidable equality. -/
add_decl_doc instDecidableEqObservedDatum

/-- The finite observed-data type has a canonical finite enumeration. -/
add_decl_doc instFintypeObservedDatum

/-- This declaration supplies the canonical canonical measurable space observed datum typeclass instance for the finite slate-benefit construction. -/
instance : MeasurableSpace (ObservedDatum 𝒳 K) := ⊤

/-- A conditional probability represented as a real-valued ratio, with zero at a zero denominator. -/
noncomputable def conditionalReal {α : Type*} [MeasurableSpace α]
    (P : Measure α) (A B : Set α) : ℝ :=
  if 0 < P.real B then P.real (A ∩ B) / P.real B else 0

/-- Real-valued capacity arrays. Their nonnegativity is a consequence of the causal
assumptions for observable contrasts, rather than data contained in an arbitrary input law. -/
structure Capacities (𝒳 : Type*) (K : ℕ) where
  lower : 𝒳 → Fin K → ℝ -- @realizes \ell_i(x)(lower selected-complier capacity array)
  upper : 𝒳 → Fin K → ℝ -- @realizes h_j(x)(upper selected-complier capacity array)

/-- The valid capacities condition is the stated property of the slate-benefit partial-transport model. -/
def ValidCapacities (c : Capacities 𝒳 K) : Prop :=
  (∀ x i, 0 ≤ c.lower x i) ∧ (∀ x j, 0 ≤ c.upper x j)

namespace Capacities

/-- The q0 is the object specified here for the slate-benefit partial-transport construction. -/
def q0 (c : Capacities 𝒳 K) (x : 𝒳) : ℝ :=
  ∑ i, c.lower x i -- @realizes q_0(x)(sum of lower capacities)

/-- The q1 is the object specified here for the slate-benefit partial-transport construction. -/
def q1 (c : Capacities 𝒳 K) (x : 𝒳) : ℝ :=
  ∑ j, c.upper x j -- @realizes q_1(x)(sum of upper capacities)

/-- The gap is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def gap (c : Capacities 𝒳 K) (x : 𝒳) : ℝ :=
  c.q1 x - c.q0 x -- @realizes \Delta q(x)(q1 minus q0)

/-- The mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def mass (c : Capacities 𝒳 K) (x : 𝒳) : ℝ :=
  min (c.q0 x) (c.q1 x) -- @realizes m(x)(minimum of arm totals)

/-- The lower le is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def lowerLe (c : Capacities 𝒳 K) (x : 𝒳) (t : Fin K) : ℝ :=
  ∑ i with i ≤ t, c.lower x i -- @realizes \ell_{\le t}(x)(lower prefix)

/-- The lower lt is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def lowerLt (c : Capacities 𝒳 K) (x : 𝒳) (t : Fin K) : ℝ :=
  ∑ i with i < t, c.lower x i -- @realizes \ell_{<t}(x)(lower strict prefix)

/-- The lower gt is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def lowerGt (c : Capacities 𝒳 K) (x : 𝒳) (t : Fin K) : ℝ :=
  ∑ i with t < i, c.lower x i -- @realizes \ell_{>t}(x)(lower upper tail)

/-- The upper le is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def upperLe (c : Capacities 𝒳 K) (x : 𝒳) (t : Fin K) : ℝ :=
  ∑ j with j ≤ t, c.upper x j -- @realizes h_{\le t}(x)(upper prefix)

/-- The upper gt is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def upperGt (c : Capacities 𝒳 K) (x : 𝒳) (t : Fin K) : ℝ :=
  ∑ j with t < j, c.upper x j -- @realizes h_{>t}(x)(upper upper tail)

end Capacities

private def armEvent (x : 𝒳) (z : Bool) : Set (ObservedDatum 𝒳 K) :=
  {o | o.cell = x ∧ o.instrument = z}

private def selectedOutcomeEvent (x : 𝒳) (d : Bool) (i : Fin K) :
    Set (ObservedDatum 𝒳 K) :=
  {o | o.cell = x ∧ o.treatment = d ∧ o.selected = true ∧ o.outcome = some i}

/-- The raw signed instrument contrasts associated with an arbitrary finite measure. -/
noncomputable def observableCapacityContrasts (Pobs : Measure (ObservedDatum 𝒳 K)) :
    Capacities 𝒳 K where
  lower x i :=
    conditionalReal Pobs (selectedOutcomeEvent x false i) (armEvent x false) -
      conditionalReal Pobs (selectedOutcomeEvent x false i) (armEvent x true)
      -- @realizes \ell_i(x)(two conditional-instrument contrast)
  upper x j :=
    conditionalReal Pobs (selectedOutcomeEvent x true j) (armEvent x true) -
      conditionalReal Pobs (selectedOutcomeEvent x true j) (armEvent x false)
      -- @realizes h_j(x)(two conditional-instrument contrast)

/-- An observed law is compatible with the maintained domain when it is a
probability measure and its law-derived instrument contrasts are nonnegative. -/
def CompatibleObservedLaw (Pobs : Measure (ObservedDatum 𝒳 K)) : Prop :=
  IsProbabilityMeasure Pobs ∧ ValidCapacities (observableCapacityContrasts Pobs)

/-- The intrinsic domain of an observed law used by the paper: at least three
ordered outcome levels, total mass one, and no recorded outcome off selection
or missing outcome on selection. -/
def ObservedLawDomain (Pobs : Measure (ObservedDatum 𝒳 K)) : Prop :=
  3 ≤ K ∧ IsProbabilityMeasure Pobs ∧
    ∀ᵐ o ∂Pobs, o.outcome.isSome = o.selected

/-- The raw observable capacity contrasts formed for any observed-data law. -/
noncomputable def observableCapacities (Pobs : Measure (ObservedDatum 𝒳 K)) :
    Capacities 𝒳 K :=
  observableCapacityContrasts Pobs

/-- @realizes P_{\mathrm{obs}}(probability law of O)
The observable capacities on the paper domain.  Compatibility is supplied only
after identification has established validity of the raw contrasts. -/
-- @node: def:observable-capacities
noncomputable def paperObservableCapacities
    (Pobs : Measure (ObservedDatum 𝒳 K))
    (_hK : 3 ≤ K) (_hDomain : ObservedLawDomain Pobs)
    (c : Capacities 𝒳 K) (_hc : c = observableCapacities Pobs)
    (_hCompatible : CompatibleObservedLaw Pobs) : Capacities 𝒳 K :=
  c

namespace Capacities

private def lowerCandidate (c : Capacities 𝒳 K) (x : 𝒳) : Option (Fin K) → ℝ
  | none => 0
  | some t => c.lowerLe x t - c.upperLe x t + min (c.gap x) 0

private def upperCandidate (c : Capacities 𝒳 K) (x : 𝒳) : Option (Fin K) → ℝ
  | none => c.mass x
  | some t => c.lowerLt x t + c.upperGt x t

/-- The benefit lower is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def benefitLower (c : Capacities 𝒳 K) (x : 𝒳) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (lowerCandidate c x)
  -- @realizes B_L(x)(maximum of zero and branch-free lower threshold cuts)

/-- The benefit upper is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def benefitUpper (c : Capacities 𝒳 K) (x : 𝒳) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (upperCandidate c x)
  -- @realizes B_U(x)(minimum of mass cap and upper threshold cuts)

/-- The reusable branch-free lower and upper threshold cuts. -/
def thresholdCuts (c : Capacities 𝒳 K) (_hValid : ValidCapacities c) (x : 𝒳) : ℝ × ℝ :=
  (c.benefitLower x, c.benefitUpper x)

/-- The branch-free threshold cuts on the paper's observed-law domain. -/
-- @node: def:threshold-cuts
def paperThresholdCuts (Pobs : Measure (ObservedDatum 𝒳 K))
    (_hK : 3 ≤ K) (_hDomain : ObservedLawDomain Pobs)
    (c : Capacities 𝒳 K) (_hc : c = observableCapacities Pobs)
    (_hCompatible : CompatibleObservedLaw Pobs)
    (hValid : ValidCapacities c) (x : 𝒳) : ℝ × ℝ :=
  thresholdCuts c hValid x

/-- The aggregate mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def aggregateMass (c : Capacities 𝒳 K) (p : 𝒳 → ℝ) : ℝ :=
  ∑ x, p x * c.mass x -- @realizes M(weighted aggregate survivor mass)

/-- The covariate-cell probabilities determined by an observed-data law. -/
noncomputable def observedCellWeights
    (Pobs : Measure (ObservedDatum 𝒳 K)) : 𝒳 → ℝ :=
  fun x => Pobs.real {o | o.cell = x}
  -- @realizes p_x(observed-law covariate-cell probability)

/-- The two aggregate ratio endpoints together with the closed interval they
determine. -/
structure EndpointMapResult where
  endpoints : ℝ × ℝ
  identifiedSet : Set ℝ

/-- The observable endpoint functional and its identified closed interval.
The capacity array and cell weights are explicitly pinned to `Pobs`; the
remaining arguments record the paper's observed-law domain, validity,
nonnegativity, and positive target mass. -/
-- @node: def:identified-interval
noncomputable def endpointMap (c : Capacities 𝒳 K) (p : 𝒳 → ℝ)
    (Pobs : Measure (ObservedDatum 𝒳 K))
    (_hc : c = observableCapacities Pobs)
    (_hpobs : p = observedCellWeights Pobs)
    (_hValid : ValidCapacities c) -- @realizes \theta_L(valid capacities) @realizes \theta_U(valid capacities) @realizes \Theta_I(P_{\mathrm{obs}})(valid capacities)
    (_hp : ∀ x, 0 ≤ p x) -- @realizes \theta_L(nonnegative cell weights) @realizes \theta_U(nonnegative cell weights) @realizes \Theta_I(P_{\mathrm{obs}})(nonnegative cell weights)
    (_hMass : 0 < aggregateMass c p) -- @realizes \theta_L(positive aggregate mass) @realizes \theta_U(positive aggregate mass) @realizes \Theta_I(P_{\mathrm{obs}})(positive aggregate mass)
    (_hDomain : ObservedLawDomain Pobs) :
    EndpointMapResult :=
  let endpoints :=
    ((∑ x, p x * c.benefitLower x) / aggregateMass c p,
      (∑ x, p x * c.benefitUpper x) / aggregateMass c p)
  { endpoints := endpoints
    identifiedSet := Set.Icc endpoints.1 endpoints.2 }
  -- @realizes \Psi(P_{\mathrm{obs}})(ratio-of-summed-cuts endpoint map)
  -- @realizes \theta_L(lower endpoint) @realizes \theta_U(upper endpoint)
  -- @realizes \Theta_I(P_{\mathrm{obs}})(closed identified interval)

/-- The identified icc is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def identifiedIcc (c : Capacities 𝒳 K) (p : 𝒳 → ℝ)
    (Pobs : Measure (ObservedDatum 𝒳 K))
    (hc : c = observableCapacities Pobs)
    (hpobs : p = observedCellWeights Pobs)
    (hValid : ValidCapacities c) (hp : ∀ x, 0 ≤ p x)
    (hMass : 0 < aggregateMass c p)
    (hDomain : ObservedLawDomain Pobs) : Set ℝ :=
  (endpointMap c p Pobs hc hpobs hValid hp hMass hDomain).identifiedSet

end Capacities

end CausalSmith.PartialID.SlateBenefitPartialTransport
