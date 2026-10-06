module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Basic

Finite original-record private value frontiers: Basic.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


-- @env: S1
variable {n d : ℕ} -- @realizes n(participant count; admissibility below) @realizes d(stratum count)

/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Public resource tuples in the paper's domain](goal). -/
def Allowed (n d : ℕ) (eps : ℝ) : Prop :=
  2 ≤ n ∧ -- @realizes n(n≥2)
  2 ≤ d ∧ -- @realizes d(d≥2)
  0 < eps ∧ eps ≤ 1
  -- @realizes n(n≥2) @realizes d(d≥2) @realizes \varepsilon(0<ε≤1)

/-- Fix [the dimension](hyp:d). [Full binary potential-outcome records, in the order X,A,Y,Y0,Y1](goal). -/
abbrev FullRecord (d : ℕ) := Fin d × Bool × Bool × Bool × Bool
/-- Fix [the dimension](hyp:d). [Observed records](goal). -/
abbrev ObsRecord (d : ℕ) := Fin d × Bool × Bool -- @realizes \mathcal O([d]×{0,1}²)
/-- Fix [the dimension](hyp:d). [Paired input alphabet with Bool coding signs](goal). -/
abbrev PairedSymbol (d : ℕ) := Fin d × Bool -- @realizes \mathcal A_d([d]×{−1,1})
/-- Fix [the full participant record](hyp:w). [Cell coordinate](goal). -/
def cell (w : FullRecord d) : Fin d := w.1 -- @realizes X(carrier Fin d) @realizes [d](Fin d)
/-- Fix [the full participant record](hyp:w). [Assignment coordinate](goal). -/
def arm (w : FullRecord d) : Bool := w.2.1 -- @realizes A(binary)
/-- Fix [the full participant record](hyp:w). [Observed outcome coordinate](goal). -/
def outcome (w : FullRecord d) : Bool := w.2.2.1 -- @realizes Y(binary)
/-- Fix [the full participant record](hyp:w). [Control potential outcome](goal). -/
def outcome0 (w : FullRecord d) : Bool := w.2.2.2.1 -- @realizes Y^0(Bool control outcome)
/-- Fix [the full participant record](hyp:w). [Treated potential outcome](goal). -/
def outcome1 (w : FullRecord d) : Bool := w.2.2.2.2 -- @realizes Y^1(Bool treated outcome)
/-- Fix [the binary value a](hyp:a) and [the full participant record](hyp:w). [Arm-indexed potential outcome](goal). -/
def potential (a : Bool) (w : FullRecord d) : Bool :=
  if a then outcome1 w else outcome0 w
  -- @realizes Y^{\mathrm{pot}}(arm selection) @realizes a(Bool)
/-- Fix [the full participant record](hyp:w). [Observation projection](goal). -/
def observe (w : FullRecord d) : ObsRecord d :=
  (cell w, arm w, outcome w) -- @realizes O((X,A,Y))
/-- Fix [the binary value a](hyp:a). [Binary value in the real line](goal). -/
def bitVal (a : Bool) : ℝ := if a then 1 else 0
/-- Fix [the binary value s](hyp:s). [Sign coding](goal). -/
def signVal (s : Bool) : ℝ := if s then 1 else -1 -- @realizes s(±1)
/-- Fix [the observed participant record](hyp:o). [Signed observation](goal). -/
def obsSign (o : ObsRecord d) : ℝ :=
  signVal o.2.1 * signVal o.2.2 -- @realizes S((2A−1)(2Y−1))
/-- Fix [the observed participant record](hyp:o). [Paired observation projection](goal). -/
def signedObserve (o : ObsRecord d) : PairedSymbol d := (o.1, o.2.1 == o.2.2)
/-- Fix [the probability law P](hyp:P). [Observed marginal](goal). -/
def observedLaw (P : Measure (FullRecord d)) : Measure (ObsRecord d) :=
  P.map observe -- @realizes P_O(observed marginal)
/-- Fix [the probability law P](hyp:P), [the binary value a](hyp:a), and [the coordinate index](hyp:j). [Conditional cell mean, with division at zero cells interpreted by Lean](goal). -/
def armMean (P : Measure (FullRecord d)) (a : Bool) (j : Fin d) : ℝ :=
  P.real {w | cell w = j ∧ potential a w = true} / P.real {w | cell w = j}
  -- @realizes \mu(E[Ypot_a|X=j]) @realizes j(Fin d)
/-- Fix [the probability law P](hyp:P) and [the coordinate index](hyp:j). [Cellwise contrast](goal). -/
def contrast (P : Measure (FullRecord d)) (j : Fin d) : ℝ :=
  armMean P true j - armMean P false j -- @realizes \tau(μ1−μ0)
/-- Fix [the probability law P](hyp:P). [Baseline mean](goal). -/
def baseline (P : Measure (FullRecord d)) : ℝ :=
  P.real {w | outcome w = true} -- @realizes B(E Y)
/-- Fix [the probability law P](hyp:P). [First-best population value](goal). -/
def value (P : Measure (FullRecord d)) : ℝ :=
  (d : ℝ)⁻¹ * ∑ j, max (armMean P false j) (armMean P true j) -- @realizes V(mean arm maximum)
/-- Fix [the dimension](hyp:d). [Parameter cube](goal). -/
def parameterCube (d : ℕ) : Set (Fin d → ℝ) :=
  {theta | ∀ j, theta j ∈ Set.Icc (-(1/2 : ℝ)) (1/2)} -- @realizes \theta(cube)
/-- Fix [the function theta](hyp:theta). [Signed average absolute norm](goal). -/
def signedNorm (theta : Fin d → ℝ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ j, |theta j| -- @realizes F(mean absolute contrast)
/-- Fix [the function w](hyp:w). [Finite atomic law constructor](goal). -/
def atomLaw {α : Type} [Fintype α] [MeasurableSpace α] (w : α → ℝ) : Measure α :=
  ∑ a, ENNReal.ofReal (w a) • Measure.dirac a
/-- Fix [the function theta](hyp:theta). [Paired signed law](goal). -/
def pairedLaw (theta : Fin d → ℝ) : Measure (PairedSymbol d) :=
  atomLaw (fun v => (1 + signVal v.2 * theta v.1) / (2 * d)) -- @realizes P_\theta((1+sθj)/(2d))
/-- Fix [the dimension](hyp:d). [Public uniform paired law](goal). -/
def pairedUniform (d : ℕ) : Measure (PairedSymbol d) :=
  pairedLaw (fun _ => 0) -- @realizes \mathsf U_{2d}(uniform paired law)

-- @node: ass:uniform-covariates
/-- Fix [the probability law P](hyp:P). [Uniform covariate marginal](goal). -/
def UniformCovariates (P : Measure (FullRecord d)) : Prop :=
  ∀ j, P.real {w | cell w = j} = (d : ℝ)⁻¹ -- @realizes X(uniform marginal)

-- @node: ass:fair-randomization
/-- Fix [the probability law P](hyp:P). [Fair assignment conditional on both potential outcomes and the cell](goal). -/
def FairRandomization (P : Measure (FullRecord d)) : Prop :=
  ∀ (j : Fin d) (a y0 y1 : Bool),
    P.real {w | cell w = j ∧ arm w = a ∧ outcome0 w = y0 ∧ outcome1 w = y1} =
      (1/2 : ℝ) * P.real {w | cell w = j ∧ outcome0 w = y0 ∧ outcome1 w = y1}
      -- @realizes A(fair conditional assignment)

-- @node: ass:consistency
/-- Fix [the probability law P](hyp:P). [Almost-sure consistency](goal). -/
def Consistency (P : Measure (FullRecord d)) : Prop :=
  P.real {w | outcome w = potential (arm w) w} = 1 -- @realizes Y(consistency)

-- @node: ass:interior-means
/-- Fix [the probability law P](hyp:P). [Interior Bernoulli arm means](goal). -/
def InteriorMeans (P : Measure (FullRecord d)) : Prop :=
  ∀ a j, armMean P a j ∈ Set.Icc (1/4 : ℝ) (3/4) -- @realizes \mu(interior range)

-- @node: def:causal-model
/-- Fix [the probability law P](hyp:P). [The four defining causal model atoms](goal). -/
structure CausalModel (P : Measure (FullRecord d)) : Prop where
  uniform : UniformCovariates P
  fair : FairRandomization P
  consistent : Consistency P
  interior : InteriorMeans P
/-- Fix [the dimension](hyp:d). [The complete law class, including ambient probability typing](goal). -/
def causalClass (d : ℕ) : Set (Measure (FullRecord d)) :=
  {P | IsProbabilityMeasure P ∧ CausalModel P} -- @realizes \mathcal V_d(full causal law class)
/-- Fix [the density or prior under consideration](hyp:p) and [the binary value y](hyp:y). [Bernoulli atom weight](goal). -/
def bernMass (p : ℝ) (y : Bool) : ℝ := if y then p else 1 - p

-- @node: def:symmetric-law
/-- Fix [the function theta](hyp:theta). [Uniform cells, independent arm potentials, independent fair assignment, and consistency](goal). -/
def symmetricLaw (theta : Fin d → ℝ) : Measure (FullRecord d) :=
  atomLaw (fun w => (d : ℝ)⁻¹ * (1/2) *
    bernMass ((1 - theta (cell w))/2) (outcome0 w) *
    bernMass ((1 + theta (cell w))/2) (outcome1 w) *
    (if outcome w = potential (arm w) w then 1 else 0))
  -- @realizes G_\theta(explicit symmetric causal law)
/-- [Protocol class labels](goal). -/
inductive ProtocolClassLabel where
  | NI | SI
  deriving DecidableEq -- @realizes \mathcal C(NI or SI)
/-- [Equality of protocol-class labels is decidable](goal). -/
add_decl_doc instDecidableEqProtocolClassLabel
/-- Fix [the dimension](hyp:d). [Logarithmic dimension](goal). -/
def logDim (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)
/-- Fix [the real parameter t](hyp:t) and [the dimension](hyp:d). [Evaluated finite-resource rate](goal). -/
def rho (t : ℝ) (d : ℕ) : ℝ :=
  let L := logDim d
  if (d : ℝ)^2 * L ≤ t then (d : ℝ)^2 / (t * L)
  else min 1 (Real.log (Real.exp 1 + (d : ℝ)^2 * L / t) / L)^2
/-- Fix [the protocol-class label](hyp:_C), [the sample size and the dimension](hyp:n,d), and [the privacy budget](hyp:eps). [Class-independent squared-error rate](goal). -/
def rateR (_C : ProtocolClassLabel) (n d : ℕ) (eps : ℝ) : ℝ :=
  rho (n * eps^2) d -- @realizes r_{\mathcal C}(piecewise rho)
/-- Fix [the protocol-class label](hyp:C), [the sample size and the dimension](hyp:n,d), and [the privacy budget](hyp:eps). [Connected honest-length rate](goal). -/
def rateH (C : ProtocolClassLabel) (n d : ℕ) (eps : ℝ) : ℝ :=
  Real.sqrt (rateR C n d eps) -- @realizes h_{\mathcal C}(sqrt risk rate)


end CausalSmith.Stat.LdpOptvalueUniformFrontier
