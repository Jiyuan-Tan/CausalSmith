module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaPriors
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Projections
public import Causalean.Stat.Minimax.ChiSquared

/-! Finite-moment homogeneity testing: Helpers/ComponentAugmentation. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Every fine-frame node carries a binary treatment-coordinate and outcome-coordinate coefficient. This statement assumes [the K parameter](hyp:K). [This is the stated defined object](goal). -/
abbrev CoefficientPairs (K : ℕ) := Fin (K+1) → Bool × Bool
/-- The bundled carrier supplies its declared mathematical structure. [This is the stated defined object](goal). -/
instance : MeasurableSpace (Option (Bool × Bool)) := ⊤
/-- Each fine node either reveals its coefficient pair or carries no disclosure. This statement assumes [the K parameter](hyp:K). [This is the stated defined object](goal). -/
abbrev Disclosure (K : ℕ) := Fin (K+1) → Option (Bool × Bool)
/-- The augmented data retain the full covariate design, mark indicators and boundary coefficient disclosure. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K). [This is the stated defined object](goal). -/
abbrev Augmentation (n K : ℕ) := (Fin n → unitInterval) × (Fin n → Bool) × Disclosure K
/-- Finite labels retain treatment and signed-mark coordinates, including the unused sign in a zero mark. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
abbrev Labels (n : ℕ) := Fin n → Bool × Bool
/-- A coefficient is disclosed precisely at a coarse boundary. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M), [the i parameter](hyp:i). [This is the stated defined object](goal). -/
def boundaryNode (K M : ℕ) (i : Fin (K+1)) : Prop := i.val*M % K = 0
/-- Reveal precisely the coefficient pairs at coarse boundaries. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M), [the pairs parameter](hyp:pairs). [This is the stated defined object](goal). -/
def disclose (K M : ℕ) (pairs : CoefficientPairs K) : Disclosure K :=
  fun i => if boundaryNode K M i then some (pairs i) else none
/-- Push fair fine-node coefficient pairs through the boundary-only disclosure map. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M). [This is the stated defined object](goal). -/
def disclosureLaw (K M : ℕ) : Measure (Disclosure K) :=
  ∑ pairs : CoefficientPairs K, ENNReal.ofReal ((4:ℝ)^(-(K+1:ℤ))) • Measure.dirac (disclose K M pairs)
/-- A mark indicator has the independent Bernoulli rare-mark probability. This statement assumes [the ε parameter](hyp:ε). [This is the stated defined object](goal). -/
def markFlagLaw (ε : ℝ) : Measure Bool := ENNReal.ofReal ε • Measure.dirac true+ENNReal.ofReal (1-ε) • Measure.dirac false
/-- Combine uniform covariates, independent mark indicators and fair boundary disclosure. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the ε parameter](hyp:ε). [This is the stated defined object](goal). -/
def commonAugmentation (n K M : ℕ) (ε : ℝ) : Measure (Augmentation n K) :=
  (Measure.pi fun _ : Fin n => design).prod ((Measure.pi fun _ : Fin n => markFlagLaw ε).prod (disclosureLaw K M))
/-- Fix disclosed pairs and retain the sign-copula probabilities of all undisclosed pairs. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the σ parameter](hyp:σ), [the δ parameter](hyp:δ), [the pairs parameter](hyp:pairs). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def conditionalPairWeight (ν : Bool) (K M : ℕ) (σ : Fin (M/2) → Bool)
    (δ : Disclosure K) (pairs : CoefficientPairs K) : ℝ :=
  ∏ i : Fin (K+1), match δ i with
    | some q => if pairs i = q then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (pairs i).1 (pairs i).2
/-- Conditional six-category densities relative to fair treatment/mark labels. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. [Defining clause 4](step:4) is used. -/
def labelDensity (ν : Bool) (K M : ℕ) (a u : ℝ) (idx : CopulaIndex K M)
    (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  let ξ := copulaXi K M a idx x
  let υ := copulaUpsilon K M u idx x
  let ζ := copulaZeta ν K M a u idx x
  if marked then 1+signVal label.1*ξ+signVal label.2*υ+signVal label.1*signVal label.2*ζ
  else 1+signVal label.1*ξ
/-- Recover original records by forgetting disclosure and the unused zero-mark sign. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the L parameter](hyp:L), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def augmentedObserve (n K : ℕ) (L : ℝ) (z : Augmentation n K × Labels n) : Dataset n :=
  fun i => (z.1.1 i,(z.2 i).1,if z.1.2.1 i then signVal (z.2 i).2*L else 0)
/-- Turn a finite fair-label density into the corresponding probability-table measure. This statement assumes [the n parameter](hyp:n), [the density parameter](hyp:density). [This is the stated defined object](goal). -/
def fairLabelMeasure (n : ℕ) (density : Labels n → ℝ) : Measure (Labels n) :=
  ∑ labels : Labels n, ENNReal.ofReal ((4:ℝ)^(-(n:ℤ))*density labels) • Measure.dirac labels

end CausalSmith.Stat.FinitepHomogeneityDensegamma
