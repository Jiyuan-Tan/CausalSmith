module
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Minimax.MinimaxRisk
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProductMeasure

/-!
# Vanishing-overlap optimal value: finite observed and causal models

The finite PMF abstraction retains arbitrary and null covariate cells.
The measure-theoretic PO and MinimaxATE systems use a different model,
so only their generic minimax risk primitives are imported.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- For [the displayed parameters](hyp:d), [Obs](goal) is the object specified by this definition. -/
abbrev Obs (d : ℕ) := Fin d × Bool × Bool
  -- @realizes \([d]\)(Fin d) @realizes \(\mathcal J_d\)(observed alphabet)
  -- @realizes \(j\)(generic category index)
  -- @realizes \(X\)(first coordinate) @realizes \(A\)(second coordinate)
  -- @realizes \(Y\)(third coordinate) @realizes \(O_i\)(observed unit)

/-- For [the displayed parameters](hyp:d), [DiscreteLaw](goal) is the object specified by this definition. -/
structure DiscreteLaw (d : ℕ) where
  pmf : PMF (Obs d) -- @realizes \(\mathbb P\)(probability law)

/-- For [the displayed parameters](hyp:d,P,x,a,y), [jointMass](goal) is the object specified by this definition. -/
noncomputable def jointMass {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (a y : Bool) : ℝ := (P.pmf (x, a, y)).toReal
  -- @realizes \(q_{ay,x}\)(atom mass) @realizes \(q_j\)(category mass)

/-- For [the displayed parameters](hyp:a,y), [cellIdx](goal) is the object specified by this definition. -/
def cellIdx (a y : Bool) : Fin 4 :=
  ⟨2 * (if a then 1 else 0) + (if y then 1 else 0),
    by cases a <;> cases y <;> decide⟩

/-- For [the displayed parameters](hyp:d,P,x), [cellVector](goal) is the object specified by this definition. -/
noncomputable def cellVector {d : ℕ} (P : DiscreteLaw d) (x : Fin d) : Fin 4 → ℝ :=
  fun j => jointMass P x (j.val / 2 = 1) (j.val % 2 = 1)
  -- @realizes \(q_x\)(four atom masses)

/-- For [the displayed parameters](hyp:d,P,x), [cellMass](goal) is the object specified by this definition. -/
noncomputable def cellMass {d : ℕ} (P : DiscreteLaw d) (x : Fin d) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, jointMass P x a y
  -- @realizes \(p_x\)(covariate marginal)

/-- For [the displayed parameters](hyp:d,P,a,x), [armMass](goal) is the object specified by this definition. -/
noncomputable def armMass {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) : ℝ :=
  ∑ y : Bool, jointMass P x a y

/-- For [the displayed parameters](hyp:d,P,x), [propensity](goal) is the object specified by this definition. -/
noncomputable def propensity {d : ℕ} (P : DiscreteLaw d) (x : Fin d) : ℝ :=
  armMass P true x / cellMass P x
  -- @realizes \(\pi_x\)(occupied-cell propensity)

/-- For [the displayed parameters](hyp:d,P,a,x), [outcomeMean](goal) is the object specified by this definition. -/
noncomputable def outcomeMean {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) : ℝ :=
  jointMass P x a true / armMass P a x
  -- @realizes \(\mu_{ax}\)(armwise outcome mean)

/-- For [the displayed parameters](hyp:d,P,n), [productLaw](goal) is the object specified by this definition. -/
noncomputable def productLaw {d : ℕ} (P : DiscreteLaw d) (n : ℕ) :
    Measure (Fin n → Obs d) := Measure.pi (fun _ : Fin n => P.pmf.toMeasure)
  -- @realizes \(i\)(Fin n sample index)

/-- For [the displayed parameters](hyp:d), [FullObs](goal) is the object specified by this definition. -/
abbrev FullObs (d : ℕ) := Fin d × Bool × Bool × Bool × Bool
  -- @realizes \(Y(a)\)(last two coordinates)

/-- For [the displayed parameters](hyp:d), [PotentialLaw](goal) is the object specified by this definition. -/
structure PotentialLaw (d : ℕ) where
  pmf : PMF (FullObs d) -- @realizes \(P\)(full-data law)

/-- For [the displayed parameters](hyp:d,Q,z), [fullMass](goal) is the object specified by this definition. -/
noncomputable def fullMass {d : ℕ} (Q : PotentialLaw d) (z : FullObs d) : ℝ :=
  (Q.pmf z).toReal

/-- For [the displayed parameters](hyp:d,Q), [observedMarginal](goal) is the object specified by this definition. -/
noncomputable def observedMarginal {d : ℕ} (Q : PotentialLaw d) : DiscreteLaw d where
  pmf := Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))
  -- @realizes \(\operatorname{Obs}(P)\)(observed margin)

/-- For [the displayed parameters](hyp:d,Q,x), [poCellMass](goal) is the object specified by this definition. -/
noncomputable def poCellMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    fullMass Q (x, a, y, y0, y1)

/-- For [the displayed parameters](hyp:d,Q,x,a,y0,y1), [poAtom](goal) is the object specified by this definition. -/
noncomputable def poAtom {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (a y0 y1 : Bool) : ℝ :=
  ∑ y : Bool, fullMass Q (x, a, y, y0, y1)

/-- For [the displayed parameters](hyp:d,Q,x,r,a,ya), [poArmAtom](goal) is the object specified by this definition. -/
noncomputable def poArmAtom {d : ℕ} (Q : PotentialLaw d) (x : Fin d)
    (r : Fin 2) (a ya : Bool) : ℝ :=
  if r = 0 then ∑ y1 : Bool, poAtom Q x a ya y1
  else ∑ y0 : Bool, poAtom Q x a y0 ya

/-- For [the displayed parameters](hyp:d,Q,x,a), [poTreatMass](goal) is the object specified by this definition. -/
noncomputable def poTreatMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) (a : Bool) : ℝ :=
  ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool, fullMass Q (x, a, y, y0, y1)

/-- For [the displayed parameters](hyp:d,Q,x,r,ya), [poPotentialMass](goal) is the object specified by this definition. -/
noncomputable def poPotentialMass {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (r : Fin 2) (ya : Bool) : ℝ :=
  ∑ a : Bool, poArmAtom Q x r a ya

/-- For [the displayed parameters](hyp:d,Q,r,x), [poRegression](goal) is the object specified by this definition. -/
noncomputable def poRegression {d : ℕ} (Q : PotentialLaw d)
    (r : Fin 2) (x : Fin d) : ℝ :=
  (∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    (if (if r = 0 then y0 else y1) then 1 else 0 : ℝ) *
      fullMass Q (x, a, y, y0, y1)) / poCellMass Q x

/-- For [the displayed parameters](hyp:d,Q), [oracleValue](goal) is the object specified by this definition. -/
noncomputable def oracleValue {d : ℕ} (Q : PotentialLaw d) : ℝ :=
  ∑ x : Fin d, poCellMass Q x * max (poRegression Q 0 x) (poRegression Q 1 x)
  -- @realizes \(V^\star(P)\)(causal oracle value)

-- @env: S1
variable (n d : ℕ) (ε : ℝ) (x : Fin d) (a y : Bool)
  -- @realizes \(n\)(sample size) @realizes \(d\)(cell count)
  -- @realizes \(\epsilon\)(overlap floor) @realizes \(x\)(cell)
  -- @realizes \(a\)(arm) @realizes \(y\)(outcome)
variable (hd : 2 ≤ d) -- @realizes \(d\)(at least two cells)
variable (hε : 0 < ε ∧ ε ≤ 1 / 2) -- @realizes \(\epsilon\)(public floor in (0, 1/2])

-- @node: ass:iid-sampling
/-- For [the displayed parameters](hyp:d,n,P), [IidSampling](goal) is the object specified by this definition. -/
def IidSampling {d n : ℕ} (P : DiscreteLaw d)
    (μn : Measure (Fin n → Obs d)) : Prop := μn = productLaw P n

-- @node: ass:shrinking-overlap
/-- For [the displayed parameters](hyp:d,P), [Overlap](goal) is the object specified by this definition. -/
def Overlap {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) : Prop :=
  ∀ x, 0 < cellMass P x →
    ε ≤ propensity P x ∧ propensity P x ≤ 1 - ε
    -- @realizes \(p_x\)(occupied cells) @realizes \(\pi_x\)(overlap range)

-- @env: S2
variable (Q : PotentialLaw d) -- @realizes \(P\)(full law)

-- @node: ass:consistency
/-- For [the displayed parameters](hyp:d,Q), [Consistency](goal) is the object specified by this definition. -/
def Consistency {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) → Q.pmf z = 0
  -- @realizes \(Y(a)\)(selected potential outcome equals observed outcome)

-- @node: ass:conditional-exchangeability
/-- For [the displayed parameters](hyp:d,Q), [ConditionalExchangeability](goal) is the object specified by this definition. -/
def ConditionalExchangeability {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ x r a ya,
    poArmAtom Q x r a ya * poCellMass Q x =
      poTreatMass Q x a * poPotentialMass Q x r ya
  -- @realizes \(Y(a)\)(armwise conditional independence)

-- @node: def:observed-class
/-- For [the displayed parameters](hyp:d,P), [ObservedClass](goal) is the object specified by this definition. -/
structure ObservedClass {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) : Prop where
  overlap : Overlap ε P -- @realizes \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\)(observed class)

-- @node: def:causal-class
/-- For [the displayed parameters](hyp:d,Q), [CausalClass](goal) is the object specified by this definition. -/
structure CausalClass {d : ℕ} (ε : ℝ) (Q : PotentialLaw d) : Prop where
  consistency : Consistency Q
  exchangeability : ConditionalExchangeability Q
  overlap : Overlap ε (observedMarginal Q)
    -- @realizes \(\mathcal P_{d,\epsilon}\)(causal completion class)

-- @node: def:observed-value
/-- For [the displayed parameters](hyp:d,P), [observedValue](goal) is the object specified by this definition. -/
noncomputable def observedValue {d : ℕ} (P : DiscreteLaw d) : ℝ :=
  ∑ x : Fin d, cellMass P x * max (outcomeMean P false x) (outcomeMean P true x)
  -- @realizes \(\Psi(\mathbb P)\)(optimal regression value)

/-- For [the displayed parameters](hyp:n,d), [Estimator](goal) is the object specified by this definition. -/
abbrev Estimator (n d : ℕ) := {f : (Fin n → Obs d) → ℝ // Measurable f}
/-- For [the displayed parameters](hyp:d), [ModelLaw](goal) is the object specified by this definition. -/
abbrev ModelLaw (d : ℕ) (ε : ℝ) := {P : DiscreteLaw d // ObservedClass ε P}
/-- For [the displayed parameters](hyp:d), [CausalModelLaw](goal) is the object specified by this definition. -/
abbrev CausalModelLaw (d : ℕ) (ε : ℝ) := {Q : PotentialLaw d // CausalClass ε Q}

/-- For [the displayed parameters](hyp:n,d,est,P), [observedRisk](goal) is the object specified by this definition. -/
noncomputable def observedRisk (n : ℕ) {d : ℕ} {ε : ℝ}
    (est : Estimator n d) (P : ModelLaw d ε) : ℝ :=
  Causalean.Stat.sqRisk (productLaw P.1 n) est.1 (observedValue P.1)

/-- For [the displayed parameters](hyp:n,d), [minimaxRisk](goal) is the object specified by this definition. -/
noncomputable abbrev minimaxRisk (n d : ℕ) (ε : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal (observedRisk n (d := d) (ε := ε))
  -- @realizes \(\mathfrak R_{n,d,\epsilon}\)(all-estimator minimax risk)

/-- For [the displayed parameters](hyp:n,d,est,Q), [causalRisk](goal) is the object specified by this definition. -/
noncomputable def causalRisk (n : ℕ) {d : ℕ} {ε : ℝ}
    (est : Estimator n d) (Q : CausalModelLaw d ε) : ℝ :=
  Causalean.Stat.sqRisk (productLaw (observedMarginal Q.1) n) est.1 (oracleValue Q.1)

/-- For [the displayed parameters](hyp:n,d), [causalMinimaxRisk](goal) is the object specified by this definition. -/
noncomputable def causalMinimaxRisk (n d : ℕ) (ε : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal (causalRisk n (d := d) (ε := ε))

/-- For [the displayed parameters](hyp:d), [logAlphabet](goal) is the object specified by this definition. -/
noncomputable def logAlphabet (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)
  -- @realizes \(L_d\)(log(ed))


/-- For [the displayed parameters](hyp:n,d), [rateScale](goal) is the object specified by this definition. -/
noncomputable def rateScale (n d : ℕ) (ε : ℝ) : ℝ :=
  min 1 ((d : ℝ) / (n * ε * logAlphabet d))

end CausalSmith.Stat.OptvalueVanishingoverlapRate
