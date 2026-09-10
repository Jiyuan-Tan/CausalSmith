import Causalean.Stat.Minimax.MinimaxValue
import Causalean.Stat.Minimax.MinimaxRisk
import Causalean.Stat.Sample.PiTransport
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure

set_option linter.style.longLine false

/-!
# Discrete optimal-value minimax model

Finite-PMF substrate for the observed and full-data experiments.  The general
regime-indexed potential-outcome API is intentionally bypassed because all
variables here are coordinates of a finite product.
-/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The treatment-outcome coordinate set. -/
abbrev Cell := Fin 2 × Fin 2 -- @realizes \(\mathcal J\)(four binary coordinates) @realizes \(\jmath\)(index in Cell)

/-- One observed unit. -/
abbrev Obs (d : ℕ) := Fin d × Bool × Bool
  -- @realizes \([d]\)(Fin d) @realizes \(X\)(first coordinate) @realizes \(A\)(second coordinate) @realizes \(Y\)(third coordinate) @realizes \(O_i\)(observed triple)

/-- A probability law on the observed finite alphabet. -/
structure DiscreteLaw (d : ℕ) where
  pmf : PMF (Obs d) -- @realizes \(\mathbb P\)(law on observed triples) @realizes \(\mathbf q\)(table of atom masses)

/-- For [the specified discrete law](hyp:P), the [observed-data law is the probability measure associated with the discrete probability mass function](goal). -/
noncomputable def obsLaw {d : ℕ} (P : DiscreteLaw d) : Measure (Obs d) := P.pmf.toMeasure

/-- For [the specified discrete law](hyp:P), the [observed-data law induced by a discrete law is a probability measure](goal). -/
instance {d : ℕ} (P : DiscreteLaw d) : IsProbabilityMeasure (obsLaw P) := by
  unfold obsLaw
  infer_instance

/-- An observed atom mass. -/
noncomputable def jointMass {d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (a y : Bool) : ℝ := (P.pmf (x, a, y)).toReal
  -- @realizes \(q_{ay,x}\)(joint atom probability)

/-- The four observed masses in one covariate cell. -/
noncomputable def cellVector {d : ℕ} (P : DiscreteLaw d) (x : Fin d) : Cell → ℝ :=
  fun j => jointMass P x (finTwoEquiv j.1) (finTwoEquiv j.2)
  -- @realizes \(q_x\)(four-vector) @realizes \(u\)(generic four-vector carrier)

/-- The mass of a covariate cell. -/
noncomputable def cellMass {d : ℕ} (P : DiscreteLaw d) (x : Fin d) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, jointMass P x a y
  -- @realizes \(p_x\)(marginal cell mass)

/-- The mass of one treatment arm within a covariate cell. -/
noncomputable def armMass {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) : ℝ :=
  ∑ y : Bool, jointMass P x a y

/-- The totalized propensity. -/
noncomputable def propensity {d : ℕ} (P : DiscreteLaw d) (x : Fin d) : ℝ :=
  armMass P true x / cellMass P x
  -- @realizes \(\pi_x\)(conditional treatment probability)

/-- The totalized binary outcome regression. -/
noncomputable def outcomeMean {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) : ℝ :=
  jointMass P x a true / armMass P a x
  -- @realizes \(\mu_{ax}\)(conditional binary outcome mean)

/-- Canonical finite product law. -/
noncomputable def productLaw {d : ℕ} (P : DiscreteLaw d) (n : ℕ) :
    Measure (Fin n → Obs d) := Measure.pi (fun _ : Fin n => obsLaw P)
  -- @realizes \(O_i\)(i.i.d. product sample) @realizes \(i\)(Fin n sample index)

/-- For [the specified discrete law](hyp:P), the [finite observed-data product law is a probability measure](goal). -/
instance {d n : ℕ} (P : DiscreteLaw d) : IsProbabilityMeasure (productLaw P n) := by
  unfold productLaw
  infer_instance

-- @env: S1
variable (n d : ℕ) -- @realizes \(n\)(sample size) @realizes \(d\)(alphabet size)
variable (epsilon : ℝ) -- @realizes \(\epsilon\)(overlap constant)
variable (x : Fin d) (a y : Bool) -- @realizes \(x\)(cell index) @realizes \(a\)(treatment index) @realizes \(y\)(outcome index)

-- @node: ass:iid-sampling
/-- The supplied sample law equals the canonical product law. -/
def IidSampling {d n : ℕ} (P : DiscreteLaw d)
    (mu_n : Measure (Fin n → Obs d)) : Prop := mu_n = productLaw P n

-- @node: ass:fixed-overlap
/-- Every occupied cell has propensity in the fixed overlap interval. -/
def Overlap {d : ℕ} (epsilon : ℝ) (P : DiscreteLaw d) : Prop :=
  ∀ x, 0 < cellMass P x →
    epsilon ≤ propensity P x ∧ propensity P x ≤ 1 - epsilon
    -- @realizes \(p_x\)(occupied-cell condition) @realizes \(\pi_x\)(overlap interval)

/-- A full-data atom `(X,A,Y,Y(0),Y(1))`. -/
abbrev FullObs (d : ℕ) := Fin d × Bool × Bool × Bool × Bool
  -- @realizes \(Y(a)\)(last two coordinates)

/-- A probability law on the full-data alphabet. -/
structure PotentialLaw (d : ℕ) where
  pmf : PMF (FullObs d) -- @realizes \(P\)(full-data law)

/-- For [the specified rectangle or law, data point or sample](hyp:Q,z), the [full-data atom mass is the real-valued probability assigned by the potential-outcome law to that atom](goal). -/
noncomputable def fullMass {d : ℕ} (Q : PotentialLaw d) (z : FullObs d) : ℝ :=
  (Q.pmf z).toReal

-- @env: S2
variable (Q : PotentialLaw d) -- @realizes \(P\)(full-data law)

-- @node: ass:consistency
/-- Observed outcomes equal the selected potential outcome almost surely. -/
def Consistency {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) → fullMass Q z = 0
  -- @realizes \(Y\)(selected outcome) @realizes \(A\)(selection arm) @realizes \(Y(a)\)(potential outcome)

/-- For [the specified rectangle or law, cell, treatment arm, y0, y1](hyp:Q,x,a,y0,y1), the [potential-outcome atom mass marginalizes the full-data law over the observed outcome while fixing covariate, treatment, and both potential outcomes](goal). -/
noncomputable def poAtom {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (a y0 y1 : Bool) : ℝ :=
  ∑ y : Bool, fullMass Q (x, a, y, y0, y1)

/-- The `(Y(r),A,X)` atom obtained by marginalizing the other potential outcome. -/
noncomputable def poArmAtom {d : ℕ} (Q : PotentialLaw d) (x : Fin d)
    (r : Fin 2) (a ya : Bool) : ℝ :=
  if r = 0 then ∑ y1 : Bool, poAtom Q x a ya y1
  else ∑ y0 : Bool, poAtom Q x a y0 ya

-- @node: ass:conditional-exchangeability
/-- Armwise finite conditional independence `Y(r) ⟂ A | X`, separately for each arm. -/
def ConditionalExchangeability {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ x r a ya,
    poArmAtom Q x r a ya * (∑ a' : Bool, ∑ y' : Bool, poArmAtom Q x r a' y') =
      (∑ a' : Bool, poArmAtom Q x r a' ya) *
        (∑ y' : Bool, poArmAtom Q x r a y')
  -- @realizes \(Y(a)\)(each potential outcome separately) @realizes \(A\)(armwise conditional independence) @realizes \(X\)(conditioning cell)

-- @node: def:observed-margin
/-- Push a full-data law to its observed margin. -/
noncomputable def observedMarginal {d : ℕ} (Q : PotentialLaw d) : DiscreteLaw d where
  pmf := Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))
  -- @realizes \(\operatorname{Obs}(P)\)(observed marginal)

-- @node: def:observed-model-class
/-- The unrestricted observed finite-law class, restricted only by overlap. -/
structure ObservedModelClass (epsilon : ℝ) {d : ℕ} (P : DiscreteLaw d) : Prop where
  d_ge_two : 2 ≤ d -- @realizes \(d\)(alphabet size at least two)
  epsilon_pos : 0 < epsilon -- @realizes \(\epsilon\)(strictly positive)
  epsilon_lt_half : epsilon < 1 / 2 -- @realizes \(\epsilon\)(strictly below one half)
  overlap : Overlap epsilon P -- @realizes \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\)(membership by overlap)

-- @node: def:model-class
/-- Consistent, exchangeable causal completions with an overlapping observed margin. -/
structure CausalCompletionClass (epsilon : ℝ) {d : ℕ} (Q : PotentialLaw d) : Prop where
  d_ge_two : 2 ≤ d -- @realizes \(d\)(alphabet size at least two)
  epsilon_pos : 0 < epsilon -- @realizes \(\epsilon\)(strictly positive)
  epsilon_lt_half : epsilon < 1 / 2 -- @realizes \(\epsilon\)(strictly below one half)
  consistency : Consistency Q
  exchangeability : ConditionalExchangeability Q
  overlap : Overlap epsilon (observedMarginal Q)
    -- @realizes \(\mathcal P_{d,\epsilon}\)(causal completion class)

/-- If [the potential-outcome law satisfies the stated causal restrictions](hyp:hQ), then [the observed marginal belongs to the observed model class](goal). -/
theorem CausalCompletionClass.observedModel {epsilon : ℝ} {d : ℕ} {Q : PotentialLaw d}
    (hQ : CausalCompletionClass epsilon Q) : ObservedModelClass epsilon (observedMarginal Q) :=
  ⟨hQ.d_ge_two, hQ.epsilon_pos, hQ.epsilon_lt_half, hQ.overlap⟩

/-- The observed-law factorization using the canonical cell mass, propensity, and regressions. This uses [the observed law satisfies the stated model restrictions](hyp:hP). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma observedModelClass_factorization {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    ∀ x a,
      jointMass P x a true = cellMass P x *
        (if a then propensity P x else 1 - propensity P x) * outcomeMean P a x ∧
      jointMass P x a false = cellMass P x *
        (if a then propensity P x else 1 - propensity P x) * (1 - outcomeMean P a x) := by
  intro x a
  have hmass (a y : Bool) : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
  have hcell : 0 ≤ cellMass P x := by
    simp [cellMass]
    nlinarith [hmass false false, hmass false true, hmass true false, hmass true true]
  by_cases hx : cellMass P x = 0
  · have hs : jointMass P x true true + jointMass P x true false +
        (jointMass P x false true + jointMass P x false false) = 0 := by
      simpa [cellMass] using hx
    have hz00 : jointMass P x false false = 0 := by
      nlinarith [hmass false false, hmass false true, hmass true false, hmass true true]
    have hz01 : jointMass P x false true = 0 := by
      nlinarith [hmass false false, hmass false true, hmass true false, hmass true true]
    have hz10 : jointMass P x true false = 0 := by
      nlinarith [hmass false false, hmass false true, hmass true false, hmass true true]
    have hz11 : jointMass P x true true = 0 := by
      nlinarith [hmass false false, hmass false true, hmass true false, hmass true true]
    fin_cases a <;> simp [propensity, outcomeMean, armMass, hx, hz00, hz01, hz10, hz11]
  · have hxpos : 0 < cellMass P x := lt_of_le_of_ne hcell (Ne.symm hx)
    have hov := hP.overlap x hxpos
    have ht : 0 < armMass P true x := by
      have : 0 < epsilon * cellMass P x := mul_pos hP.epsilon_pos hxpos
      exact lt_of_lt_of_le this ((le_div_iff₀ hxpos).mp hov.1)
    have hcell_eq : cellMass P x = armMass P false x + armMass P true x := by
      simp [cellMass, armMass]
      ring
    have hf : 0 < armMass P false x := by
      have hbound := hov.2
      rw [propensity, div_le_iff₀ hxpos] at hbound
      nlinarith [mul_pos hP.epsilon_pos hxpos]
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      unfold propensity outcomeMean <;>
      constructor <;>
      field_simp [hx, ne_of_gt ht, ne_of_gt hf] <;>
      simp [cellMass, armMass] at hcell_eq ⊢;
      nlinarith

/-- The formula underlying the observed optimal-regression value. -/
noncomputable def observedOptimalValueRaw {d : ℕ} (P : DiscreteLaw d) : ℝ :=
  ∑ x : Fin d, cellMass P x * max (outcomeMean P false x) (outcomeMean P true x)

-- @node: def:observed-optimal-value
/-- The optimal-regression value, defined only on the published observed model class. -/
noncomputable def observedOptimalValue {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (_hP : ObservedModelClass epsilon P) : ℝ :=
  observedOptimalValueRaw P
  -- @realizes \(\Psi(\mathbb P)\)(weighted cellwise optimal regression)

/-- Full-data cell mass. -/
noncomputable def poCellMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    fullMass Q (x, a, y, y0, y1)

/-- Totalized conditional potential-outcome mean. -/
noncomputable def poRegression {d : ℕ} (Q : PotentialLaw d) (a : Fin 2) (x : Fin d) : ℝ :=
  let numerator := ∑ arm : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    (if (if a = 0 then y0 else y1) then 1 else 0 : ℝ) * fullMass Q (x, arm, y, y0, y1)
  numerator / poCellMass Q x

-- @node: def:oracle-value
/-- The full-data unrestricted oracle value. -/
noncomputable def oracleValue {d : ℕ} (Q : PotentialLaw d) : ℝ :=
  ∑ x : Fin d, poCellMass Q x * max (poRegression Q 0 x) (poRegression Q 1 x)
  -- @realizes \(V^\star(P)\)(full-data oracle value)

/-- Measurable estimators for the fixed-sample experiment. -/
abbrev Estimator (n d : ℕ) := {f : (Fin n → Obs d) → ℝ // Measurable f}

/-- Observed laws packaged with model-class membership. -/
abbrev ModelLaw (d : ℕ) (epsilon : ℝ) :=
  {P : DiscreteLaw d // ObservedModelClass epsilon P}

/-- Statewise squared-error risk. -/
noncomputable def observedRisk (n : ℕ) {d : ℕ} (est : Estimator n d)
    (P : ModelLaw d epsilon) : ℝ :=
  Causalean.Stat.sqRisk (productLaw P.1 n) est.1 (observedOptimalValue P.1 P.2)

-- @node: def:minimax-risk
/-- Thin paper-local notation for the reused generic minimax value. -/
noncomputable abbrev minimaxRisk (n d : ℕ) (epsilon : ℝ) : ℝ :=
  Causalean.Stat.minimaxValue (observedRisk n (d := d) (epsilon := epsilon))
  -- @realizes \(\mathfrak R_{n,d,\epsilon}\)(minimax squared risk)

/-- For [the specified alphabet size, overlap level](hyp:d,epsilon), the [causal model law is a potential-outcome law belonging to the causal completion class at the chosen overlap level](goal). -/
abbrev CausalModelLaw (d : ℕ) (epsilon : ℝ) :=
  {Q : PotentialLaw d // CausalCompletionClass epsilon Q}

/-- For [the specified overlap level, sample size, estimator, rectangle or law](hyp:epsilon,n,est,Q), the [causal risk is the squared-error risk of the estimator under the observed marginal, with the potential-outcome oracle value as target](goal). -/
noncomputable def causalRisk (n : ℕ) {d : ℕ} (est : Estimator n d)
    (Q : CausalModelLaw d epsilon) : ℝ :=
  Causalean.Stat.sqRisk (productLaw (observedMarginal Q.1) n) est.1 (oracleValue Q.1)

/-- For [the specified sample size, alphabet size, overlap level](hyp:n,d,epsilon), the [causal minimax risk is the minimax squared-error risk over the causal model class](goal). -/
noncomputable def causalMinimaxRisk (n d : ℕ) (epsilon : ℝ) : ℝ :=
  Causalean.Stat.minimaxValue (causalRisk n (d := d) (epsilon := epsilon))

/-- The logarithmic alphabet scale. -/
noncomputable def logAlphabet (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)
  -- @realizes \(L_d\)(log(ed))

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
