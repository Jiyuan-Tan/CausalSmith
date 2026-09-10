import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Causalean.PO.ID.Partial.Basic
import Causalean.Stat.Sample

set_option linter.unusedVariables false

/-!
# Selective-label counterfactual-correctness models

Finite design, response-type, incidence, and endpoint-program primitives for
the selective-label/untrialed-policy paper.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

/-- A recorded label is either hidden or a revealed binary truth. -/
inductive MaskedLabel
  | hidden
  | revealed (z : Bool)
  deriving DecidableEq, Fintype

/-- The finite randomized design. -/
structure SLCCDesign where
  Stratum : Type
  Policy : Type
  TrialArm : Type
  Performance : Type
  [stratumFintype : Fintype Stratum]
  [stratumDecidableEq : DecidableEq Stratum]
  [policyFintype : Fintype Policy]
  [policyDecidableEq : DecidableEq Policy]
  [trialFintype : Fintype TrialArm]
  [trialDecidableEq : DecidableEq TrialArm]
  [performanceFintype : Fintype Performance]
  [performanceDecidableEq : DecidableEq Performance]
  [performanceLinearOrder : LinearOrder Performance]
  untrialed : Policy -- @realizes e(carrier e ∈ J)
  trialPolicy : TrialArm → Policy -- @realizes J_0(trial arms embedded in J)
  trialPolicy_injective : Function.Injective trialPolicy
  untrialed_not_trial : ∀ j, trialPolicy j ≠ untrialed
  qValue : Performance → ℝ -- @realizes Q_set(finite ordered values in ℝ)
  qValue_strictMono : StrictMono qValue
  qValue_pos : ∀ q, 0 < qValue q
  qValue_lt_one : ∀ q, qValue q < 1
  config : Policy → Stratum → Bool × Performance -- @realizes c_j(J-indexed configuration maps)
  rho : TrialArm → ℝ -- @realizes rho(carrier J_0 → ℝ)
  rho_pos : ∀ j, 0 < rho j -- @realizes rho(strictly positive coordinates)
  rho_sum : ∑ j, rho j = 1 -- @realizes rho(probability-vector normalization)

instance (d : SLCCDesign) : Fintype d.Stratum := d.stratumFintype
instance (d : SLCCDesign) : DecidableEq d.Stratum := d.stratumDecidableEq
instance (d : SLCCDesign) : Fintype d.Policy := d.policyFintype
instance (d : SLCCDesign) : DecidableEq d.Policy := d.policyDecidableEq
instance (d : SLCCDesign) : Fintype d.TrialArm := d.trialFintype
instance (d : SLCCDesign) : DecidableEq d.TrialArm := d.trialDecidableEq
instance (d : SLCCDesign) : Fintype d.Performance := d.performanceFintype
instance (d : SLCCDesign) : DecidableEq d.Performance := d.performanceDecidableEq
instance (d : SLCCDesign) : LinearOrder d.Performance := d.performanceLinearOrder

-- @env: S1
-- @realizes J(finite policy carrier)
-- @realizes J_0(finite trial-arm carrier)
-- @realizes S_set(finite stratum carrier)
-- @realizes R_set(binary recommendation carrier Bool)
-- @realizes Q_set(finite totally ordered performance carrier)
-- @realizes C_set(configuration carrier Bool × Performance)
variable (d : SLCCDesign)

/-- The neutral recommendation is zero/false. -/
def neutralRecommendation : Bool := false -- @realizes r_neu(r_neu = 0)

/-- All deterministic finite response coordinates before shape restrictions. -/
structure RawResponseType (d : SLCCDesign) where
  stratum : d.Stratum -- @realizes t(stratum coordinate)
  truth : Bool -- @realizes Z(binary truth coordinate)
  actionResponse : (Bool × d.Performance) → Bool -- @realizes A_c(binary configuration array)
  outcomeResponse : (Bool × d.Performance) → Bool -- @realizes Y_c(binary configuration array)
  deriving DecidableEq

noncomputable instance (d : SLCCDesign) : Fintype (RawResponseType d) :=
  Fintype.ofInjective
    (fun r => (r.stratum, r.truth, r.actionResponse, r.outcomeResponse)) (by
      intro a b h
      cases a
      cases b
      cases h
      rfl)

-- @realizes T_raw(S × Bool × Bool^C × Bool^C)
-- @realizes t(response-type carrier)
abbrev RawType (d : SLCCDesign) := RawResponseType d

/-- Unit-level counterfactual correctness. -/
-- @node: ass:counterfactual-correctness
def CounterfactualCorrectness (d : SLCCDesign) (z : Bool)
    (yc : (Bool × d.Performance) → Bool) : Prop :=
  ∀ r q r' q', r = z → r' ≠ z → yc (r', q') ≤ yc (r, q)

/-- Outcomes under a correct recommendation are nondecreasing in certified performance. -/
-- @node: ass:correct-performance-order
def CorrectPerformanceOrder (d : SLCCDesign) (z : Bool)
    (yc : (Bool × d.Performance) → Bool) : Prop :=
  ∀ q q', q ≤ q' → yc (z, q) ≤ yc (z, q')

/-- Outcomes under an incorrect recommendation are nonincreasing in certified performance. -/
-- @node: ass:incorrect-performance-order
def IncorrectPerformanceOrder (d : SLCCDesign) (z : Bool)
    (yc : (Bool × d.Performance) → Bool) : Prop :=
  ∀ q q', q ≤ q' → yc (!z, q') ≤ yc (!z, q)

/-- The neutral recommendation's outcome is invariant to performance. -/
-- @node: ass:neutral-performance-invariance
def NeutralPerformanceInvariance (d : SLCCDesign)
    (yc : (Bool × d.Performance) → Bool) : Prop :=
  ∀ q q', yc (neutralRecommendation, q) = yc (neutralRecommendation, q')

/-- A legal deterministic response type bundles exactly the four shape restrictions. -/
-- @node: def:legal-response-types
structure LegalResponseType (d : SLCCDesign) where -- @realizes T_SLCC(legal subtype of T_raw)
  raw : RawResponseType d -- @realizes t(legal response type)
  correctness : CounterfactualCorrectness d raw.truth raw.outcomeResponse
  correctOrder : CorrectPerformanceOrder d raw.truth raw.outcomeResponse
  incorrectOrder : IncorrectPerformanceOrder d raw.truth raw.outcomeResponse
  neutralInvariant : NeutralPerformanceInvariance d raw.outcomeResponse

noncomputable instance (d : SLCCDesign) : Fintype (LegalResponseType d) :=
  Fintype.ofInjective (fun t => t.raw) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

noncomputable instance (d : SLCCDesign) : DecidableEq (LegalResponseType d) :=
  Classical.decEq _

/-- Observable cells obey the selective-label masking rule. -/
def LabelCellValid (a : Bool) (ell : MaskedLabel) : Prop :=
  match a, ell with
  | false, .hidden => True
  | true, .revealed _ => True
  | _, _ => False

/-- A finite observable record `(D,S,A,Y,Z_obs)`. -/
structure ObservableCell (d : SLCCDesign) where
  arm : d.TrialArm
  stratum : d.Stratum
  action : Bool
  outcome : Bool
  label : MaskedLabel
  valid : LabelCellValid action label

noncomputable instance (d : SLCCDesign) : Fintype (ObservableCell d) :=
  Fintype.ofInjective (fun o => (o.arm, o.stratum, o.action, o.outcome, o.label)) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

noncomputable instance (d : SLCCDesign) : DecidableEq (ObservableCell d) :=
  Classical.decEq _

-- @realizes O_set(legal selectively labelled cells)
-- @realizes O_i(observed categorical record carrier)
abbrev ObservedRecord (d : SLCCDesign) := ObservableCell d

/-- The same record after forgetting the revealed label. -/
structure BlindCell (d : SLCCDesign) where
  arm : d.TrialArm
  stratum : d.Stratum
  action : Bool
  outcome : Bool
  deriving DecidableEq, Fintype

/-- Randomized policy assignment is independence from all response coordinates. -/
-- @node: ass:randomized-policy-assignment
def RandomizedPolicyAssignment {Ω : Type*} [MeasurableSpace Ω]
    (d : SLCCDesign) (μ : Measure Ω) (D : Ω → d.TrialArm)
    (S : Ω → d.Stratum) (Z : Ω → Bool)
    (Ac Yc : Ω → (Bool × d.Performance) → Bool) : Prop :=
  ∀ (A : Set d.TrialArm)
      (B : Set (d.Stratum × Bool ×
        ((Bool × d.Performance) → Bool) × ((Bool × d.Performance) → Bool))),
    μ ({ω | D ω ∈ A} ∩ {ω | (S ω, Z ω, Ac ω, Yc ω) ∈ B}) =
      μ {ω | D ω ∈ A} * μ {ω | (S ω, Z ω, Ac ω, Yc ω) ∈ B}

/-- Every randomized trial arm has its known design probability. -/
-- @node: ass:known-arm-law
def KnownArmLaw {Ω : Type*} [MeasurableSpace Ω] (d : SLCCDesign)
    (μ : Measure Ω) (D : Ω → d.TrialArm) : Prop :=
  ∀ j, μ {ω | D ω = j} = ENNReal.ofReal (d.rho j)

/-- The realized action reads the common response array at the assigned configuration. -/
-- @node: ass:common-action-response
def CommonActionResponse {Ω : Type*} (d : SLCCDesign)
    (D : Ω → d.TrialArm) (S : Ω → d.Stratum)
    (Ac : Ω → (Bool × d.Performance) → Bool) (A : Ω → Bool) : Prop :=
  ∀ ω, A ω = Ac ω (d.config (d.trialPolicy (D ω)) (S ω))

/-- The realized outcome reads the common response array at the assigned configuration. -/
-- @node: ass:common-outcome-response
def CommonOutcomeResponse {Ω : Type*} (d : SLCCDesign)
    (D : Ω → d.TrialArm) (S : Ω → d.Stratum)
    (Yc : Ω → (Bool × d.Performance) → Bool) (Y : Ω → Bool) : Prop :=
  ∀ ω, Y ω = Yc ω (d.config (d.trialPolicy (D ω)) (S ω))

/-- Revelation is exactly the endogenous action. -/
-- @node: ass:reveal-action
def RevealAction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R A : Ω → Bool) : Prop := R =ᵐ[μ] A

/-- The observed truth is revealed precisely on the revelation event. -/
-- @node: ass:masked-truth
def MaskedTruth {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z R : Ω → Bool) (Zobs : Ω → MaskedLabel) : Prop :=
  Zobs =ᵐ[μ] fun ω => if R ω then .revealed (Z ω) else .hidden

/-- A finite randomized selective-label model carrying all ten assumptions. -/
-- @node: def:slcc-scm-class
structure SLCCModel (d : SLCCDesign) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where -- @realizes M_SLCC(model class)
  D : Ω → d.TrialArm -- @realizes D(random trial-arm variable)
  S : Ω → d.Stratum -- @realizes S(random stratum variable)
  Z : Ω → Bool -- @realizes Z(binary truth variable)
  Ac : Ω → (Bool × d.Performance) → Bool -- @realizes A_c(random response array)
  Yc : Ω → (Bool × d.Performance) → Bool -- @realizes Y_c(random response array)
  A : Ω → Bool -- @realizes A(binary realized action)
  Y : Ω → Bool -- @realizes Y(binary realized outcome)
  R : Ω → Bool -- @realizes R(binary revelation indicator)
  Zobs : Ω → MaskedLabel -- @realizes Z_obs(masked-label variable)
  randomized : RandomizedPolicyAssignment d μ D S Z Ac Yc
  knownLaw : KnownArmLaw d μ D
  commonAction : CommonActionResponse d D S Ac A
  commonOutcome : CommonOutcomeResponse d D S Yc Y
  revealAction : RevealAction μ R A
  maskedTruth : MaskedTruth μ Z R Zobs
  correctness : ∀ ω, CounterfactualCorrectness d (Z ω) (Yc ω)
  correctOrder : ∀ ω, CorrectPerformanceOrder d (Z ω) (Yc ω)
  incorrectOrder : ∀ ω, IncorrectPerformanceOrder d (Z ω) (Yc ω)
  neutralInvariant : ∀ ω, NeutralPerformanceInvariance d (Yc ω)

/-- The latent response-type simplex. -/
-- @node: def:response-simplex
def responseSimplex (d : SLCCDesign) : Set (LegalResponseType d → ℝ) :=
  stdSimplex ℝ (LegalResponseType d) -- @realizes Delta_SLCC(w ≥ 0 and sum w = 1)

/-- The selective-label incidence matrix. -/
-- @node: def:selective-label-incidence-map
def incidence (d : SLCCDesign) :
    Matrix (ObservableCell d) (LegalResponseType d) ℝ := fun o t =>
  if t.raw.stratum = o.stratum ∧
      t.raw.actionResponse (d.config (d.trialPolicy o.arm) o.stratum) = o.action ∧
      t.raw.outcomeResponse (d.config (d.trialPolicy o.arm) o.stratum) = o.outcome ∧
      o.label = (if o.action then .revealed t.raw.truth else .hidden)
    then d.rho o.arm else 0 -- @realizes B(rho-weighted legal-cell incidence)

/-- The untrialed binary target on a legal response type. -/
def targetVector (d : SLCCDesign) (t : LegalResponseType d) : ℝ :=
  if t.raw.outcomeResponse (d.config d.untrialed t.raw.stratum) then 1 else 0
  -- @realizes h_e(h_e(t) = y at c_e(s))

/-- A generic finite incidence geometry, including its label coarsening. -/
structure SLCCIncidence (O T OBlind : Type*) [Fintype O] where
  B : Matrix O T ℝ -- @realizes B(finite incidence matrix carrier)
  B_nonnegative : ∀ o t, 0 ≤ B o t
  B_column_sum : ∀ t, ∑ o, B o t = 1
  h : T → ℝ -- @realizes h_e(binary target-vector carrier)
  h_binary : ∀ t, h t = 0 ∨ h t = 1
  K : Matrix OBlind O ℝ -- @realizes K_blind(label-coarsening matrix carrier)

-- @env: S2
-- @realizes w(finite real response-weight vector)
-- @realizes p(finite real observable-law vector)
variable {O T OBlind : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]
  (G : SLCCIncidence O T OBlind)

/-- The value of the causal target under latent weights. -/
def targetFunctional (G : SLCCIncidence O T OBlind) (w : T → ℝ) : ℝ :=
  ∑ t, G.h t * w t -- @realizes tau_e(h_eᵀw)

/-- The observable law induced by latent weights. -/
def observableLaw (G : SLCCIncidence O T OBlind) (w : T → ℝ) : O → ℝ :=
  G.B.mulVec w -- @realizes p(p = Bw)

/-- The finite observable-law polytope. -/
def observablePolytope (G : SLCCIncidence O T OBlind) : Set (O → ℝ) :=
  {p | ∃ w ∈ stdSimplex ℝ T, G.B.mulVec w = p}
  -- @realizes O_poly(B Delta_SLCC)

/-- The feasible latent fiber above an observable law. -/
def responseFiber (G : SLCCIncidence O T OBlind) (p : O → ℝ) : Set (T → ℝ) :=
  {w | w ∈ stdSimplex ℝ T ∧ G.B.mulVec w = p}

/-- The two sharp endpoint value functions `(L,U)`. -/
-- @node: def:sharp-endpoint-programs
noncomputable def sharpEndpointPrograms (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) : ℝ × ℝ :=
  let values := targetFunctional G '' responseFiber G p
  (sInf values, sSup values)
  -- @realizes L(minimum over the response fiber)
  -- @realizes U(maximum over the response fiber)
  -- @realizes theta(pair (L,U))

/-- The lower sharp endpoint. -/
noncomputable def lowerEndpoint (G : SLCCIncidence O T OBlind) (p : O → ℝ) : ℝ :=
  (sharpEndpointPrograms G p).1

/-- The upper sharp endpoint. -/
noncomputable def upperEndpoint (G : SLCCIncidence O T OBlind) (p : O → ℝ) : ℝ :=
  (sharpEndpointPrograms G p).2

/-- The coarsened incidence matrix. -/
def blindIncidence (G : SLCCIncidence O T OBlind) : Matrix OBlind T ℝ :=
  G.K * G.B -- @realizes B_blind(B_blind = K_blind B)

/-- The coarsened observable law. -/
def blindLaw (G : SLCCIncidence O T OBlind) (p : O → ℝ) : OBlind → ℝ :=
  G.K.mulVec p -- @realizes p_blind(p_blind = K_blind p)

/-- The two endpoint programs after discarding the revealed truth label. -/
-- @node: def:z-blind-projection
noncomputable def blindEndpointPrograms (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) : ℝ × ℝ :=
  let values := targetFunctional G ''
    {w | w ∈ stdSimplex ℝ T ∧ (blindIncidence G).mulVec w = blindLaw G p}
  (sInf values, sSup values)
  -- @realizes L_blind(minimum under coarsened constraints)
  -- @realizes U_blind(maximum under coarsened constraints)

/-- The i.i.d. finite-cell sampling assumption, retaining the exact library bundle. -/
-- @node: ass:iid-finite-sampling
def IidFiniteSampling {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    (μ : Measure Ω)
    (P : Measure O) (S : Causalean.Stat.IIDSample Ω O μ P)
    (G : SLCCIncidence O T OBlind) (p : O → ℝ) : Prop :=
  p ∈ observablePolytope G ∧ ∀ o, P {o} = ENNReal.ofReal (p o)

/-- Weak convergence, expressed by bounded continuous test functions. -/
def WeakConvergence {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] (μ : Measure Ω) (Xn : ℕ → Ω → E) (Q : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
    Filter.Tendsto (fun n => ∫ ω, f (Xn n ω) ∂μ) Filter.atTop
      (nhds (∫ x, f x ∂Q))

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
