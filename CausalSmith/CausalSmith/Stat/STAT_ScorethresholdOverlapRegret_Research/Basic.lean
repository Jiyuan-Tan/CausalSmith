module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Score-threshold overlap regret — shared world and law class

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @env: S1
variable (α γ θ : ℝ) -- @realizes alpha(carrier ℝ); @realizes gamma(carrier ℝ); @realizes theta(carrier ℝ)

/-- The standing range of the three public exponents. -/
def PublicExponents (α γ θ : ℝ) : Prop :=
  0 < α ∧ -- @realizes alpha(positive public exponent)
  0 < γ ∧ -- @realizes gamma(positive public exponent)
  0 < θ   -- @realizes theta(positive public exponent)

/-- A full potential-outcome row. The coordinate ranges are pinned by `WellFormed` and `BoundedPotentials`. -/
structure FullRow where
  X : ℝ -- @realizes X(score coordinate; Xspace=[0,1] via WellFormed)
  A : Bool -- @realizes A(Bool realizes treatment); @realizes Aspace({0,1} via Bool)
  Y : ℝ -- @realizes Y(outcome coordinate); @realizes Yspace([-1,1] via WellFormed)
  Y0 : ℝ -- @realizes Yzero(control potential; Yspace=[-1,1] via BoundedPotentials)
  Y1 : ℝ -- @realizes Yone(treated potential; Yspace=[-1,1] via BoundedPotentials)

instance : MeasurableSpace FullRow :=
  MeasurableSpace.comap (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) inferInstance

/-- The observed row. -/
structure Observation where
  X : ℝ -- @realizes O(observed score; Xspace=[0,1])
  A : Bool -- @realizes O(observed treatment; Aspace={0,1})
  Y : ℝ -- @realizes O(observed outcome; Yspace=[-1,1])

instance : MeasurableSpace Observation :=
  MeasurableSpace.comap (fun o : Observation => (o.X, o.A, o.Y)) inferInstance

/-- A law together with versions of the propensity and conditional effect, and its sampling law. -/
structure RowLaw where
  full : Measure FullRow -- @realizes P(full potential-outcome row measure; probability via WellFormed)
  logger : ℝ → ℝ -- @realizes e(carrier Xspace→ℝ; conditional propensity via WellFormed)
  tau : ℝ → ℝ -- @realizes tau(carrier Xspace→ℝ; conditional effect via WellFormed)
  samples : (n : ℕ) → Measure (Fin n → Observation) -- @realizes data(row-n sample distribution)

/-- Score marginal. -/
noncomputable def RowLaw.PX (P : RowLaw) : Measure ℝ :=
  P.full.map FullRow.X -- @realizes PX(P_X is the X marginal)

/-- Observable marginal. -/
noncomputable def RowLaw.obsLaw (P : RowLaw) : Measure Observation :=
  P.full.map fun o => ⟨o.X, o.A, o.Y⟩ -- @realizes O(O=(X,A,Y))

/-- Ambient probability, support, and tested conditional-mean clauses. -/
def WellFormed (P : RowLaw) : Prop :=
  IsProbabilityMeasure P.full ∧ -- @realizes P(probability law)
  P.full {o | o.X ∉ Set.Icc (0:ℝ) 1} = 0 ∧ -- @realizes Xspace(X is supported on [0,1])
  P.full {o | o.Y ∉ Set.Icc (-1:ℝ) 1} = 0 ∧ -- @realizes Yspace(observed outcome in [-1,1] almost surely)
  Measurable (fun x : Set.Icc (0:ℝ) 1 => P.logger x) ∧
  Measurable (fun x : Set.Icc (0:ℝ) 1 => P.tau x) ∧
  (∀ B : Set ℝ, MeasurableSet B →
    ∫ o in {o | o.X ∈ B}, (if o.A then (1:ℝ) else 0) ∂P.full =
      ∫ x in B, P.logger x ∂P.PX) ∧ -- @realizes e(e(x)=P(A=1|X=x), tested on B)
  (∀ B : Set ℝ, MeasurableSet B →
    ∫ o in {o | o.X ∈ B}, (o.Y1-o.Y0) ∂P.full =
      ∫ x in B, P.tau x ∂P.PX) -- @realizes tau(tau=E[Y1-Y0|X], tested on B)

-- @node: ass:bounded-potentials
/-- Both potential outcomes lie in [-1,1] almost surely. -/
def BoundedPotentials (P : RowLaw) : Prop :=
  ∀ᵐ o ∂P.full, o.Y0 ∈ Set.Icc (-1:ℝ) 1 ∧ o.Y1 ∈ Set.Icc (-1:ℝ) 1 -- @realizes Yzero(Y0 in Yspace); @realizes Yone(Y1 in Yspace); @realizes Yspace(potential outcomes in [-1,1] almost surely)

/-- A row law with the probability, conditional-version, and potential-outcome
range clauses required by public functionals. -/
abbrev WellFormedLaw := {P : RowLaw // WellFormed P ∧ BoundedPotentials P}

/-- Package the two independently reusable law conditions for public functionals. -/
def RowLaw.toWellFormedLaw (P : RowLaw) (hwf : WellFormed P)
    (hbounded : BoundedPotentials P) : WellFormedLaw :=
  ⟨P, hwf, hbounded⟩

/-- Weak-arm propensity. -/
def overlap (P : RowLaw) (x : ℝ) : ℝ :=
  min (P.logger x) (1 - P.logger x) -- @realizes p(p=min(e,1-e))

/-- Effect magnitude. -/
def effectMagnitude (P : RowLaw) (x : ℝ) : ℝ :=
  |P.tau x| -- @realizes tabs(t=|tau|)

/-- Tie-favoring canonical policy. -/
noncomputable def canonicalPolicy (P : RowLaw) (x : ℝ) : Bool :=
  decide (0 ≤ P.tau x) -- @realizes pistar(pi*=1{tau≥0})

-- @env: S2
variable (n : ℕ) (d : Fin n → Observation) -- @realizes n(sample size ℕ; positive in theorem binders)

/-- Canonical product sample law. -/
noncomputable def sampleLaw (P : RowLaw) (n : ℕ) : Measure (Fin n → Observation) :=
  Measure.pi fun _ : Fin n => P.obsLaw -- @realizes data(P^⊗n)

/-- Independent uniform learner randomization. -/
noncomputable def uniformRandomizer : Measure ℝ :=
  volume.restrict (Set.Icc (0:ℝ) 1) -- @realizes U(Unif[0,1])

noncomputable def experiment (P : RowLaw) (n : ℕ) :
    Measure ((Fin n → Observation) × ℝ) :=
  (sampleLaw P n).prod uniformRandomizer -- @realizes U(independent of data by product law)

/-- Empirical average. -/
noncomputable def empiricalAverage {n : ℕ} (f : Observation → ℝ) (d : Fin n → Observation) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (d i) -- @realizes Pn(P_n f = n⁻¹ sum_i f(O_i))

-- @env: S3
variable (π : ℝ → Bool)

/-- Left orientation threshold. -/
noncomputable def leftThr (t : ℝ) (x : ℝ) : Bool := decide (x ≤ t)
/-- Right orientation threshold. -/
noncomputable def rightThr (t : ℝ) (x : ℝ) : Bool := decide (t ≤ x)

-- @node: def:threshold-class
/-- Both threshold orientations and both constant rules. -/
def thresholdClass : Set (ℝ → Bool) :=
  {π | (∀ x ∈ Set.Icc (0:ℝ) 1, π x = false) ∨
    (∀ x ∈ Set.Icc (0:ℝ) 1, π x = true) ∨
    (∃ t ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ Set.Icc (0:ℝ) 1, π x = leftThr t x) ∨
    (∃ t ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ Set.Icc (0:ℝ) 1, π x = rightThr t x)} -- @realizes Pi(two orientations plus constants on Xspace)

-- @node: def:binary-policy-class
/-- Ambient Borel binary policies. -/
def binaryPolicyClass : Set (ℝ → Bool) :=
  {φ | Measurable (fun x : Set.Icc (0:ℝ) 1 => φ x)} -- @realizes Bclass(Borel binary policies on Xspace)

/-- A fixed-logger randomized learner family. -/
abbrev Learner (n : ℕ) :=
  (ℝ → ℝ) → (Fin n → Observation) → ℝ → ℝ → Bool

-- @node: def:binary-learner-class
/-- Measurability is required separately for each fixed supplied logger. -/
def LearnerClass (n : ℕ) (Φ : Learner n) : Prop :=
  ∀ e : ℝ → ℝ,
    Measurable (fun x : Set.Icc (0:ℝ) 1 => e x) →
    (∀ x ∈ Set.Icc (0:ℝ) 1, e x ∈ Set.Ioo (0:ℝ) 1) →
    Measurable (fun z : (Fin n → {o : Observation //
        o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1}) ×
        Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 =>
      Φ e (fun i => (z.1 i).1) z.2.1.1 z.2.2.1) ∧
    (∀ e' : ℝ → ℝ, Set.EqOn e e' (Set.Icc (0:ℝ) 1) →
      ∀ z : (Fin n → {o : Observation //
          o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1}) ×
          Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1,
        Φ e (fun i => (z.1 i).1) z.2.1.1 z.2.2.1 =
          Φ e' (fun i => (z.1 i).1) z.2.1.1 z.2.2.1) -- @realizes Aclass(logger indexing depends only on Xspace)

/-- Identified policy welfare. -/
noncomputable def rawWelfare (P : RowLaw) (φ : ℝ → Bool) : ℝ :=
  ∫ x, (if φ x then (1:ℝ) else 0) * P.tau x ∂P.PX -- @realizes V(V_P(phi)=E[phi(X)tau(X)])

-- @node: def:welfare
/-- The welfare functional has the paper's Borel-policy domain. -/
noncomputable def welfare (P : WellFormedLaw) (φ : {φ : ℝ → Bool // φ ∈ binaryPolicyClass}) : ℝ := -- @realizes phi(ambient binary policy)
  rawWelfare P.1 φ.1

/-- Welfare regret. -/
noncomputable def rawRegret (P : RowLaw) (φ : ℝ → Bool) : ℝ :=
  rawWelfare P (canonicalPolicy P) - rawWelfare P φ

-- @node: def:regret
/-- Regret on the paper's Borel-policy domain. -/
noncomputable def regret (P : WellFormedLaw) (φ : {φ : ℝ → Bool // φ ∈ binaryPolicyClass}) : ℝ :=
  rawRegret P.1 φ.1 -- @realizes R(R_P(phi)=V_P(pi*)-V_P(phi))

/-- Restrict an ambient representative to the Borel-policy domain; invalid sections
are assigned the constant policy outside the experiment's support. -/
noncomputable def measurablePolicy (φ : ℝ → Bool) :
    {φ : ℝ → Bool // φ ∈ binaryPolicyClass} := by
  classical
  exact if h : φ ∈ binaryPolicyClass then ⟨φ, h⟩ else
    ⟨fun _ => false, by simp [binaryPolicyClass]⟩

-- @env: S4
variable (α γ θ : ℝ)

/-- Public margin constant. -/
def Cm : ℝ := 2 -- @realizes Cm(C_m=2)
/-- Public overlap window scale. -/
def co : ℝ := 1 -- @realizes co(c_o=1)
/-- Public margin window endpoint. -/
noncomputable def u0 : ℝ := 1/2 -- @realizes u0(u_0=1/2)
/-- Public joint-envelope constant. -/
noncomputable def Co (θ : ℝ) : ℝ := (2:ℝ) ^ (θ+2) -- @realizes Co(C_o=2^(theta+2))

/-- Joint balance exponent. -/
noncomputable def betaExp (α γ θ : ℝ) : ℝ := α*γ/(α+θ*γ) -- @realizes beta(alpha gamma/(alpha+theta gamma))
/-- Small-effect bias exponent. -/
noncomputable def sLoc (α γ θ : ℝ) : ℝ := (α+1)/(1+betaExp α γ θ) -- @realizes sloc((alpha+1)/(1+beta))
/-- Local information exponent. -/
noncomputable def DExp (α γ θ : ℝ) : ℝ := α+2+betaExp α γ θ -- @realizes Dexp(alpha+2+beta)
/-- High-effect bias exponent. -/
def sHi (θ : ℝ) : ℝ := θ -- @realizes shi(s_hi=theta)
/-- Dominant bias exponent. -/
noncomputable def sExp (α γ θ : ℝ) : ℝ := min (sLoc α γ θ) (sHi θ) -- @realizes s(min(sloc,shi))
/-- Minimax exponent. -/
noncomputable def rExp (α γ θ : ℝ) : ℝ := sExp α γ θ/(sExp α γ θ+1) -- @realizes r(s/(s+1))
/-- Finite positive phase-boundary value. -/
noncomputable def gammaC (α θ : ℝ) : ℝ := α*(α+1-θ)/(θ*(θ-1)) -- @realizes gammac(alpha(alpha+1-theta)/(theta(theta-1)))

/-- Accepted-bank exponent algebra, locally defined. -/
noncomputable def bankBeta (α γ : ℝ) : ℝ := if γ = 0 then 0 else α*γ/(α+1)
noncomputable def bankD (α γ : ℝ) : ℝ := 2+α+bankBeta α γ
noncomputable def rBank (α γ : ℝ) : ℝ := (1+α)/bankD α γ
lemma rBank_of_pos (α γ : ℝ) (hγ : 0 < γ) :
    rBank α γ = (α+1)/(α+2+α*γ/(α+1)) := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  simp only [rBank, bankD, bankBeta, if_neg hγ0]
  ring

-- @node: ass:iid
/-- Row-n observations have the product sample law. -/
def IIDRows (P : RowLaw) (n : ℕ) : Prop :=
  P.samples n = sampleLaw P n -- @realizes data(D_n~P^⊗n)

-- @node: ass:uniform-score
/-- Arbitrary Borel score probability law supported on [0,1], including atoms. -/
def BorelScoreMarginal (P : RowLaw) : Prop :=
  IsProbabilityMeasure P.PX ∧ P.PX (Set.Icc (0:ℝ) 1)ᶜ = 0 -- @realizes PX(Borel probability on Xspace)

-- @node: ass:consistency
/-- Observed outcome equals the assigned potential outcome. -/
def Consistency (P : RowLaw) : Prop :=
  ∀ᵐ o ∂P.full, o.Y = if o.A then o.Y1 else o.Y0 -- @realizes Y(consistency)

-- @node: ass:exchangeability
/-- Tested conditional exchangeability for bounded measurable functions of the potentials. -/
def Exchangeability (P : RowLaw) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → ∀ g : ℝ × ℝ → ℝ, Measurable g →
    (∃ M : ℝ, ∀ y, |g y| ≤ M) → ∀ a : Bool,
    ∫ o in {o | o.X ∈ B ∧ o.A = a}, g (o.Y0,o.Y1) ∂P.full =
      ∫ o in {o | o.X ∈ B},
        (if a then P.logger o.X else 1-P.logger o.X) * g (o.Y0,o.Y1) ∂P.full

-- @node: ass:known-logging
/-- The supplied learner coordinate agrees with the law's true logger on the score domain. -/
def KnownLogging (P : RowLaw) (e : ℝ → ℝ) : Prop :=
  Set.EqOn e P.logger (Set.Icc (0:ℝ) 1) -- @realizes e(supplied logger equals true propensity on Xspace)

-- @node: ass:positivity
/-- Pointwise positivity without a uniform floor. -/
def Positivity (P : RowLaw) (e : ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂P.PX, 0 < e x ∧ e x < 1 -- @realizes e(0<e(X)<1 a.s.); @realizes p(0<p≤1/2 a.s.)

-- @node: ass:margin
/-- Welfare margin condition. -/
def MarginCondition (P : RowLaw) (α : ℝ) : Prop :=
  ∀ u : ℝ, 0 < u → u ≤ u0 →
    P.PX.real {x | 0 < effectMagnitude P x ∧ effectMagnitude P x ≤ u} ≤ Cm*u^α -- @realizes tabs(positive-effect margin tail)

-- @node: ass:global-joint-envelope
/-- Global joint effect-propensity envelope. -/
def GlobalJointEnvelope (P : RowLaw) (α γ θ : ℝ) : Prop :=
  ∀ u v : ℝ, 0 < u → u ≤ 2 → 0 < v → v ≤ co*u^γ →
    P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧ effectMagnitude P x ≤ u}
      ≤ Co θ*u^α*v^θ -- @realizes p(joint tail with weak-arm propensity); @realizes tabs(positive-effect range)

-- @node: ass:canonical-threshold
/-- The canonical rule is a threshold policy modulo score-null sets. -/
def CanonicalThreshold (P : RowLaw) : Prop :=
  ∃ π ∈ thresholdClass, π =ᵐ[P.PX] canonicalPolicy P -- @realizes pi(canonical threshold witness); @realizes pistar(threshold realizability)

-- @node: def:law-class
/-- The row-n triangular class, with the ten named assumptions as fields. -/
structure LawClass (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ) : Prop where
  exponents : PublicExponents α γ θ
  sampleSize : 0 < n -- @realizes n(positive sample size)
  wf : WellFormed P
  iid : IIDRows P n
  score : BorelScoreMarginal P
  consistent : Consistency P
  exchangeable : Exchangeability P
  bounded : BoundedPotentials P
  effectBound : ∀ᵐ x ∂P.PX, |P.tau x| ≤ 2 -- @realizes tau(conditional mean of Y1-Y0 in [-2,2])
  known : KnownLogging P e
  loggerSpace : ∀ x ∈ Set.Icc (0:ℝ) 1, e x ∈ Set.Ioo (0:ℝ) 1 -- @realizes e(e:Xspace→(0,1) pointwise)
  positive : Positivity P e
  margin : MarginCondition P α
  envelope : GlobalJointEnvelope P α γ θ
  canonical : CanonicalThreshold P -- @realizes Pclass(all named member assumptions)

-- @node: def:minimax-risk
/-- Expected-regret minimax value over fixed-logger randomized learners. -/
noncomputable def minimaxRegret (α γ θ : ℝ) (n : ℕ) : ℝ :=
  ⨅ Φ : {Φ : Learner n // LearnerClass n Φ},
    ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2},
      ∫ du, regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
        (measurablePolicy (fun x => Φ.1 Pe.1.2 du.1 du.2 x))
        ∂experiment Pe.1.1 n -- @realizes Mn(inf learners sup laws expected regret)

end CausalSmith.Stat.ScorethresholdOverlapRegret
