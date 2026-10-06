module
public import Causalean.Stat.UStatistic.LocalizedVariance.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Continuous observed laws and honest interval decisions

Concrete binary records, continuous conditional cells, the prescribed native-logit
model, randomized interval procedures, and the expected-length objective.
The Hölder seminorm is extended nonnegative, so a continuous non-Hölder function
has infinite seminorm rather than the junk value of an unbounded real supremum.
-/
@[expose] public section
set_option linter.style.longLine false

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The covariate interval. -/
abbrev Covariate := Set.Icc (0 : ℝ) 1 -- @realizes x(carrier [0,1]) @realizes z(carrier [0,1])
/-- The concrete observed record space. -/
abbrev Record := Covariate × Bool × Bool -- @realizes \Omega([0,1] × binary × binary) @realizes O(record)
/-- First coordinate. -/
def covariate (o : Record) : Covariate := o.1 -- @realizes X(first coordinate)
/-- Binary treatment as a real. -/
def treatment (o : Record) : ℝ := if o.2.1 then 1 else 0 -- @realizes A(binary treatment)
/-- Binary outcome as a real. -/
def outcome (o : Record) : ℝ := if o.2.2 then 1 else 0 -- @realizes Y(binary outcome)
/-- Public uniform design, as Lebesgue measure pulled back to the unit interval. -/
def uniformLaw : Measure Covariate := Measure.comap Subtype.val volume -- @realizes \lambda(uniform [0,1])
/-- Logistic map. -/
def logistic (t : ℝ) : ℝ := Real.sigmoid t -- @realizes \ell(sigmoid) @realizes t(real argument)
/-- Log odds, used only at interior probabilities. -/
def logit (t : ℝ) : ℝ := Real.log (t / (1 - t)) -- @realizes \operatorname{logit}(log odds)
/-- Reconstruct the joint law from its covariate law and conditional cell functions. -/
def jointLaw (Q : Measure Covariate) (p : Bool → Bool → Covariate → ℝ) : Measure Record :=
  ∑ a : Bool, ∑ y : Bool,
    Measure.map (fun x : Covariate => (x, a, y))
      (Q.withDensity (fun x => ENNReal.ofReal (p a y x)))
/-- An ambient probability law includes its unique continuous interior conditional cells. -/
structure ObservedLaw where
  measure : Measure Record -- @realizes P(Borel law on records)
  probability : IsProbabilityMeasure measure -- @realizes P(probability)
  cells : Bool → Bool → Covariate → ℝ -- @realizes p(conditional four-cell carrier) @realizes a(binary index) @realizes y(binary index)
  continuous_cells : ∀ a y, Continuous (cells a y) -- @realizes p(continuous versions)
  interior_cells : ∀ a y x, 0 < cells a y x ∧ cells a y x < 1 -- @realizes p(strictly interior)
  normalized_cells : ∀ x, ∑ a : Bool, ∑ y : Bool, cells a y x = 1 -- @realizes p(conditional probabilities sum to one)
  disintegration : measure = jointLaw (Measure.map covariate measure) cells -- @realizes P(cell disintegration)
  full_support : ∀ G : Set Covariate, IsOpen G → G.Nonempty →
    0 < (Measure.map covariate measure) G -- @realizes P(full-support covariate marginal)
attribute [instance] ObservedLaw.probability

-- @env: S1
variable (P : ObservedLaw) (α β r : ℝ)
/-- Public exponent domain. -/
def ExponentDomain (α β : ℝ) : Prop :=
  0 < β ∧ β < 1 / 4 ∧ β < α ∧ α ≤ 1 -- @realizes \mathcal D(exact public exponent domain) @realizes \alpha(public real exponent) @realizes \beta(public real exponent)
/-- The propensity, pinned to the law. -/
def propensity (P : ObservedLaw) (x : Covariate) : ℝ :=
  P.cells true false x + P.cells true true x -- @realizes e(treatment conditional probability)
/-- Arm risks, pinned to the conditional table. -/
def armRisk (P : ObservedLaw) (a : Bool) (x : Covariate) : ℝ :=
  P.cells a true x / (P.cells a false x + P.cells a true x) -- @realizes \mu(arm conditional risk)
/-- Native propensity logit. -/
def propensityLogit (P : ObservedLaw) (x : Covariate) : ℝ :=
  logit (propensity P x) -- @realizes g(propensity logit)
/-- Native prognosis logit. -/
def prognosisLogit (P : ObservedLaw) (x : Covariate) : ℝ :=
  logit (armRisk P false x) -- @realizes \nu(control risk logit)
/-- Effect is defined literally at covariate zero. -/
def effect (P : ObservedLaw) : ℝ :=
  logit (armRisk P true ⟨0, le_rfl, zero_le_one⟩) -
    prognosisLogit P ⟨0, le_rfl, zero_le_one⟩ -- @realizes \theta(logit mu1(P,0) - nu(P,0))
/-- Conditional cells expressed through propensity and arm risks. -/
def cellProbability (P : ObservedLaw) (a y : Bool) (x : Covariate) : ℝ :=
  (if a then propensity P x else 1 - propensity P x) *
    (if y then armRisk P a x else 1 - armRisk P a x) -- @realizes p(Bernoulli factorization)
/-- Conditional outcome mean. -/
def marginalMean (P : ObservedLaw) (x : Covariate) : ℝ :=
  (1 - propensity P x) * armRisk P false x + propensity P x * armRisk P true x -- @realizes m(marginal outcome mean)
/-- Expected conditional covariance under uniform design. -/
def covarianceCoordinate (P : ObservedLaw) : ℝ :=
  (∫ o, treatment o * outcome o ∂P.measure) -
    ∫ x, propensity P x * marginalMean P x ∂uniformLaw -- @realizes C(observable covariance coordinate)
/-- Integrated off-diagonal product. -/
def denominatorCoordinate (P : ObservedLaw) : ℝ :=
  ∫ x, cellProbability P true false x * cellProbability P false true x ∂uniformLaw -- @realizes S(off-diagonal product integral)
/-- Public denominator floor. -/
def denominatorFloor : ℝ := 1 / 512 -- @realizes s_0(1/512)
/-- The generic Hölder exponent has precisely the paper's domain. -/
def HolderExponentDomain (γ : ℝ) : Prop := -- @realizes \gamma(0 < gamma and gamma <= 1)
  0 < γ ∧ γ ≤ 1
/-- The generic real function on the covariate interval is continuous. -/
def ContinuousFunctionDomain (f : Covariate → ℝ) : Prop := -- @realizes f(continuous real function on [0,1])
  Continuous f
/-- Extended Hölder seminorm, including infinite values. Its paper domain is
`HolderExponentDomain γ` together with `ContinuousFunctionDomain f`. -/
def holderSeminorm (γ : ℝ) (f : Covariate → ℝ) : ℝ≥0∞ := -- @realizes \gamma(real carrier; range via HolderExponentDomain) @realizes f(function carrier; continuity via ContinuousFunctionDomain)
  ⨆ x : Covariate, ⨆ z : Covariate, ⨆ (_ : x ≠ z),
    ENNReal.ofReal (|f x - f z| / |(x : ℝ) - (z : ℝ)| ^ γ) -- @realizes [\cdot]_\gamma(exact extended supremum)

-- @node: ass:uniform-design
/-- Known uniform covariate design. -/
def UniformDesign (P : ObservedLaw) : Prop := Measure.map covariate P.measure = uniformLaw
-- @node: ass:homogeneous-logit
/-- A single homogeneous conditional log-odds coefficient. -/
def HomogeneousLogit (P : ObservedLaw) : Prop :=
  ∀ x, armRisk P true x = logistic (prognosisLogit P x + effect P)
-- @node: ass:effect-envelope
/-- Compact scalar effect envelope. -/
def EffectEnvelope (P : ObservedLaw) : Prop := |effect P| ≤ 1 / 2
-- @node: ass:propensity-envelope
/-- Propensity native-logit envelope. -/
def PropensityEnvelope (P : ObservedLaw) : Prop := ∀ x, |propensityLogit P x| ≤ 1
-- @node: ass:prognosis-envelope
/-- Prognosis native-logit envelope. -/
def PrognosisEnvelope (P : ObservedLaw) : Prop := ∀ x, |prognosisLogit P x| ≤ 1
-- @node: ass:propensity-holder
/-- Propensity native-logit Hölder radius. -/
def PropensityHolder (α : ℝ) (P : ObservedLaw) : Prop := holderSeminorm α (propensityLogit P) ≤ 2
-- @node: ass:prognosis-holder
/-- Prognosis native-logit Hölder radius. -/
def PrognosisHolder (β : ℝ) (P : ObservedLaw) : Prop := holderSeminorm β (prognosisLogit P) ≤ 2
/-- The public evaluation-radius parameter has exactly the frozen range. -/
-- keep: canonical symbol realization used by every delivered radius-domain premise
def RadiusDomain (r : ℝ) : Prop := r ∈ Set.Icc (0 : ℝ) (1/2) -- @realizes r(public evaluation radius)
-- @node: ass:evaluation-radius
/-- Radius restriction used only for length evaluation. -/
def EvaluationRadius (r : ℝ) (P : ObservedLaw) : Prop := |effect P| ≤ r
-- @node: def:logistic-class
/-- The unrestricted homogeneous logistic class. -/
structure LogisticClass (P : ObservedLaw) : Prop where -- @realizes \mathcal L(logistic class)
  homogeneous : HomogeneousLogit P
-- @node: def:model
/-- Exactly the seven prescribed law properties. -/
structure Model (α β : ℝ) (P : ObservedLaw) : Prop where -- @realizes \mathcal M(model class)
  uniform : UniformDesign P
  homogeneous : HomogeneousLogit P
  effect_envelope : EffectEnvelope P
  propensity_envelope : PropensityEnvelope P
  prognosis_envelope : PrognosisEnvelope P
  propensity_holder : PropensityHolder α P
  prognosis_holder : PrognosisHolder β P
-- @node: def:radius-model
/-- The radius slice inherits the whole model and adds only the effect bound. -/
structure RadiusModel (α β r : ℝ) (P : ObservedLaw) : Prop extends Model α β P where -- @realizes \mathcal M_r(radius model)
  radius : EvaluationRadius r P

/-- An interval encoded by endpoints and their inclusion flags. -/
def IntervalDataValid (d : ℝ × ℝ × Bool × Bool) : Prop :=
  -(1 / 2 : ℝ) ≤ d.1 ∧ d.2.1 ≤ 1 / 2 ∧
    (d.1 < d.2.1 ∨ (d.1 = d.2.1 ∧ d.2.2.1 = true ∧ d.2.2.2 = true))
/-- All nonempty connected Borel intervals in the effect region. -/
abbrev EffectInterval := {d : ℝ × ℝ × Bool × Bool // IntervalDataValid d} -- @realizes \mathcal C(endpoints and inclusion flags)
/-- Interval membership, respecting endpoint inclusion. -/
def intervalSet (B : EffectInterval) : Set ℝ :=
  {t | (B.val.1 < t ∨ (B.val.2.2.1 = true ∧ B.val.1 = t)) ∧
       (t < B.val.2.1 ∨ (B.val.2.2.2 = true ∧ t = B.val.2.1))}
/-- Interval length is supremum minus infimum. -/
def intervalLength (B : EffectInterval) : ℝ := B.val.2.1 - B.val.1
/-- Exactly n original observations and an independent uniform seed. -/
abbrev Experiment (n : ℕ) := (Fin n → Record) × Covariate -- @realizes \mathcal O(ordered n-record sample) @realizes i(Fin n index) @realizes U(independent seed)
-- @env: S2
variable (n : ℕ)
/-- Reuse the substrate's finite iid law and tensor the seed. -/
def experimentLaw (P : ObservedLaw) (n : ℕ) : Measure (Experiment n) :=
  (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n).prod uniformLaw
/-- Borel interval procedures, including randomized procedures. -/
structure Procedure (n : ℕ) where
  output : Experiment n → EffectInterval -- @realizes I(data and seed to interval)
  borel : Measurable output
  coverage_measurable : ∀ t : ℝ, MeasurableSet {ω | t ∈ intervalSet (output ω)}
  length_measurable : Measurable (fun ω => intervalLength (output ω))
-- @node: ass:global-coverage
/-- Global finite-sample ninety-percent coverage. -/
def GlobalCoverage (n : ℕ) (α β : ℝ) (I : Procedure n) : Prop :=
  ∀ P, Model α β P → (9 / 10 : ℝ≥0∞) ≤
    experimentLaw P n {ω | effect P ∈ intervalSet (I.output ω)}
-- @node: def:honest-procedures
/-- Honest procedures are bundled through their sole member property. -/
structure HonestProcedure (n : ℕ) (α β : ℝ) (I : Procedure n) : Prop where -- @realizes \mathcal A(globally honest procedures)
  coverage : GlobalCoverage n α β I
/-- Expected length, with the seed included. -/
def expectedLength (P : ObservedLaw) (n : ℕ) (I : Procedure n) : ℝ :=
  ∫ ω, intervalLength (I.output ω) ∂experimentLaw P n
/-- Worst-case expected length on the prescribed radius slice. -/
def worstLength (n : ℕ) (α β r : ℝ) (I : Procedure n) : ℝ :=
  sSup {l | ∃ P, RadiusModel α β r P ∧ l = expectedLength P n I}
-- @node: def:length-objective
/-- Infimum of worst-case length over globally honest procedures. -/
def lengthObjective (n : ℕ) (α β r : ℝ) : ℝ :=
  sInf {l | ∃ I : Procedure n, HonestProcedure n α β I ∧ l = worstLength n α β r I} -- @realizes J(minimax expected length)
/-- Numerator rate exponent. -/
def exponentA (α β : ℝ) : ℝ := min (1 / 2) (2 * (α + β) / (2 * α + 2 * β + 1))
/-- Effect-scaled denominator rate exponent. -/
def exponentB (β : ℝ) : ℝ := 4 * β / (4 * β + 1)
-- @node: def:diagnostic-envelope
/-- Explicit diagnostic profile. -/
def diagnosticEnvelope (n : ℕ) (α β r : ℝ) : ℝ :=
  (n : ℝ) ^ (-exponentA α β) + r * (n : ℝ) ^ (-exponentB β) -- @realizes d_n(explicit power profile) @realizes n(sample size; positivity in statements)

/-- Every encoded interval has nonnegative length. [the stated conclusion](goal) holds. -/
-- @node: intervalLength_nonneg
lemma intervalLength_nonneg (B : EffectInterval) : 0 ≤ intervalLength B := by
  rcases B.property.2.2 with h | ⟨h, _, _⟩
  · exact sub_nonneg.mpr h.le
  · exact sub_nonneg.mpr h.le

/-- Expected interval length is nonnegative under any observed law. [the stated conclusion](goal) holds. -/
-- @node: expectedLength_nonneg
lemma expectedLength_nonneg (P : ObservedLaw) (n : ℕ) (I : Procedure n) :
    0 ≤ expectedLength P n I := by
  exact integral_nonneg (fun ω => intervalLength_nonneg (I.output ω))

/-- The worst-case length is nonnegative, including an empty radius slice. [the stated conclusion](goal) holds. -/
-- @node: worstLength_nonneg
lemma worstLength_nonneg (n : ℕ) (α β r : ℝ) (I : Procedure n) :
    0 ≤ worstLength n α β r I := by
  apply Real.sSup_nonneg
  rintro l ⟨P, _, rfl⟩
  exact expectedLength_nonneg P n I

/-- Any honest procedure upper bounds the minimax objective. Under the stated assumptions. [The stated hypotheses](hyp:hI) hold, and [the stated conclusion follows](goal). -/
-- @node: lengthObjective_le
lemma lengthObjective_le (n : ℕ) (α β r : ℝ) (I : Procedure n)
    (hI : HonestProcedure n α β I) : lengthObjective n α β r ≤ worstLength n α β r I := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro l ⟨J, _, rfl⟩
    exact worstLength_nonneg n α β r J
  · exact ⟨I, hI, rfl⟩
/-- [An all-procedure lower bound transfers to the minimax objective.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: le_lengthObjective
lemma le_lengthObjective (n : ℕ) (α β r b : ℝ)
    (h : ∀ I : Procedure n, HonestProcedure n α β I → b ≤ worstLength n α β r I) :
    b ≤ lengthObjective n α β r := by
  classical
  have : IsProbabilityMeasure uniformLaw := by
    constructor
    rw [uniformLaw, comap_subtype_coe_apply measurableSet_Icc]
    rw [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
    norm_num
  let B : EffectInterval := ⟨(-(1/2 : ℝ), (1/2 : ℝ), true, true), by
    norm_num [IntervalDataValid]⟩
  let I : Procedure n := {
    output := fun _ => B
    borel := by fun_prop
    coverage_measurable := fun t => by
      by_cases ht : t ∈ intervalSet B <;> simp [ht]
    length_measurable := by fun_prop }
  have hI : HonestProcedure n α β I := by
    constructor
    intro P hP
    have : IsProbabilityMeasure (experimentLaw P n) := by
      unfold experimentLaw Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
      infer_instance
    have ht : effect P ∈ intervalSet B := by
      have he := abs_le.mp hP.effect_envelope
      change (-(1/2 : ℝ) < effect P ∨ (true = true ∧ -(1/2 : ℝ) = effect P)) ∧
        (effect P < (1/2 : ℝ) ∨ (true = true ∧ effect P = (1/2 : ℝ)))
      constructor
      · rcases he.1.eq_or_lt with hEq | hLt
        · exact Or.inr ⟨rfl, hEq⟩
        · exact Or.inl hLt
      · rcases he.2.lt_or_eq with hLt | hEq
        · exact Or.inl hLt
        · exact Or.inr ⟨rfl, hEq⟩
    change (9/10 : ℝ≥0∞) ≤ experimentLaw P n {ω : Experiment n | effect P ∈ intervalSet B}
    simp only [ht, Set.ofPred_true, measure_univ]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  apply le_csInf
  · exact ⟨worstLength n α β r I, I, hI, rfl⟩
  · rintro l ⟨J, hJ, rfl⟩
    exact h J hJ
end CausalSmith.Stat.LogoddsLowsmoothFrontier
