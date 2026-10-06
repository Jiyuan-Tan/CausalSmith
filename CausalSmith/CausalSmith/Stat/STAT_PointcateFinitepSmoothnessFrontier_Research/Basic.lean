module
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Finite-moment point-CATE frontier: Basic. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Public parameters carry the moment and three smoothness exponents. -/
structure Params where
  p : ℝ -- @realizes p(real moment exponent)
  α : ℝ -- @realizes alpha(real propensity exponent)
  β : ℝ -- @realizes beta(real baseline exponent)
  γ : ℝ -- @realizes gamma(real effect exponent)
/-- Public tuples carry the ordinary product topology. -/
instance : TopologicalSpace Params :=
  TopologicalSpace.induced (fun κ : Params => (κ.p, κ.α, κ.β, κ.γ)) inferInstance
/-- The parameter domain is (1,2] times (0,1] cubed. -/
def Params.Valid (κ : Params) : Prop :=
  (1 < κ.p ∧ κ.p ≤ 2) ∧ -- @realizes p(1<p≤2)
  (0 < κ.α ∧ κ.α ≤ 1) ∧ -- @realizes alpha(0<alpha≤1)
  (0 < κ.β ∧ κ.β ≤ 1) ∧ -- @realizes beta(0<beta≤1)
  (0 < κ.γ ∧ κ.γ ≤ 1) -- @realizes gamma(0<gamma≤1)
/-- Borel records comprise a covariate, binary treatment, and real response. -/
abbrev O := unitInterval × Bool × ℝ -- @realizes Ospace([0,1]×Bool×Real) @realizes O(record carrier)
/-- The original covariate coordinate. -/
def X (o : O) : unitInterval := o.1 -- @realizes X(first coordinate)
/-- The original treatment coordinate. -/
def A (o : O) : Bool := o.2.1 -- @realizes A(second coordinate)
/-- The original outcome coordinate. -/
def Y (o : O) : ℝ := o.2.2 -- @realizes Y(third coordinate)
/-- The known design probability is Lebesgue measure on the unit interval. -/
def design : Measure unitInterval := volume -- @realizes lambda(Lebesgue probability)
/-- One half belongs to the unit interval. -/
-- @node: half_mem
lemma half_mem : (1/2 : ℝ) ∈ Icc 0 1 := by
  constructor <;> norm_num
/-- The point target is evaluated at one half. -/
def xstar : unitInterval := ⟨1/2, half_mem⟩ -- @realizes xstar(1/2)
/-- Conditional observed marks are a Bernoulli-weighted pair of outcome kernels. -/
def recordMeasure (e : unitInterval → ℝ) (Q : Bool → Kernel unitInterval ℝ)
    (x : unitInterval) : Measure (Bool × ℝ) :=
  ENNReal.ofReal (e x) • ((Measure.dirac true).prod (Q true x)) +
  ENNReal.ofReal (1 - e x) • ((Measure.dirac false).prod (Q false x))
/-- The explicit conditional record measure varies measurably with the covariate. -/
-- @node: measurable_recordMeasure
@[fun_prop] lemma measurable_recordMeasure (e : unitInterval → ℝ) (he : Measurable e)
    (Q : Bool → Kernel unitInterval ℝ) : Measurable (recordMeasure e Q) := by
  unfold recordMeasure
  have hprod (a : Bool) (μ : Measure ℝ) :
      (Measure.dirac a).prod μ = μ.map (Prod.mk a) := by
    rw [Measure.prod, Measure.dirac_bind (measurable_of_countable _)]
  simp_rw [hprod]
  have htrue : Measurable (fun x => ((Q true) x).map (Prod.mk true)) := (Measure.measurable_map (Prod.mk true) measurable_prodMk_left).comp
    (Q true).measurable
  have hfalse : Measurable (fun x => ((Q false) x).map (Prod.mk false)) := (Measure.measurable_map (Prod.mk false) measurable_prodMk_left).comp
    (Q false).measurable
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have ht := (Measure.measurable_coe hs).comp htrue
  have hf := (Measure.measurable_coe hs).comp hfalse
  fun_prop
/-- The observed-record kernel uses the explicit Bernoulli weights. -/
def recordKernel (e : unitInterval → ℝ) (he : Measurable e)
    (Q : Bool → Kernel unitInterval ℝ) : Kernel unitInterval (Bool × ℝ) :=
  ⟨recordMeasure e Q, measurable_recordMeasure e he Q⟩
/-- A probability law together with its pinned observational versions; model restrictions
are stated separately in InModel. -/
structure ObservedLaw where
  P : Measure O -- @realizes P(Borel record law)
  probability : IsProbabilityMeasure P -- @realizes P(probability normalization)
  e : unitInterval → ℝ -- @realizes e(propensity carrier)
  e_measurable : Measurable e -- @realizes e(Borel version)
  e_range : ∀ x, 0 ≤ e x ∧ e x ≤ 1 -- @realizes e(probability range)
  Q : Bool → Kernel unitInterval ℝ -- @realizes Q(arm conditional Borel kernels)
  markov : ∀ a, IsMarkovKernel (Q a) -- @realizes Q(arm probability normalization)
  m0 : unitInterval → ℝ -- @realizes m0(control mean carrier)
  tau : unitInterval → ℝ -- @realizes tau(contrast carrier)
  record_version : P = (P.map X) ⊗ₘ recordKernel e e_measurable Q -- @realizes e(conditional treatment probability) @realizes Q(conditional outcome law)
  mean0_version : ∀ᵐ x ∂(P.map X), m0 x = ∫ y, y ∂Q false x -- @realizes m0(kernel mean)
  mean1_version : ∀ᵐ x ∂(P.map X), m0 x + tau x = ∫ y, y ∂Q true x -- @realizes tau(treated mean minus control mean) @realizes m1(treated kernel mean)
/-- A bundled observed law supplies its probability instance. -/
instance (law : ObservedLaw) : IsProbabilityMeasure law.P := law.probability
/-- The original arm kernels supply their Markov instances. -/
instance (law : ObservedLaw) (a : Bool) : IsMarkovKernel (law.Q a) := law.markov a
/-- The treated mean equals baseline plus contrast. -/
def ObservedLaw.m1 (law : ObservedLaw) (x : unitInterval) : ℝ := law.m0 x + law.tau x -- @realizes m1(m0+tau)
/-- The marginal conditional mean is baseline plus propensity times contrast. -/
def ObservedLaw.g (law : ObservedLaw) (x : unitInterval) : ℝ := law.m0 x + law.e x * law.tau x -- @realizes g(m0+e*tau)
/-- The scalar estimand evaluates the continuous contrast version at one half. -/
def ObservedLaw.theta (law : ObservedLaw) : ℝ := law.tau xstar -- @realizes theta(tau(xstar))
/-- Finite original datasets. -/
abbrev Dataset (n : ℕ) := Fin n → O -- @realizes On(original n-record tuple)
/-- Data augmented by an independent unit-interval seed. -/
abbrev Experiment (n : ℕ) := Dataset n × unitInterval -- @realizes U(uniform seed carrier)
/-- The canonical original decision experiment. -/
def jointLaw (n : ℕ) (P : Measure O) : Measure (Experiment n) :=
  (Measure.pi fun _ : Fin n => P).prod design -- @realizes joint(P^n×lambda) @realizes U(independent uniform seed)
/-- Sample-size-indexed seeded experiment laws on a generic measurable record space. -/
abbrev ExperimentFamilyOf (Ω : Type*) [MeasurableSpace Ω] :=
  (n : ℕ) → Measure Ω → Measure ((Fin n → Ω) × unitInterval)
/-- The original-record instance of the generic seeded experiment family. -/
abbrev ExperimentFamily := ExperimentFamilyOf O
-- @env: S1
variable (κ : Params) (n : ℕ) -- @realizes kappa(public tuple) @realizes n(natural sample size; restricted to ≥2 in statements)
-- @node: ass:iid
/-- The experiment-law family is the independent product of the record law and seed law. -/
def IIDSampling {Ω : Type*} [MeasurableSpace Ω] (expLaw : ExperimentFamilyOf Ω) : Prop :=
  ∀ n, 2 ≤ n → ∀ P, IsProbabilityMeasure P → expLaw n P = (Measure.pi (fun _ : Fin n => P)).prod design
-- @node: def:holder
/-- The radius-twenty order-at-most-one Holder ball includes continuity and the sup bound. -/
def holderBall (s : ℝ) (f : unitInterval → ℝ) : Prop :=
  Continuous f ∧ (∀ x, |f x| ≤ 20) ∧
    ∀ x z, |f x - f z| ≤ 20 * |(x : ℝ) - z| ^ s -- @realizes H(continuous radius-20 Holder ball)
-- @node: ass:uniform
/-- The covariate marginal is exactly the known uniform design. -/
def UniformDesign (law : ObservedLaw) : Prop := law.P.map X = design -- @realizes X(uniform original covariate marginal)
-- @node: ass:overlap
/-- The propensity is everywhere between one quarter and three quarters. -/
def Overlap (law : ObservedLaw) : Prop := ∀ x, 1/4 ≤ law.e x ∧ law.e x ≤ 3/4 -- @realizes e(everywhere 1/4≤e≤3/4)
-- @node: ass:propensity-holder
/-- The original propensity has its public Holder exponent. -/
def PropensityHolder (law : ObservedLaw) : Prop := holderBall κ.α law.e -- @realizes e(Holder alpha radius 20)
-- @node: ass:baseline-holder
/-- The original control mean has its public Holder exponent. -/
def BaselineHolder (law : ObservedLaw) : Prop := holderBall κ.β law.m0 -- @realizes m0(Holder beta radius 20)
-- @node: ass:effect-holder
/-- The original contrast has its public Holder exponent. -/
def EffectHolder (law : ObservedLaw) : Prop := holderBall κ.γ law.tau -- @realizes tau(Holder gamma radius 20)
-- @node: ass:effect-range
/-- The contrast is everywhere bounded in absolute value by one half. -/
def EffectRange (law : ObservedLaw) : Prop := ∀ x, |law.tau x| ≤ 1/2 -- @realizes tau(effect range)
-- @node: ass:conditional-moment
/-- Each conditional arm law has raw p-moment at most ten almost everywhere. -/
def ConditionalMoment (law : ObservedLaw) : Prop :=
  ∀ᵐ x ∂design, ∀ a : Bool, ∫⁻ y, ENNReal.ofReal (|y| ^ κ.p) ∂law.Q a x ≤ 10 -- @realizes Q(raw conditional p-moment envelope)
-- @node: def:model
/-- The seven primitive modelling atoms define the law class. -/
structure InModel (law : ObservedLaw) : Prop where
  uniform : UniformDesign law
  overlap : Overlap law
  propensityHolder : PropensityHolder κ law
  baselineHolder : BaselineHolder κ law
  effectHolder : EffectHolder κ law
  effectRange : EffectRange law
  conditionalMoment : ConditionalMoment κ law
/-- The complete indexed law class. -/
def modelClass : Set ObservedLaw := {law | InModel κ law} -- @realizes M(seven-atom law class)
/-- Endpoint and inclusion-flag codes with all endpoints in the target range. -/
abbrev Endpoints := {c : ℝ × ℝ × Bool × Bool //
  -1/2 ≤ c.1 ∧ c.1 ≤ c.2.1 ∧ c.2.1 ≤ 1/2} -- @realizes Cinterval(ordered endpoints in target range; inclusion flags)
/-- Empty or connected bounded intervals with the inherited Borel structure. -/
abbrev IntervalCode := Unit ⊕ Endpoints -- @realizes Cinterval(empty or connected interval codes)
/-- The subset represented by an interval code. -/
def IntervalCode.toSet : IntervalCode → Set ℝ
  | .inl _ => ∅
  | .inr c => if c.1.2.2.1 then
      (if c.1.2.2.2 then Icc c.1.1 c.1.2.1 else Ico c.1.1 c.1.2.1)
    else (if c.1.2.2.2 then Ioc c.1.1 c.1.2.1 else Ioo c.1.1 c.1.2.1)
/-- Endpoint difference, or zero for the empty code. -/
def IntervalCode.length : IntervalCode → ℝ
  | .inl _ => 0
  | .inr c => Causalean.Stat.intervalLength c.1.1 c.1.2.1
-- @env: S2
variable (S : Type*) [MeasurableSpace S]
/-- Borel randomized decisions bounded to the target interval, with optional side information. -/
def SideEstimator := {t : Dataset n × unitInterval × S → ℝ //
  Measurable t ∧ ∀ z, t z ∈ Icc (-1/2) (1/2)}
/-- Borel randomized interval decisions. -/
def IntervalProc := {i : Dataset n × unitInterval × S → IntervalCode // Measurable i}
-- @node: def:decisions
/-- Original decisions receive only the dataset and uniform seed; the Unit factor carries no information. -/
def Estimator := SideEstimator n Unit -- @realizes Tset(Borel dataset-and-seed decisions)
/-- Original interval decisions have no law-dependent side information. -/
abbrev OriginalIntervalProc := IntervalProc n Unit -- @realizes Iset(Borel dataset-and-seed interval decisions)
/-- Inserting the unique Unit value identifies the original decision domain measurably. -/
def originalDecisionDomain : (Dataset n × unitInterval × Unit) ≃ᵐ Experiment n where
  toFun z := (z.1, z.2.1)
  invFun z := (z.1, z.2, ())
  left_inv := by intro z; rcases z with ⟨o, u, s⟩; cases s; rfl
  right_inv := by intro z; rfl
  measurable_toFun := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
variable {S}
/-- Absolute error under a law-specific side-information value. -/
def decisionRisk (expLaw : ExperimentFamily) (side : ObservedLaw → S)
    (t : SideEstimator n S) (law : ObservedLaw) : ℝ :=
  ∫ z, |t.1 (z.1, z.2, side law) - law.theta| ∂expLaw n law.P
/-- The probability that the reported interval contains the target. -/
def coverage (expLaw : ExperimentFamily) (side : ObservedLaw → S)
    (i : IntervalProc n S) (law : ObservedLaw) : ℝ :=
  (expLaw n law.P).real {z | law.theta ∈ (i.1 (z.1, z.2, side law)).toSet}
/-- Expected length of a side-information decision. -/
def expectedLength (expLaw : ExperimentFamily) (side : ObservedLaw → S)
    (i : IntervalProc n S) (law : ObservedLaw) : ℝ :=
  ∫ z, (i.1 (z.1, z.2, side law)).length ∂expLaw n law.P
/-- Minimax absolute risk on the entire model. -/
def minimaxRiskWith (expLaw : ExperimentFamily) (side : ObservedLaw → S) : ℝ :=
  ⨅ t : SideEstimator n S, ⨆ law : {law // InModel κ law}, decisionRisk n expLaw side t law.1
/-- Honest minimax length on the entire model. -/
def honestLengthWith (expLaw : ExperimentFamily) (side : ObservedLaw → S) : ℝ :=
  ⨅ i : {i : IntervalProc n S // ∀ law, InModel κ law → 9/10 ≤ coverage n expLaw side i law},
    ⨆ law : {law // InModel κ law}, expectedLength n expLaw side i.1 law.1
-- @node: def:risks
/-- Original-record minimax absolute risk with the independent seed. -/
def minimaxRisk : ℝ := minimaxRiskWith κ n jointLaw (fun _ => ()) -- @realizes R(original minimax risk)
/-- Original-record whole-class honest minimax length. -/
def honestLength : ℝ := honestLengthWith κ n jointLaw (fun _ => ()) -- @realizes L(honest minimax expected length)
/-- Sup-norm Borel space of continuous nuisance functions. -/
abbrev Nuisance := C(unitInterval, ℝ) -- @realizes oracle(continuous-function side-information carrier)
/-- The supplied-function measurable space is its sup-norm Borel space. -/
instance : MeasurableSpace Nuisance := borel Nuisance
/-- The supplied-function measurable structure is exactly Borel. -/
instance : BorelSpace Nuisance := ⟨rfl⟩
/-- A continuous version, with a fixed total extension outside the class. -/
def continuousVersion (f : unitInterval → ℝ) : Nuisance :=
  if h : Continuous f then ⟨f, h⟩ else 0
/-- Revealed propensity. -/
def sideE (law : ObservedLaw) : Nuisance := continuousVersion law.e
/-- Revealed propensity and baseline. -/
def sideEM (law : ObservedLaw) : Nuisance × Nuisance := (sideE law, continuousVersion law.m0)
-- @node: def:oracle
/-- Risk in the revealed-propensity experiment. -/
def oracleRisk : ℝ := minimaxRiskWith κ n jointLaw sideE -- @realizes Roracle(revealed e risk)
/-- Alternative spelling for the revealed-propensity risk. -/
abbrev oracleRiskE := oracleRisk
/-- Risk in the revealed-propensity-and-baseline experiment. -/
def oracleRiskEM : ℝ := minimaxRiskWith κ n jointLaw sideEM -- @realizes Roracle(revealed e,m0 risk)
/-- Honest length in the revealed-propensity experiment. -/
def oracleLengthE : ℝ := honestLengthWith κ n jointLaw sideE -- @realizes Loracle(revealed e length)
/-- Honest length in the revealed-propensity-and-baseline experiment. -/
def oracleLengthEM : ℝ := honestLengthWith κ n jointLaw sideEM -- @realizes Loracle(revealed e,m0 length)
/-- The revealed-propensity score uses the original outcome. -/
def scoreZ (e : unitInterval → ℝ) (o : O) : ℝ :=
  if A o then Y o / e (X o) else -Y o / (1 - e (X o)) -- @realizes Zoracle(AY/e−(1−A)Y/(1−e))
-- @env: S3
variable (κ : Params)
/-- Finite-moment precision exponent. -/
def qExp : ℝ := (κ.p - 1) / κ.p -- @realizes q((p−1)/p)
/-- Sum of nuisance regularities. -/
def sumReg : ℝ := κ.α + κ.β -- @realizes S(alpha+beta)
/-- Revealed-nuisance precision exponent. -/
def rOracle : ℝ := κ.γ * qExp κ / (κ.γ + qExp κ) -- @realizes rO(gamma*q/(gamma+q))
/-- Confounding-interaction precision exponent. -/
def rInter : ℝ := 2 * sumReg κ / (1 + sumReg κ / κ.γ + 2 * κ.α + κ.β / qExp κ) -- @realizes rI(2S/(1+S/gamma+2alpha+beta/q))
/-- The common pure-power benchmark. -/
def rate (n : ℕ) : ℝ := max ((n : ℝ) ^ (-rOracle κ)) ((n : ℝ) ^ (-rInter κ)) -- @realizes rhoH(maximum power benchmark) @realizes rhoR(risk rate) @realizes rhoL(length rate)
/-- Oracle-survival boundary expression. -/
def boundary : ℝ := sumReg κ / κ.γ + (2 * κ.α + κ.p * κ.β) / (κ.p - 1)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
