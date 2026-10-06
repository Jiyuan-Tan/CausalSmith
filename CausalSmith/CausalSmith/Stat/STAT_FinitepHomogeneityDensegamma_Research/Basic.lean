module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Finite-moment homogeneity testing: Basic. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The moment and independent primitive smoothness tuple. [This is the stated defined object](goal). -/
structure Params where -- @realizes v(public four-exponent tuple)
  p : ℝ -- @realizes p(real carrier)
  α : ℝ -- @realizes alpha(real carrier)
  β : ℝ -- @realizes beta(real carrier)
  γ : ℝ -- @realizes gamma(real carrier)
/-- Product topology on public tuples. [This is the stated defined object](goal). -/
instance : TopologicalSpace Params :=
  TopologicalSpace.induced (fun v : Params => (v.p,v.α,v.β,v.γ)) inferInstance
/-- The public exponent domain. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Params.Valid (v : Params) : Prop := -- @realizes V(public domain)
  (1 < v.p ∧ v.p ≤ 2) ∧ -- @realizes p(1<p≤2)
  (0 < v.α ∧ v.α ≤ 1) ∧ -- @realizes alpha(0<alpha≤1)
  (0 < v.β ∧ v.β ≤ 1) ∧ -- @realizes beta(0<beta≤1)
  (1/4 ≤ v.γ ∧ v.γ ≤ 1) -- @realizes gamma(1/4≤gamma≤1)
/-- Primitive-smoothness tuples for bounded experiments. [This is the stated defined object](goal). -/
structure Smooth3 where -- @realizes w(three public smoothness exponents)
  α : ℝ -- @realizes alpha(bounded-tuple carrier)
  β : ℝ -- @realizes beta(bounded-tuple carrier)
  γ : ℝ -- @realizes gamma(bounded-tuple carrier)
/-- The bundled carrier supplies its declared mathematical structure. [This is the stated defined object](goal). -/
instance : TopologicalSpace Smooth3 :=
  TopologicalSpace.induced (fun w : Smooth3 => (w.α,w.β,w.γ)) inferInstance
/-- The primitive-smoothness domain. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def Smooth3.Valid (w : Smooth3) : Prop := -- @realizes Wdomain(public domain)
  (0 < w.α ∧ w.α ≤ 1) ∧ -- @realizes alpha(bounded-tuple range)
  (0 < w.β ∧ w.β ≤ 1) ∧ -- @realizes beta(bounded-tuple range)
  (1/4 ≤ w.γ ∧ w.γ ≤ 1) -- @realizes gamma(bounded-tuple range)
/-- Insert the second-moment exponent into a primitive-smoothness tuple. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def Params.ofBounded (w : Smooth3) : Params := ⟨2,w.α,w.β,w.γ⟩
/-- Retain the three smoothness exponents of the public tuple. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Params.toSmooth3 (v : Params) : Smooth3 := ⟨v.α,v.β,v.γ⟩
/-- Replace the moment exponent while keeping primitive smoothness fixed. This statement assumes [the v parameter](hyp:v), [the p parameter](hyp:p). [This is the stated defined object](goal). -/
def Params.withP (v : Params) (p : ℝ) : Params := ⟨p,v.α,v.β,v.γ⟩
/-- Covariate, treatment and outcome records. [This is the stated defined object](goal). -/
abbrev Record := unitInterval × Bool × ℝ -- @realizes O(original record)
/-- Extract the original covariate from a record. This statement assumes [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def X (o : Record) : unitInterval := o.1 -- @realizes X(unit-interval coordinate)
/-- Extract the original treatment label from a record. This statement assumes [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def A (o : Record) : Bool := o.2.1 -- @realizes A(binary coordinate)
/-- Extract the original real outcome from a record. This statement assumes [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def Y (o : Record) : ℝ := o.2.2 -- @realizes Y(real coordinate)
/-- Design: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def design : Measure unitInterval := volume -- @realizes lambda(Lebesgue probability)
/-- Continuous covariate functions carry the uniform topology and its Borel structure. [This is the stated defined object](goal). -/
abbrev Nuisance := C(unitInterval,ℝ)
/-- The bundled carrier supplies its declared mathematical structure. [This is the stated defined object](goal). -/
instance : MeasurableSpace Nuisance := borel Nuisance
/-- The bundled carrier supplies its declared mathematical structure. [This is the stated defined object](goal). -/
instance : BorelSpace Nuisance := ⟨rfl⟩
/-- Equivalence classes retain precisely Borel versions equal almost everywhere. This statement assumes [the f parameter](hyp:f). [This is the stated defined object](goal). -/
def eqClass (f : unitInterval → ℝ) : Set (unitInterval → ℝ) :=
  {g | Measurable g ∧ g =ᵐ[design] f} -- @realizes EqClass(Borel a.e. equivalence)
/-- A continuous member of an equivalence class, unique on unit-interval volume. This statement assumes [the E parameter](hyp:E), [the hE parameter](hyp:hE), [the h parameter](hyp:h). [This is the stated defined object](goal). -/
def representative (E : Set (unitInterval → ℝ))
    (hE : ∃ f : unitInterval → ℝ, Measurable f ∧ E = eqClass f)
    (h : ∃ f : Nuisance, (f : unitInterval → ℝ) ∈ E) : Nuisance := Classical.choose h -- @realizes Rep(select continuous member; uniqueness for equivalence classes)
/-- Recordmeasure: the displayed mathematical construction or bound. This statement assumes [the e parameter](hyp:e), [the Q parameter](hyp:Q), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def recordMeasure (e : unitInterval → ℝ) (Q : Bool → Kernel unitInterval ℝ)
    (x : unitInterval) : Measure (Bool × ℝ) :=
  ENNReal.ofReal (e x) • ((Measure.dirac true).prod (Q true x)) +
  ENNReal.ofReal (1-e x) • ((Measure.dirac false).prod (Q false x))
/-- The explicit recordMeasure construction is Borel measurable. This statement assumes [the he condition](hyp:he). [This is the stated conclusion](goal). -/
-- @node: measurable_recordMeasure
@[fun_prop] lemma measurable_recordMeasure (e : unitInterval → ℝ) (he : Measurable e)
    (Q : Bool → Kernel unitInterval ℝ) : Measurable (recordMeasure e Q) := by
  have hprod (a : Bool) (x : unitInterval) :
      (Measure.dirac a).prod (Q a x) = (Q a x).map (Prod.mk a) := by
    rw [Measure.prod, Measure.dirac_bind (measurable_of_countable _)]
  unfold recordMeasure
  simp_rw [hprod]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_prodMk_left hs]
  exact ((ENNReal.measurable_ofReal.comp he).mul
    ((Q true).measurable_coe (measurable_prodMk_left hs))).add
    ((ENNReal.measurable_ofReal.comp (measurable_const.sub he)).mul
      ((Q false).measurable_coe (measurable_prodMk_left hs)))
/-- Recordkernel: the displayed mathematical construction or bound. This statement assumes [the e parameter](hyp:e), [the he parameter](hyp:he), [the Q parameter](hyp:Q). [This is the stated defined object](goal). -/
def recordKernel (e : unitInterval → ℝ) (he : Measurable e)
    (Q : Bool → Kernel unitInterval ℝ) : Kernel unitInterval (Bool × ℝ) :=
  ⟨recordMeasure e Q, measurable_recordMeasure e he Q⟩
/-- Observational versions are pinned to the actual law; model atoms are separate. [This is the stated defined object](goal). -/
structure ObservedLaw where
  P : Measure Record -- @realizes P(Borel record measure)
  probability : IsProbabilityMeasure P -- @realizes P(probability normalization)
  e : Nuisance -- @realizes e(continuous propensity representative) @realizes Rep(continuous carrier)
  e_range : ∀ x, 0 ≤ e x ∧ e x ≤ 1 -- @realizes e(probability range)
  Q : Bool → Kernel unitInterval ℝ -- @realizes Q(Borel arm kernels)
  markov : ∀ a, IsMarkovKernel (Q a) -- @realizes Q(probability normalization)
  m0 : Nuisance -- @realizes mzero(continuous control mean)
  tau : Nuisance -- @realizes tau(continuous contrast)
  record_version : P = (P.map X) ⊗ₘ recordKernel e e.continuous.measurable Q -- @realizes eClass(propensity a.e. version) @realizes Q(conditional arm laws)
  mean0_version : ∀ᵐ x ∂design, m0 x = ∫ y, y ∂Q false x -- @realizes mzeroClass(control mean equivalence class)
  mean1_version : ∀ᵐ x ∂design, m0 x + tau x = ∫ y, y ∂Q true x -- @realizes moneClass(treated mean equivalence class) @realizes tau(treated minus control)
/-- The bundled carrier supplies its declared mathematical structure. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
instance (law : ObservedLaw) : IsProbabilityMeasure law.P := law.probability
/-- The bundled carrier supplies its declared mathematical structure. This statement assumes [the law parameter](hyp:law), [the a parameter](hyp:a). [This is the stated defined object](goal). -/
instance (law : ObservedLaw) (a : Bool) : IsMarkovKernel (law.Q a) := law.markov a
/-- The treated mean is the sum of the original baseline and effect. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def ObservedLaw.m1 (law : ObservedLaw) : Nuisance := law.m0 + law.tau -- @realizes mone(baseline plus contrast)
/-- The covariate marginal is the pushforward of the original law. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def covariateLaw (law : ObservedLaw) : Measure unitInterval := law.P.map X -- @realizes PX(covariate marginal)
/-- The continuous Holder ball has both sup norm and Holder constant at most twenty. This statement assumes [the s parameter](hyp:s), [the f parameter](hyp:f). [This is the stated defined object](goal). -/
def holderBall (s : ℝ) (f : unitInterval → ℝ) : Prop :=
  Continuous f ∧ (∀ x, |f x| ≤ 20) ∧
  ∀ x z, |f x-f z| ≤ 20 * |(x:ℝ)-(z:ℝ)| ^ s -- @realizes Holder(radius-twenty continuous Holder ball)
-- @env: S1
variable (v : Params) (law : ObservedLaw) -- @realizes v(public exponent tuple)
/-- [Uniform](goal). \(P_X=\lambda\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:uniform
def UniformDesign : Prop := covariateLaw law = design -- @realizes PX(uniform marginal) @realizes lambda(known marginal)
/-- [Overlap](goal). \(e_P([0,1])\subseteq[1/4,3/4]\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:overlap
def Overlap : Prop := ∀ x, 1/4 ≤ law.e x ∧ law.e x ≤ 3/4 -- @realizes e(fixed overlap envelope)
/-- [Propensity smoothness](goal). \(\mathcal E_P\in\{[f]_\lambda:f\in\mathcal H^\alpha(20)\}\). This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: ass:propensity-smoothness
def PropensitySmooth : Prop := holderBall v.α law.e -- @realizes e(Holder alpha)
/-- [Baseline smoothness](goal). \(\mathcal G_{0,P}\in\{[g]_\lambda:g\in\mathcal H^\beta(20)\}\). This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: ass:baseline-smoothness
def BaselineSmooth : Prop := holderBall v.β law.m0 -- @realizes mzero(Holder beta)
/-- [Effect smoothness](goal). \(\mathcal G_{1,P}\in\{[m_{0,P}+t]_\lambda:t\in\mathcal H^\gamma(20)\}\). This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: ass:effect-smoothness
def EffectSmooth : Prop := holderBall v.γ law.tau -- @realizes tau(Holder gamma)
/-- [Baseline cap](goal). \(\|m_{0,P}\|_\infty\le1/2\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:baseline-cap
def BaselineCap : Prop := ∀ x, |law.m0 x| ≤ 1/2 -- @realizes mzero(supremum cap)
/-- [Effect cap](goal). \(\|\tau_P\|_\infty\le1/2\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:effect-cap
def EffectCap : Prop := ∀ x, |law.tau x| ≤ 1/2 -- @realizes tau(supremum cap)
/-- [Raw moment](goal). \(\max_{a\in\{0,1\}}\operatorname*{ess\,sup}_{x\sim\lambda}\int |y|^p\,Q_{a,P}(dy\mid x)\le10\). This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: ass:raw-moment
def RawMoment : Prop := ∀ a : Bool, ∀ᵐ x ∂design,
  ∫⁻ y, ENNReal.ofReal (|y| ^ v.p) ∂law.Q a x ≤ 10 -- @realizes Q(conditional moment envelope)
/-- [Null constancy](goal). \(\exists c\in[-1/2,1/2]\ \forall x\in[0,1],\ \tau_P(x)=c\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:null-constancy
def NullConstancy : Prop := ∃ c : ℝ, -1/2 ≤ c ∧ c ≤ 1/2 ∧ ∀ x, law.tau x = c -- @realizes c(candidate constant in [-1/2,1/2])
/-- [Bounded outcome](goal). \(P(|Y|\le1)=1\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:bounded-outcome
def BoundedOutcome : Prop := law.P {o | |Y o| ≤ 1} = 1
/-- [Binary outcome](goal). \(P(Y\in\{-1,1\})=1\) This statement assumes [the law parameter](hyp:law). -/
-- @node: ass:binary-outcome
def SignedBinaryOutcome : Prop := law.P {o | Y o = -1 ∨ Y o = 1} = 1

/-- [Entire stipulated independent-primitive law class](goal). \(\mathcal M_v=\{P:\ P_X=\lambda,\ \max_{a\in\{0,1\}}\operatorname*{ess\,sup}_{x\sim\lambda}\int |y|^pQ_{a,P}(dy\mid x)\le10,\ \exists f\in\mathcal H^\alpha(20),\ g_0\in\mathcal H^\beta(20),\ g_1\in C([0,1]):\ \mathcal E_P=[f]_\lambda,\ \mathcal G_{0,P}=[g_0]_\lambda,\ \mathcal G_{1,P}=[g_1]_\lambda,\ f([0,1])\subseteq[1/4,3/4],\ g_1-g_0\in\mathcal H^\gamma(20),\ \|g_0\|_\infty\le1/2,\ \|g_1-g_0\|_\infty\le1/2\},\quad v=(p,\alpha,\beta,\gamma)\in\mathcal V\). The continuous representatives in this membership predicate are \(e_P,m_{0,P},m_{1,P}\); the effect is their canonical difference \(\tau_P\). This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: def:model
structure InModel : Prop where -- @realizes M(flat model membership bundle)
  uniform : UniformDesign law
  overlap : Overlap law
  propensitySmooth : PropensitySmooth v law
  baselineSmooth : BaselineSmooth v law
  effectSmooth : EffectSmooth v law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment v law
/-- [Entire unknown-constant mean null](goal). \(H_0(v)=\{P\in\mathcal M_v:\ \exists c\in[-1/2,1/2]\ \forall x\in[0,1],\ \tau_P(x)=c\}\). This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: def:null
structure InNull : Prop where -- @realizes Hnull(flat model membership bundle)
  uniform : UniformDesign law
  overlap : Overlap law
  propensitySmooth : PropensitySmooth v law
  baselineSmooth : BaselineSmooth v law
  effectSmooth : EffectSmooth v law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment v law
  nullConstancy : NullConstancy law
/-- [Broader oracle model on the existing continuous-representative carrier](goal). Keep uniform design, overlap, effect Hölder smoothness, both mean caps and the conditional p-moment envelope. The existing continuous representatives and their version identities are retained; only the quantitative propensity and baseline Hölder restrictions are deleted. Membership depends on the public tuple only through p and gamma. This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: def:oracle-broad-model
structure InOracleModel : Prop where -- @realizes MoracleBroad(six retained model atoms on the continuous carrier)
  uniform : UniformDesign law
  overlap : Overlap law
  effectSmooth : EffectSmooth v law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment v law
/-- [Broader oracle composite original-mean null](goal). The broader model with an unknown constant effect in [-1/2,1/2]. This statement assumes [the v parameter](hyp:v), [the law parameter](hyp:law). -/
-- @node: def:oracle-broad-null
structure InOracleNull : Prop where -- @realizes HnulloracleBroad(broader model plus unknown-constant effect)
  uniform : UniformDesign law
  overlap : Overlap law
  effectSmooth : EffectSmooth v law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment v law
  nullConstancy : NullConstancy law
variable (w : Smooth3)
/-- [Bounded benchmark with identical primitive constraints](goal). \(\mathcal M^{\mathrm b}_w=\{P\in\mathcal M_{(2,\alpha,\beta,\gamma)}:P(|Y|\le1)=1\},\quad w=(\alpha,\beta,\gamma)\in\mathcal W\). This statement assumes [the w parameter](hyp:w), [the law parameter](hyp:law). -/
-- @node: def:bounded-model
structure InBoundedModel (w : Smooth3) (law : ObservedLaw) : Prop where -- @realizes Mbound(flat model membership bundle)
  uniform : UniformDesign law
  overlap : Overlap law
  propensitySmooth : PropensitySmooth (Params.ofBounded w) law
  baselineSmooth : BaselineSmooth (Params.ofBounded w) law
  effectSmooth : EffectSmooth (Params.ofBounded w) law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment (Params.ofBounded w) law
  boundedOutcome : BoundedOutcome law
variable (w : Smooth3)
/-- [Signed-binary benchmark with identical primitive constraints](goal). \(\mathcal M^{\mathrm{bin}}_w=\{P\in\mathcal M_{(2,\alpha,\beta,\gamma)}:P(Y\in\{-1,1\})=1\},\quad w=(\alpha,\beta,\gamma)\in\mathcal W\). This statement assumes [the w parameter](hyp:w), [the law parameter](hyp:law). -/
-- @node: def:binary-model
structure InBinaryModel (w : Smooth3) (law : ObservedLaw) : Prop where -- @realizes Mbin(flat model membership bundle)
  uniform : UniformDesign law
  overlap : Overlap law
  propensitySmooth : PropensitySmooth (Params.ofBounded w) law
  baselineSmooth : BaselineSmooth (Params.ofBounded w) law
  effectSmooth : EffectSmooth (Params.ofBounded w) law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment (Params.ofBounded w) law
  signedBinaryOutcome : SignedBinaryOutcome law
variable (w : Smooth3)
/-- [Bounded composite mean-constancy null](goal). \(H_0^{\mathrm b}(w)=\{P\in\mathcal M^{\mathrm b}_w:\exists c\in[-1/2,1/2]\ \forall x\in[0,1],\ \tau_P(x)=c\}\). This statement assumes [the w parameter](hyp:w), [the law parameter](hyp:law). -/
-- @node: def:bounded-null
structure InBoundedNull (w : Smooth3) (law : ObservedLaw) : Prop where -- @realizes Hnullbound(flat model membership bundle)
  uniform : UniformDesign law
  overlap : Overlap law
  propensitySmooth : PropensitySmooth (Params.ofBounded w) law
  baselineSmooth : BaselineSmooth (Params.ofBounded w) law
  effectSmooth : EffectSmooth (Params.ofBounded w) law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment (Params.ofBounded w) law
  boundedOutcome : BoundedOutcome law
  nullConstancy : NullConstancy law
variable (w : Smooth3)
/-- [Signed-binary composite mean-constancy null](goal). \(H_0^{\mathrm{bin}}(w)=\{P\in\mathcal M^{\mathrm{bin}}_w:\exists c\in[-1/2,1/2]\ \forall x\in[0,1],\ \tau_P(x)=c\}\). This statement assumes [the w parameter](hyp:w), [the law parameter](hyp:law). -/
-- @node: def:binary-null
structure InBinaryNull (w : Smooth3) (law : ObservedLaw) : Prop where -- @realizes Hnullbin(flat model membership bundle)
  uniform : UniformDesign law
  overlap : Overlap law
  propensitySmooth : PropensitySmooth (Params.ofBounded w) law
  baselineSmooth : BaselineSmooth (Params.ofBounded w) law
  effectSmooth : EffectSmooth (Params.ofBounded w) law
  baselineCap : BaselineCap law
  effectCap : EffectCap law
  rawMoment : RawMoment (Params.ofBounded w) law
  signedBinaryOutcome : SignedBinaryOutcome law
  nullConstancy : NullConstancy law

/-- The subclass bundle retains every original model atom. [This is the stated conclusion](goal). -/
-- @node: InNull.toInModel
lemma InNull.toInModel {v : Params} {law : ObservedLaw} (h : InNull v law) : InModel v law  := by
  exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
    h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment⟩
/-- Every shared-class model law is legal for the broader supplied-propensity experiment. [This is the stated conclusion](goal). -/
lemma InModel.toInOracleModel {v : Params} {law : ObservedLaw} (h : InModel v law) :
    InOracleModel v law := by
  exact ⟨h.uniform, h.overlap, h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment⟩
/-- Every shared-class null law is legal for the broader supplied-propensity null. [This is the stated conclusion](goal). -/
lemma InNull.toInOracleNull {v : Params} {law : ObservedLaw} (h : InNull v law) :
    InOracleNull v law := by
  exact ⟨h.uniform, h.overlap, h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment,
    h.nullConstancy⟩
/-- The broad supplied-propensity null is contained in its model class. [This is the stated conclusion](goal). -/
lemma InOracleNull.toInOracleModel {v : Params} {law : ObservedLaw} (h : InOracleNull v law) :
    InOracleModel v law := by
  exact ⟨h.uniform, h.overlap, h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment⟩
/-- Shared-class model certificates coerce to broad oracle certificates. [This is the stated defined object](goal). -/
instance {v : Params} {law : ObservedLaw} : Coe (InModel v law) (InOracleModel v law) :=
  ⟨InModel.toInOracleModel⟩
/-- Shared-class null certificates coerce to broad oracle-null certificates. [This is the stated defined object](goal). -/
instance {v : Params} {law : ObservedLaw} : Coe (InNull v law) (InOracleNull v law) :=
  ⟨InNull.toInOracleNull⟩
/-- The subclass bundle retains every original model atom. [This is the stated conclusion](goal). -/
-- @node: InBoundedModel.toInModel
lemma InBoundedModel.toInModel {w : Smooth3} {law : ObservedLaw} (h : InBoundedModel w law) : InModel (Params.ofBounded w) law  := by
  exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
    h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment⟩
/-- The subclass bundle retains every original model atom. [This is the stated conclusion](goal). -/
-- @node: InBinaryModel.toInModel
lemma InBinaryModel.toInModel {w : Smooth3} {law : ObservedLaw} (h : InBinaryModel w law) : InModel (Params.ofBounded w) law  := by
  exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
    h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment⟩
/-- The average contrast integrates the continuous original effect over the known design. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def meanTau (law : ObservedLaw) : ℝ := ∫ x, law.tau x ∂design -- @realizes meanTau(average original contrast)
/-- Heterogeneity is the square root of the integrated squared centered contrast. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def hetDist (law : ObservedLaw) : ℝ := Real.sqrt (∫ x, (law.tau x-meanTau law)^2 ∂design) -- @realizes d(L2 centered contrast)
/-- The model maximum is the supremum of all legal heterogeneity distances. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def maxDist (v : Params) : ℝ := sSup (hetDist '' {law | InModel v law}) -- @realizes D(model supremum)
/-- The maximum heterogeneity distance over the broader supplied-propensity model. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def maxDistOracle (v : Params) : ℝ := sSup (hetDist '' {law | InOracleModel v law}) -- @realizes DoracleBroad(supremum over the broader model)
/-- The bounded model maximum is the supremum of its legal heterogeneity distances. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def maxDistBounded (w : Smooth3) : ℝ := sSup (hetDist '' {law | InBoundedModel w law}) -- @realizes Dbound(bounded supremum)
/-- The binary model maximum is the supremum of its legal heterogeneity distances. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def maxDistBinary (w : Smooth3) : ℝ := sSup (hetDist '' {law | InBinaryModel w law}) -- @realizes Dbin(binary supremum)
/-- The explicit separated witness has distance one divided by eight times the square root of two. [This is the stated defined object](goal). -/
def d0 : ℝ := 1/(8*Real.sqrt 2) -- @realizes dzero(nonempty witness distance)
/-- A dataset retains every original record, indexed by the sample size. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
abbrev Dataset (n : ℕ) := Fin n → Record -- @realizes Data(all original records)
/-- The experiment augments all original records with the public uniform seed. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
abbrev Experiment (n : ℕ) := Dataset n × unitInterval -- @realizes U(public seed carrier)
/-- [Given original iid sampling experiment](goal). For the original-record experiment, define \(\mathsf S_{n,P}=P^{\otimes n}\otimes\lambda\) on \( ([0,1]\times\{0,1\}\times\mathbb R)^n\times[0,1]\). The first coordinate is \(\mathcal D_n\), and the last is \(U\). Its test expectation is exactly the already stipulated \(\mathsf R_n(P,\phi)=\int\phi(\mathcal D_n,u)\,\mathsf S_{n,P}(d\mathcal D_n,du)\). Thus this definition names the given iid experiment and independent public randomization; it changes no member-law predicate. This statement assumes [the n parameter](hyp:n), [the P parameter](hyp:P). -/
-- @node: def:original-record-experiment
def expLaw (n : ℕ) (P : Measure Record) : Measure (Experiment n) :=
  (Measure.pi fun _ : Fin n => P).prod design -- @realizes U(independent uniform randomization)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
