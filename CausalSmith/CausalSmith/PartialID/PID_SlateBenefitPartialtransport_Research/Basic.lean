import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Capacities
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Core.Variable
import Causalean.Stat.Sample
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Slate-benefit potential-outcome setup

The five-node potential-outcome subsystem, its causal assumptions, and the
pointwise and uniform law classes used throughout the paper.
-/

open MeasureTheory Set
open Causalean PO Causalean.Stat

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

universe uV uVal uOmega uCell

-- @env: S1
variable {𝒳 : Type uCell} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
variable {K : ℕ}

/-- A five-node potential-outcome system for a covariate, binary instrument,
received treatment, selection indicator, and finite ordered outcome. -/
structure POSlateSystem (P : POSystem) (𝒳 : Type*) [MeasurableSpace 𝒳] (K : ℕ) where
  hK : 3 ≤ K -- @realizes K(outcome support has at least three ordered levels)
  xNode : P.V -- @realizes X(system node) @realizes \mathcal X(value carrier)
  zNode : P.V -- @realizes Z(system node)
  dNode : P.V -- @realizes D(system node)
  sNode : P.V -- @realizes S(system node)
  yNode : P.V -- @realizes Y(system node)
  hX : P.X xNode ≃ᵐ 𝒳 -- @realizes X(measurable identification with \mathcal X)
  hZ : P.X zNode ≃ᵐ Bool -- @realizes Z(binary value space)
  hD : P.X dNode ≃ᵐ Bool -- @realizes D(binary value space)
  hS : P.X sNode ≃ᵐ Bool -- @realizes S(binary value space)
  hY : P.X yNode ≃ᵐ Fin K -- @realizes Y(ordered support \mathcal Y) @realizes K(at least three in theorem binders)
  hXZ : xNode ≠ zNode
  hXD : xNode ≠ dNode
  hXS : xNode ≠ sNode
  hXY : xNode ≠ yNode
  hZD : zNode ≠ dNode
  hZS : zNode ≠ sNode
  hZY : zNode ≠ yNode
  hDS : dNode ≠ sNode
  hDY : dNode ≠ yNode
  hSY : sNode ≠ yNode
  [borel : StandardBorelSpace P.Ω] -- @realizes P(standard-Borel latent probability space)

namespace POSlateSystem

variable {P : POSystem} (S : POSlateSystem P 𝒳 K)

/-- The x var is the object specified here for the slate-benefit partial-transport construction. -/
def xVar : POVar P 𝒳 := ⟨S.xNode, S.hX⟩
/-- The z var is the object specified here for the slate-benefit partial-transport construction. -/
def zVar : POVar P Bool := ⟨S.zNode, S.hZ⟩
/-- The d var is the object specified here for the slate-benefit partial-transport construction. -/
def dVar : POVar P Bool := ⟨S.dNode, S.hD⟩
/-- The s var is the object specified here for the slate-benefit partial-transport construction. -/
def sVar : POVar P Bool := ⟨S.sNode, S.hS⟩
/-- The y var is the object specified here for the slate-benefit partial-transport construction. -/
def yVar : POVar P (Fin K) := ⟨S.yNode, S.hY⟩

/-- The factual x is the object specified here for the slate-benefit partial-transport construction. -/
def factualX : P.Ω → 𝒳 := S.xVar.factual
/-- The factual z is the object specified here for the slate-benefit partial-transport construction. -/
def factualZ : P.Ω → Bool := S.zVar.factual
/-- The factual d is the object specified here for the slate-benefit partial-transport construction. -/
def factualD : P.Ω → Bool := S.dVar.factual
/-- The factual s is the object specified here for the slate-benefit partial-transport construction. -/
def factualS : P.Ω → Bool := S.sVar.factual
/-- The factual y is the object specified here for the slate-benefit partial-transport construction. -/
def factualY : P.Ω → Fin K := S.yVar.factual

/-- The dof z is the object specified here for the slate-benefit partial-transport construction. -/
def DofZ (z : Bool) : P.Ω → Bool := S.dVar.cfUnder S.zVar z
/-- The d0 is the object specified here for the slate-benefit partial-transport construction. -/
def D0 : P.Ω → Bool := S.DofZ false -- @realizes D_0(treatment under instrument zero)
/-- The d1 is the object specified here for the slate-benefit partial-transport construction. -/
def D1 : P.Ω → Bool := S.DofZ true -- @realizes D_1(treatment under instrument one)

/-- The sof d is the object specified here for the slate-benefit partial-transport construction. -/
def SofD (d : Bool) : P.Ω → Bool := S.sVar.cfUnder S.dVar d
-- @node: s0
/-- The s0 is the object specified here for the slate-benefit partial-transport construction. -/
def S0 : P.Ω → Bool := S.SofD false -- @realizes S_0(selection under treatment zero)
-- @node: s1
/-- The s1 is the object specified here for the slate-benefit partial-transport construction. -/
def S1 : P.Ω → Bool := S.SofD true -- @realizes S_1(selection under treatment one)

/-- The yof d is the object specified here for the slate-benefit partial-transport construction. -/
def YofD (d : Bool) : P.Ω → Fin K := S.yVar.cfUnder S.dVar d
/-- The y0 is the object specified here for the slate-benefit partial-transport construction. -/
def Y0 : P.Ω → Fin K := S.YofD false -- @realizes Y_0(outcome under treatment zero)
/-- The y1 is the object specified here for the slate-benefit partial-transport construction. -/
def Y1 : P.Ω → Fin K := S.YofD true -- @realizes Y_1(outcome under treatment one)

/-- The x event is the event specified by the stated potential-outcome conditions. -/
def xEvent (x : 𝒳) : Set P.Ω := {ω | S.factualX ω = x}

/-- The complier event is the event specified by the stated potential-outcome conditions. -/
def complierEvent : Set P.Ω :=
  {ω | S.DofZ false ω = false ∧ S.DofZ true ω = true}
  -- @realizes C(event D1 greater than D0)

/-- The p is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def p (x : 𝒳) : ℝ := P.μ.real (S.xEvent x)
  -- @realizes p_x(cell probability)

/-- The propensity is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def propensity (x : 𝒳) : ℝ :=
  conditionalReal P.μ {ω | S.factualZ ω = true} (S.xEvent x)
  -- @realizes \pi(conditional instrument propensity)

/-- The observed datum is the object specified here for the slate-benefit partial-transport construction. -/
def observedDatum (ω : P.Ω) : ObservedDatum 𝒳 K where
  cell := S.factualX ω
  instrument := S.factualZ ω
  treatment := S.factualD ω
  selected := S.factualS ω
  outcome := if S.factualS ω then some (S.factualY ω) else none
  -- @realizes O(observed tuple with missing outcome off selection)

/-- The observed law is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def observedLaw : Measure (ObservedDatum 𝒳 K) :=
  P.μ.map S.observedDatum
  -- @realizes P_{\mathrm{obs}}(pushforward law of observed tuple)

/-- The d under z is the object specified here for the slate-benefit partial-transport construction. -/
def dUnderZ (z : Bool) : RegimedVar P Bool :=
  ⟨S.dVar, Regime.single S.zNode (S.hZ.symm z)⟩

/-- The s under d is the object specified here for the slate-benefit partial-transport construction. -/
def sUnderD (d : Bool) : RegimedVar P Bool :=
  ⟨S.sVar, Regime.single S.dNode (S.hD.symm d)⟩

/-- The y under d is the object specified here for the slate-benefit partial-transport construction. -/
def yUnderD (d : Bool) : RegimedVar P (Fin K) :=
  ⟨S.yVar, Regime.single S.dNode (S.hD.symm d)⟩

/-- The cf bundle is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def cfBundle : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ false) <|
  POCFBundle.cons (S.dUnderZ true) <|
  POCFBundle.cons (S.sUnderD false) <|
  POCFBundle.cons (S.sUnderD true) <|
  POCFBundle.cons (S.yUnderD false) <|
  POCFBundle.cons (S.yUnderD true) <|
  POCFBundle.nil P

end POSlateSystem

-- @node: ass:iv-independence
/-- The iv independence condition is the stated property of the slate-benefit partial-transport model. -/
def IVIndependence {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) : Prop :=
  P.CondIndepCF (RegimedVar.ofFactual S.zVar) S.cfBundle
    (RegimedVar.ofFactual S.xVar) P.μ

-- @node: ass:treatment-consistency
/-- The treatment consistency condition is the stated property of the slate-benefit partial-transport model. -/
def TreatmentConsistency {P : POSystem} (S : POSlateSystem P 𝒳 K) : Prop :=
  ∀ᵐ ω ∂P.μ, S.factualD ω = S.DofZ (S.factualZ ω) ω

-- @node: ass:selection-exclusion-consistency
/-- The selection exclusion condition is the stated property of the slate-benefit partial-transport model. -/
def SelectionExclusion {P : POSystem} (S : POSlateSystem P 𝒳 K) : Prop :=
  ∀ᵐ ω ∂P.μ, S.factualS ω = S.SofD (S.factualD ω) ω

-- @node: ass:outcome-exclusion-consistency
/-- The outcome exclusion condition is the stated property of the slate-benefit partial-transport model. -/
def OutcomeExclusion {P : POSystem} (S : POSlateSystem P 𝒳 K) : Prop :=
  ∀ᵐ ω ∂P.μ, S.factualS ω = true → S.factualY ω = S.YofD (S.factualD ω) ω

-- @node: ass:instrument-overlap
/-- The instrument overlap condition is the stated property of the slate-benefit partial-transport model. -/
def InstrumentOverlap {P : POSystem} (S : POSlateSystem P 𝒳 K) (εZ : ℝ) : Prop :=
  0 < εZ ∧ εZ < (1 : ℝ) / 2 ∧
    ∀ x, 0 < S.p x → εZ ≤ S.propensity x ∧ S.propensity x ≤ 1 - εZ
  -- @realizes \varepsilon_Z(two-sided overlap constant) @realizes \pi(range in overlap interval)

-- @node: ass:no-defiers
/-- The no defiers condition is the stated property of the slate-benefit partial-transport model. -/
def NoDefiers {P : POSystem} (S : POSlateSystem P 𝒳 K) : Prop :=
  ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true

-- @node: ass:weak-selection-monotonicity
/-- The weak selection monotonicity condition is the stated property of the slate-benefit partial-transport model. -/
def WeakSelectionMonotonicity {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (d : 𝒳 → Bool) : Prop :=
  ∀ x, 0 < P.μ (S.complierEvent ∩ S.xEvent x) →
    ∀ᵐ ω ∂(P.μ.restrict (S.complierEvent ∩ S.xEvent x)),
      (d x = true → S.SofD false ω ≤ S.SofD true ω) ∧
      (d x = false → S.SofD true ω ≤ S.SofD false ω)
  -- @realizes d(x)(cellwise direction in the two-point sign space)

-- @node: ass:direction-margin
/-- The direction margin condition is the stated property of the slate-benefit partial-transport model. -/
def DirectionMargin (c : Capacities 𝒳 K) (p : 𝒳 → ℝ) (κσ : ℝ) : Prop :=
  ∀ x, 0 < p x → 0 < c.mass x → κσ ≤ |c.gap x|
  -- @realizes \kappa_{\sigma}(direction-separation margin)

-- @node: ass:positive-aggregate-survivors
/-- The positive aggregate survivors condition is the stated property of the slate-benefit partial-transport model. -/
def PositiveAggregateSurvivors (c : Capacities 𝒳 K) (p : 𝒳 → ℝ) : Prop :=
  0 < c.aggregateMass p

-- @node: ass:uniform-aggregate-survivor-bound
/-- The uniform aggregate survivor bound condition is the stated property of the slate-benefit partial-transport model. -/
def UniformAggregateSurvivorBound (c : Capacities 𝒳 K) (p : 𝒳 → ℝ) (mstar : ℝ) : Prop :=
  0 < mstar ∧ mstar ≤ c.aggregateMass p -- @realizes m_{\star}(positive uniform aggregate lower bound)

-- @env: S3
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The first `n` observations are measurable, mutually independent draws from
the common observed-data law on the sampling probability space. -/
structure FiniteIidSampling (n : ℕ) (μ : Measure Ω)
    (Pobs : Measure (ObservedDatum 𝒳 K))
    (O : ℕ → Ω → ObservedDatum 𝒳 K) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measurable : ∀ i, i < n → Measurable (O i)
  indep : ProbabilityTheory.iIndepFun (fun i : Fin n => O i) μ
  law : ∀ i, i < n → μ.map (O i) = Pobs
  -- @realizes \mathbf O_n(first n observations on their sampling probability space)
  -- @realizes O(measurable mutually independent observation sequence below n)
  -- @realizes P_{\mathrm{obs}}(common pushforward law) @realizes n(sample-size index)

-- @node: ass:iid-sampling
/-- The first `n` observations themselves are measurable, mutually independent,
and have common law `Pobs` on the stated probability space.  No infinite
continuation on the same carrier is part of this assumption. -/
def IidSampling (n : ℕ) (μ : Measure Ω) (Pobs : Measure (ObservedDatum 𝒳 K))
    (O : ℕ → Ω → ObservedDatum 𝒳 K) : Prop :=
  FiniteIidSampling n μ Pobs O

/-- The maintained structural model class on the paper's finite-discrete
covariate domain. -/
-- @node: def:structural-law-class
structure TieSafeSurvivorModel {P : POSystem} [StandardBorelSpace P.Ω]
    [MeasurableSingletonClass 𝒳]
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool) : Prop where
  ivIndependence : IVIndependence S
  treatmentConsistency : TreatmentConsistency S
  selectionExclusion : SelectionExclusion S
  outcomeExclusion : OutcomeExclusion S
  instrumentOverlap : InstrumentOverlap S εZ
  noDefiers : NoDefiers S
  weakSelectionMonotonicity : WeakSelectionMonotonicity S d
  positiveAggregateSurvivors :
    PositiveAggregateSurvivors (observableCapacities S.observedLaw) S.p
  -- @realizes \mathcal M(exact maintained structural law class)

/-- The reusable finite-sample triangular-array law record, with no
direction-margin field. -/
structure UniformInferenceLawClass {P : POSystem} [StandardBorelSpace P.Ω]
    (Sys : POSlateSystem P 𝒳 K) (εZ mstar : ℝ) (d : 𝒳 → Bool) (n : ℕ)
    (O : ℕ → Ω → ObservedDatum 𝒳 K) : Prop where
  ivIndependence : IVIndependence Sys
  treatmentConsistency : TreatmentConsistency Sys
  selectionExclusion : SelectionExclusion Sys
  outcomeExclusion : OutcomeExclusion Sys
  instrumentOverlap : InstrumentOverlap Sys εZ
  noDefiers : NoDefiers Sys
  weakSelectionMonotonicity : WeakSelectionMonotonicity Sys d
  uniformAggregateSurvivorBound :
    UniformAggregateSurvivorBound (observableCapacities Sys.observedLaw) Sys.p mstar
  iidSampling : IidSampling n μ Sys.observedLaw O
  -- @realizes \mathcal P_n(margin-free triangular-array inference class)

/-- The paper-facing triangular-array class is indexed only by positive sample
sizes and uses the frozen finite-discrete covariate domain. -/
-- @node: def:uniform-law-class
def PositiveUniformInferenceLawClass {P : POSystem} [StandardBorelSpace P.Ω]
    [MeasurableSingletonClass 𝒳]
    (Sys : POSlateSystem P 𝒳 K) (εZ mstar : ℝ) (d : 𝒳 → Bool) (n : ℕ)
    (_hn : 1 ≤ n) (O : ℕ → Ω → ObservedDatum 𝒳 K) : Prop :=
  UniformInferenceLawClass (μ := μ) Sys εZ mstar d n O

/-- A genuine full potential-outcome law and its five-node slate subsystem.
The parameter `P₀` fixes universe levels only; `system` ranges over compatible
full laws rather than over records on a preselected law. -/
structure FullLawCandidate (P₀ : POSystem.{uV, uVal, uOmega})
    (𝒳 : Type uCell) [MeasurableSpace 𝒳] (K : ℕ) where
  system : POSystem.{uV, uVal, uOmega}
  slate : POSlateSystem system 𝒳 K

/-- Membership of a full law in the maintained class together with exact
agreement with the supplied observed law. -/
def FullLawFeasible {P : POSystem.{uV, uVal, uOmega}}
    [MeasurableSingletonClass 𝒳]
    (Pobs : Measure (ObservedDatum 𝒳 K))
    (W : FullLawCandidate P 𝒳 K) : Prop :=
  let _ : StandardBorelSpace W.system.Ω := W.slate.borel
  ∃ (εZ : ℝ) (d : 𝒳 → Bool),
    TieSafeSurvivorModel W.slate εZ d ∧ W.slate.observedLaw = Pobs

end CausalSmith.PartialID.SlateBenefitPartialTransport
