module
public import Causalean.Stat.Nonparametric.Approximation.Holder.Defs
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Inference.AffineInversion
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rough nuisance transported CACE: law and decision class

The law has a full-data population coordinate and an assigned source overlay.
Fixed-size source and target experiments are separate factors. The single-population
IV and infinite-sequence iid abstractions in Causalean have different carriers
(bypass-justified); restricted volume, affine inversion, and Hölder balls are reused.
-/

@[expose] public section
set_option linter.style.longLine false

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @env: S1
variable (n : ℕ)
/-- [The covariate space object](goal) is defined without additional inputs. -/
def covariateSpace : Set ℝ := Icc (0 : ℝ) 1 -- @realizes \mathcal X([0,1])
/-- [The parameter space object](goal) is defined without additional inputs. -/
def parameterSpace : Set ℝ := Icc (-1 : ℝ) 1 -- @realizes \Theta([-1,1])
/-- [The full data object](goal) is defined without additional inputs. -/
abbrev FullData := Bool × ℝ × Bool × Bool × ℝ × ℝ
/-- [The assigned object](goal) is defined without additional inputs. -/
abbrev Assigned := FullData × Bool × Bool × ℝ
/-- [The source obs object](goal) is defined without additional inputs. -/
abbrev SourceObs := ℝ × Bool × Bool × ℝ
/-- [The two sample object](goal) is defined from [the supplied inputs](hyp:nS,nT). -/
abbrev TwoSample (nS nT : ℕ) := (Fin nS → SourceObs) × (Fin nT → ℝ)
/-- [The population object](goal) is defined from [the supplied inputs](hyp:o). -/
def population (o : FullData) : Bool := o.1 -- @realizes S(source=true, target=false)
/-- [The covariate object](goal) is defined from [the supplied inputs](hyp:o). -/
def covariate (o : FullData) : ℝ := o.2.1 -- @realizes X(scalar covariate)
/-- [The receipt0 object](goal) is defined from [the supplied inputs](hyp:o). -/
def receipt0 (o : FullData) : Bool := o.2.2.1 -- @realizes D(z)(z=false)
/-- [The receipt1 object](goal) is defined from [the supplied inputs](hyp:o). -/
def receipt1 (o : FullData) : Bool := o.2.2.2.1 -- @realizes D(z)(z=true)
/-- [The outcome0 object](goal) is defined from [the supplied inputs](hyp:o). -/
def outcome0 (o : FullData) : ℝ := o.2.2.2.2.1 -- @realizes Y(d)(d=false)
/-- [The outcome1 object](goal) is defined from [the supplied inputs](hyp:o). -/
def outcome1 (o : FullData) : ℝ := o.2.2.2.2.2 -- @realizes Y(d)(d=true)
/-- [The bool real object](goal) is defined from [the supplied inputs](hyp:b). -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0
/-- [The potential receipt object](goal) is defined from [the supplied inputs](hyp:o,z). -/
def potentialReceipt (o : FullData) (z : Bool) : Bool :=
  if z then receipt1 o else receipt0 o
/-- [The potential outcome object](goal) is defined from [the supplied inputs](hyp:o,d). -/
def potentialOutcome (o : FullData) (d : Bool) : ℝ :=
  if d then outcome1 o else outcome0 o
/-- [The complier object](goal) is defined from [the supplied inputs](hyp:o). -/
def complier (o : FullData) : ℝ :=
  if receipt1 o && !receipt0 o then 1 else 0 -- @realizes C(1{D(1)>D(0)})
/-- [The observe source object](goal) is defined from [the supplied inputs](hyp:o). -/
def observeSource (o : Assigned) : SourceObs :=
  (covariate o.1, o.2.1, o.2.2.1, o.2.2.2)
  -- @realizes Z(assigned encouragement) @realizes D(observed receipt)
  -- @realizes Y(observed outcome) @realizes O_i^{\mathrm S}(source record)
/-- The transport law is specified by its full-data, assignment, and sampling laws together with its density, propensity, and arm-mean functions. -/

structure TransportLaw where
  fullLaw : Measure FullData -- @realizes P_n^F(full-data probability law)
  assignedLaw : Measure Assigned
  sampleLaw : ∀ nS nT, Measure (TwoSample nS nT) -- @realizes P(two-sample law)
  fS : ℝ → ℝ -- @realizes f_{\mathrm S}(density carrier)
  fT : ℝ → ℝ -- @realizes f_{\mathrm T}(density carrier)
  e : ℝ → ℝ -- @realizes e(propensity carrier)
  m : Bool → Bool → ℝ → ℝ -- @realizes m_{Az}(arm means: A=true means Y)
  assignmentPotentialOutcome : Bool → FullData → ℝ
/-- [The population law object](goal) is defined from [the supplied inputs](hyp:P,s). -/

noncomputable def populationLaw (P : TransportLaw) (s : Bool) : Measure FullData :=
  ProbabilityTheory.cond P.fullLaw {o | population o = s}
/-- [The source obs law object](goal) is defined from [the supplied inputs](hyp:P). -/
noncomputable def sourceObsLaw (P : TransportLaw) : Measure SourceObs :=
  P.assignedLaw.map observeSource -- @realizes P_{\mathrm S}(observed source law)
/-- [The source xlaw object](goal) is defined from [the supplied inputs](hyp:P). -/
noncomputable def sourceXLaw (P : TransportLaw) : Measure ℝ :=
  (sourceObsLaw P).map Prod.fst
/-- [The target xlaw object](goal) is defined from [the supplied inputs](hyp:P). -/
noncomputable def targetXLaw (P : TransportLaw) : Measure ℝ :=
  (populationLaw P false).map covariate -- @realizes P_{\mathrm T}(target covariate law)
/-- [The data law object](goal) is defined from [the supplied inputs](hyp:P,nS,nT). -/
noncomputable def dataLaw (P : TransportLaw) (nS nT : ℕ) :
    Measure (TwoSample nS nT) := P.sampleLaw nS nT
  -- @realizes \mathcal S_n(source sample) @realizes \mathcal T_n(target sample)
  -- @realizes X_j^{\mathrm T}(target record)
/-- [The arm value object](goal) is defined from [the supplied inputs](hyp:A,o). -/

def armValue (A : Bool) (o : SourceObs) : ℝ :=
  if A then o.2.2.2 else boolReal o.2.2.1
/-- [The assignment mass object](goal) is defined from [the supplied inputs](hyp:P,z,x). -/
def assignmentMass (P : TransportLaw) (z : Bool) (x : ℝ) : ℝ :=
  if z then P.e x else 1 - P.e x
/-- [The arm contrast object](goal) is defined from [the supplied inputs](hyp:P,A,x). -/

noncomputable def armContrast (P : TransportLaw) (A : Bool) (x : ℝ) : ℝ :=
  P.m A true x - P.m A false x -- @realizes \Delta_A(m_A1-m_A0)
/-- [The transported form object](goal) is defined from [the supplied inputs](hyp:P,A). -/
noncomputable def transportedForm (P : TransportLaw) (A : Bool) : ℝ :=
  ∫ x in covariateSpace, P.fT x * armContrast P A x -- @realizes T_A(generic transported reduced form for Y and D)
/-- [The first stage object](goal) is defined from [the supplied inputs](hyp:P). -/
noncomputable def firstStage (P : TransportLaw) : ℝ :=
  transportedForm P false -- @realizes \mu(T_D)
/-- [The target complier share object](goal) is defined from [the supplied inputs](hyp:P). -/
noncomputable def targetComplierShare (P : TransportLaw) : ℝ :=
  (populationLaw P false {o | complier o = 1}).toReal
/-- [The target cace object](goal) is defined from [the supplied inputs](hyp:P). -/
noncomputable def targetCACE (P : TransportLaw) : ℝ :=
  (∫ o, (outcome1 o - outcome0 o) * complier o ∂populationLaw P false) /
    targetComplierShare P -- @realizes \theta(target complier average effect)

-- @env: S2
variable (α c_f C_f L a : ℝ)
/-- [The holder exponent object](goal) is defined without additional inputs. -/
noncomputable def holderExponent : ℝ := 1 / 8 -- @realizes \beta(1/8)
/-- [The threshold object](goal) is defined without additional inputs. -/
def threshold : ℕ := 256 -- @realizes n_0(256)
/-- [The holder on object](goal) is defined from [the supplied inputs](hyp:f,L). -/
def HolderOn (f : ℝ → ℝ) (L : ℝ) : Prop :=
  1 < L ∧ -- @realizes L(radius greater than one)
  Causalean.Stat.Nonparametric.HolderBallStd
    (fun x : Fin 1 → ℝ => f (x 0)) holderExponent L
    {x | x 0 ∈ covariateSpace}
  -- @realizes \mathcal H^{\beta}([0,1],L)(Hölder ball)
  -- @realizes L(Hölder radius)
/-- [The measurable on covariate object](goal) is defined from [the supplied inputs](hyp:f). -/

def MeasurableOnCovariate (f : ℝ → ℝ) : Prop :=
  Measurable (Set.indicator covariateSpace f)

-- @node: ass:source-iid
/-- [The source iid object](goal) is defined from [the supplied inputs](hyp:P,nS,nT). -/
def SourceIid (P : TransportLaw) (nS nT : ℕ) : Prop :=
  (dataLaw P nS nT).map Prod.fst = Measure.pi (fun _ : Fin nS => sourceObsLaw P)

-- @node: ass:target-iid
/-- [The target iid object](goal) is defined from [the supplied inputs](hyp:P,nS,nT). -/
def TargetIid (P : TransportLaw) (nS nT : ℕ) : Prop :=
  (dataLaw P nS nT).map Prod.snd = Measure.pi (fun _ : Fin nT => targetXLaw P)

-- @node: ass:sample-independence
/-- [The sample independence object](goal) is defined from [the supplied inputs](hyp:P,nS,nT). -/
def SampleIndependence (P : TransportLaw) (nS nT : ℕ) : Prop :=
  dataLaw P nS nT =
    ((dataLaw P nS nT).map Prod.fst).prod ((dataLaw P nS nT).map Prod.snd)

-- @node: ass:source-density-bounds
/-- [The source density bounds object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,P). -/
def SourceDensityBounds (c_f C_f : ℝ) (P : TransportLaw) : Prop :=
  (0 < c_f ∧ c_f < 1) ∧ -- @realizes c_f(domain (0,1))
  1 < C_f ∧ -- @realizes C_f(domain (1,infinity))
  IsProbabilityMeasure P.fullLaw ∧ -- @realizes P_n^F(probability law)
  (∀ᵐ o ∂P.fullLaw,
    covariate o ∈ covariateSpace ∧ -- @realizes X([0,1] full-data support)
    outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1) ∧
    -- @realizes Y(d)(both potential outcomes in [0,1])
  sourceXLaw P =
    (volume.restrict covariateSpace).withDensity (fun x => ENNReal.ofReal (P.fS x)) ∧
    -- @realizes f_{\mathrm S}(Lebesgue density identity)
  ∀ x ∈ covariateSpace, c_f ≤ P.fS x ∧ P.fS x ≤ C_f
    -- @realizes c_f(lower density envelope) @realizes C_f(upper density envelope)
    -- @realizes f_{\mathrm S}(density identity and envelope)

-- @node: ass:target-density-bounds
/-- [The target density bounds object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,P). -/
def TargetDensityBounds (c_f C_f : ℝ) (P : TransportLaw) : Prop :=
  targetXLaw P =
    (volume.restrict covariateSpace).withDensity (fun x => ENNReal.ofReal (P.fT x)) ∧
    -- @realizes f_{\mathrm T}(Lebesgue density identity)
  (∀ x ∈ covariateSpace, c_f ≤ P.fT x ∧ P.fT x ≤ C_f) ∧ -- @realizes f_{\mathrm T}(density envelope)
  0 < c_f -- @realizes f_{\mathrm T}(strictly positive lower envelope) @realizes c_f(positive density bound)

-- @node: ass:source-density-holder
/-- [The source density holder object](goal) is defined from [the supplied inputs](hyp:L,P). -/
def SourceDensityHolder (L : ℝ) (P : TransportLaw) : Prop :=
  HolderOn P.fS L -- @realizes f_{\mathrm S}(Hölder radius L)

-- @node: ass:target-density-holder
/-- [The target density holder object](goal) is defined from [the supplied inputs](hyp:L,P). -/
def TargetDensityHolder (L : ℝ) (P : TransportLaw) : Prop :=
  HolderOn P.fT L -- @realizes f_{\mathrm T}(Hölder radius L)

-- @node: ass:propensity-overlap
/-- [The propensity overlap object](goal) is defined from [the supplied inputs](hyp:P). -/
def PropensityOverlap (P : TransportLaw) : Prop :=
  ∀ x ∈ covariateSpace, (1 / 4 : ℝ) ≤ P.e x ∧ P.e x ≤ 3 / 4
    -- @realizes e([1/4,3/4])

-- @node: ass:propensity-holder
/-- [The propensity holder object](goal) is defined from [the supplied inputs](hyp:L,P). -/
def PropensityHolder (L : ℝ) (P : TransportLaw) : Prop :=
  HolderOn P.e L -- @realizes e(Hölder radius L)

-- @node: ass:arm-means-holder
/-- [The arm means holder object](goal) is defined from [the supplied inputs](hyp:L,P). -/
def ArmMeansHolder (L : ℝ) (P : TransportLaw) : Prop :=
  (∀ A z, HolderOn (P.m A z) L) ∧
  (∀ A z, MeasurableSet (covariateSpace) ∧
    Measurable (Set.indicator covariateSpace (P.m A z)) ∧
    ∀ x ∈ covariateSpace, P.m A z x ∈ Icc (0 : ℝ) 1) ∧ -- @realizes m_{Az}(both arm means in [0,1]) @realizes \Delta_A(arm range constraints) @realizes T_A(bounded contrasts) @realizes \mu(receipt-arm range constraints)
  (∀ A z (B : Set ℝ), MeasurableSet B → B ⊆ covariateSpace →
    ∫ o in {o | o.1 ∈ B ∧ o.2.1 = z}, armValue A o ∂sourceObsLaw P =
      ∫ x in B, P.fS x * assignmentMass P z x * P.m A z x)
      -- @realizes m_{Az}(conditional arm mean version)

-- @node: ass:receipt-consistency
/-- [The receipt consistency object](goal) is defined from [the supplied inputs](hyp:P). -/
def ReceiptConsistency (P : TransportLaw) : Prop :=
  ∀ᵐ o ∂P.assignedLaw, o.2.2.1 = potentialReceipt o.1 o.2.1
    -- @realizes D(D(Z) in source)

-- @node: ass:outcome-consistency
/-- [The outcome consistency object](goal) is defined from [the supplied inputs](hyp:P). -/
def OutcomeConsistency (P : TransportLaw) : Prop :=
  (∀ᵐ o ∂P.assignedLaw, o.2.2.2 = potentialOutcome o.1 o.2.2.1) ∧
  (∀ᵐ o ∂P.assignedLaw, o.2.2.2 ∈ Icc (0 : ℝ) 1)
    -- @realizes Y(Y(D) in source and observed range [0,1])

-- @node: ass:instrument-randomization
/-- [The instrument randomization object](goal) is defined from [the supplied inputs](hyp:P). -/
def InstrumentRandomization (P : TransportLaw) : Prop :=
  IsProbabilityMeasure P.assignedLaw ∧
  MeasurableOnCovariate P.e ∧
  (P.assignedLaw.map (fun o => o.1)) = populationLaw P true ∧
  ∀ (B : Set FullData), MeasurableSet B → ∀ z : Bool,
    (P.assignedLaw {o | o.1 ∈ B ∧ o.2.1 = z}).toReal =
      ∫ o in B, assignmentMass P z (covariate o) ∂populationLaw P true
      -- @realizes Z(conditional independent assignment)

-- @node: ass:exclusion
/-- [The exclusion object](goal) is defined from [the supplied inputs](hyp:P). -/
def Exclusion (P : TransportLaw) : Prop :=
  ∀ z : Bool, P.assignmentPotentialOutcome z =ᵐ[P.fullLaw]
    fun o => potentialOutcome o (potentialReceipt o z)
      -- @realizes Y(d)(Y(D(z)) exclusion)

-- @node: ass:monotonicity
/-- [The monotonicity object](goal) is defined from [the supplied inputs](hyp:P). -/
def Monotonicity (P : TransportLaw) : Prop :=
  ∀ᵐ o ∂P.fullLaw, boolReal (receipt0 o) ≤ boolReal (receipt1 o)
    -- @realizes D(z)(no defiers)
/-- [The conditional mean object](goal) is defined from [the supplied inputs](hyp:P,s,f,q). -/

def ConditionalMean (P : TransportLaw) (s : Bool)
    (f : FullData → ℝ) (q : ℝ → ℝ) : Prop :=
  Measurable q ∧ ∀ (B : Set ℝ), MeasurableSet B →
    ∫ o in {o | covariate o ∈ B}, f o ∂populationLaw P s =
      ∫ x in B, q x ∂(populationLaw P s).map covariate

-- @node: ass:transport-complier-outcome
/-- [The transport complier outcome object](goal) is defined from [the supplied inputs](hyp:P). -/
def TransportComplierOutcome (P : TransportLaw) : Prop :=
  ∃ q : ℝ → ℝ,
    ConditionalMean P false (fun o => (outcome1 o - outcome0 o) * complier o) q ∧
    ConditionalMean P true (fun o => (outcome1 o - outcome0 o) * complier o) q
    -- @realizes C(complier weighted outcome transport)

-- @node: ass:transport-complier-share
/-- [The transport complier share object](goal) is defined from [the supplied inputs](hyp:P). -/
def TransportComplierShare (P : TransportLaw) : Prop :=
  ∃ q : ℝ → ℝ,
    ConditionalMean P false complier q ∧ ConditionalMean P true complier q
    -- @realizes C(complier share transport)

-- @node: ass:positive-strength
/-- [The positive strength object](goal) is defined from [the supplied inputs](hyp:P). -/
def PositiveStrength (P : TransportLaw) : Prop :=
  0 < firstStage P -- @realizes \mu(positive first stage)

-- @node: def:model-class
/-- The model class records that [the supplied constants, law, and sample size](hyp:c_f,C_f,L,P,n) satisfy the statistical assumptions of the transported CACE experiment. -/
structure ModelClass (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) : Prop where
  -- @realizes n(common source-target sample size)
  -- @realizes \mathcal M_n(full model class)
  sourceIid : SourceIid P n n
  targetIid : TargetIid P n n
  independence : SampleIndependence P n n
  sourceBounds : SourceDensityBounds c_f C_f P
  targetBounds : TargetDensityBounds c_f C_f P
  sourceHolder : SourceDensityHolder L P
  targetHolder : TargetDensityHolder L P
  overlap : PropensityOverlap P
  propensityHolder : PropensityHolder L P
  armHolder : ArmMeansHolder L P
  receipt : ReceiptConsistency P
  outcome : OutcomeConsistency P
  randomized : InstrumentRandomization P
  exclusion : Exclusion P
  monotone : Monotonicity P
  outcomeTransport : TransportComplierOutcome P
  shareTransport : TransportComplierShare P
  strength : PositiveStrength P

/-- Bounded arm means imply a contrast in the parameter interval.  Under [the displayed assumptions and inputs](hyp:L,P,hArm,A,x,hx), [the stated conclusion holds](goal). -/
-- @node: armContrast_mem_Icc
lemma armContrast_mem_Icc (L : ℝ) (P : TransportLaw)
    (hArm : ArmMeansHolder L P) (A : Bool) (x : ℝ) (hx : x ∈ covariateSpace) :
    armContrast P A x ∈ Icc (-1 : ℝ) 1 := by -- @realizes \Delta_A(derived range [-1,1]) @realizes T_A(contrast range)
  have h1 := (hArm.2.1 A true).2.2 x hx
  have h0 := (hArm.2.1 A false).2.2 x hx
  change -1 ≤ P.m A true x - P.m A false x ∧
    P.m A true x - P.m A false x ≤ 1
  exact ⟨by simpa using sub_le_sub h1.1 h0.2,
    by simpa using sub_le_sub h1.2 h0.1⟩

/-- The target density is nonnegative on its declared domain.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,P,hT,x,hx), [the stated conclusion holds](goal). -/
-- @node: targetDensity_nonneg_of_bounds
lemma targetDensity_nonneg_of_bounds (c_f C_f : ℝ) (P : TransportLaw)
    (hT : TargetDensityBounds c_f C_f P) (x : ℝ) (hx : x ∈ covariateSpace) :
    0 ≤ P.fT x := by -- @realizes f_{\mathrm T}(derived nonnegative density) @realizes T_A(nonnegative target weight) @realizes \mu(nonnegative target weight)
  exact hT.2.2.le.trans (hT.2.1 x hx).1

/-- The one-dimensional Hölder condition supplies continuity on the covariate interval.  Under [the displayed assumptions and inputs](hyp:f,L,hf), [the stated conclusion holds](goal). -/
-- @node: HolderOn.continuousOn
lemma HolderOn.continuousOn {f : ℝ → ℝ} {L : ℝ} (hf : HolderOn f L) :
    ContinuousOn f covariateSpace := by
  have hc := hf.2.1.continuousOn
  have hdiag : Continuous (fun x : ℝ => fun _ : Fin 1 => x) := by fun_prop
  exact hc.comp (s := covariateSpace) hdiag.continuousOn (fun x hx => hx)

/-- The target probability law normalizes its real density to one.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
-- @node: targetDensity_integral_eq_one
lemma targetDensity_integral_eq_one (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) :
    (∫ x in covariateSpace, P.fT x) = 1 := by -- @realizes f_{\mathrm T}(derived probability normalization) @realizes T_A(normalized target density) @realizes \mu(normalized target density)
  have hf : ContinuousOn P.fT covariateSpace := by
    first | fun_prop | exact hP.targetHolder.continuousOn
  have hd : IntegrableOn P.fT covariateSpace := hf.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict covariateSpace] P.fT := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact targetDensity_nonneg_of_bounds c_f C_f P hP.targetBounds x hx
  have hmass : (∫ x in covariateSpace, P.fT x) =
      (targetXLaw P univ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hn hd.aestronglyMeasurable,
      hP.targetBounds.1, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  have hlow : c_f ≤ ∫ x in covariateSpace, P.fT x := by
    have hconst : IntegrableOn (fun _ : ℝ => c_f) covariateSpace :=
      continuous_const.continuousOn.integrableOn_Icc
    have h := setIntegral_mono_on hconst hd measurableSet_Icc
      (fun x hx => (hP.targetBounds.2.1 x hx).1)
    simpa [covariateSpace, Real.volume_Icc] using h
  have : IsZeroOrProbabilityMeasure (targetXLaw P) := by
    unfold targetXLaw populationLaw
    infer_instance
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := targetXLaw P) with hzero | hone
  · have hz : (∫ x in covariateSpace, P.fT x) = 0 := by
      simpa [hzero] using hmass
    exact False.elim (not_le_of_gt hP.targetBounds.2.2 (hz ▸ hlow))
  · simpa [hone] using hmass

/-- Integrating a bounded arm contrast against the target probability density
preserves its range for either observable.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: transportedForm_mem_Icc
lemma transportedForm_mem_Icc (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    transportedForm P A ∈ Icc (-1 : ℝ) 1 := by -- @realizes T_A(derived generic range [-1,1])
  have hf : ContinuousOn P.fT covariateSpace := by
    first | fun_prop | exact hP.targetHolder.continuousOn
  have hm1 : ContinuousOn (P.m A true) covariateSpace := by
    exact (hP.armHolder.1 A true).continuousOn
  have hm0 : ContinuousOn (P.m A false) covariateSpace := by
    exact (hP.armHolder.1 A false).continuousOn
  have hd := hf.integrableOn_Icc (μ := volume)
  have hi : IntegrableOn (fun x => P.fT x * armContrast P A x) covariateSpace :=
    (hf.mul (hm1.sub hm0)).integrableOn_Icc
  have hnorm := targetDensity_integral_eq_one c_f C_f L P n hP
  change -1 ≤ (∫ x in covariateSpace, P.fT x * armContrast P A x) ∧
    (∫ x in covariateSpace, P.fT x * armContrast P A x) ≤ 1
  constructor
  · have hlow := setIntegral_mono_on hd.neg hi measurableSet_Icc (fun x hx => by
      have hn := targetDensity_nonneg_of_bounds c_f C_f P hP.targetBounds x hx
      have hb := (armContrast_mem_Icc L P hP.armHolder A x hx).1
      simpa using mul_le_mul_of_nonneg_left hb hn)
    change (∫ x in covariateSpace, -P.fT x) ≤
      (∫ x in covariateSpace, P.fT x * armContrast P A x) at hlow
    simpa only [integral_neg, hnorm] using hlow
  · have hupp := setIntegral_mono_on hi hd measurableSet_Icc (fun x hx => by
      have hn := targetDensity_nonneg_of_bounds c_f C_f P hP.targetBounds x hx
      have hb := (armContrast_mem_Icc L P hP.armHolder A x hx).2
      simpa using mul_le_mul_of_nonneg_left hb hn)
    simpa only [hnorm] using hupp

/-- Model membership bounds the positive first stage above by one.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
-- @node: firstStage_le_one_of_model
lemma firstStage_le_one_of_model (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) :
    firstStage P ≤ 1 := by -- @realizes \mu(derived upper bound one)
  exact (transportedForm_mem_Icc c_f C_f L P n hP false).2
/-- [The geometry object](goal) is defined without additional inputs. -/

abbrev Geometry := (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ)
  -- @realizes \mathcal G(supplied density and propensity triple)
/-- [The admissible geometry object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L,G). -/
def AdmissibleGeometry (c_f C_f L : ℝ) (G : Geometry) : Prop :=
  HolderOn G.1 L ∧ HolderOn G.2.1 L ∧ HolderOn G.2.2 L ∧
  (∀ x ∈ covariateSpace,
    c_f ≤ G.1 x ∧ G.1 x ≤ C_f ∧
    c_f ≤ G.2.1 x ∧ G.2.1 x ≤ C_f ∧
    (1 / 4 : ℝ) ≤ G.2.2 x ∧ G.2.2 x ≤ 3 / 4)
  -- @realizes \mathcal G(Hölder geometry with density and propensity envelopes)
-- @env: S5
variable (G : Geometry)

-- @node: def:fixed-geometry-subclass
/-- The fixed-geometry subclass records that [the supplied model and geometry](hyp:c_f,C_f,L,P,n,G) meet the required geometric restrictions. -/
structure FixedGeometrySubclass (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (G : Geometry) : Prop where
  sourceIid : SourceIid P n n
  targetIid : TargetIid P n n
  independence : SampleIndependence P n n
  sourceBounds : SourceDensityBounds c_f C_f P
  targetBounds : TargetDensityBounds c_f C_f P
  sourceHolder : SourceDensityHolder L P
  targetHolder : TargetDensityHolder L P
  overlap : PropensityOverlap P
  propensityHolder : PropensityHolder L P
  armHolder : ArmMeansHolder L P
  receipt : ReceiptConsistency P
  outcome : OutcomeConsistency P
  randomized : InstrumentRandomization P
  exclusion : Exclusion P
  monotone : Monotonicity P
  outcomeTransport : TransportComplierOutcome P
  shareTransport : TransportComplierShare P
  strength : PositiveStrength P
  admissible : AdmissibleGeometry c_f C_f L G
  geometry_eq : ∀ x ∈ covariateSpace,
    P.fS x = G.1 x ∧ P.fT x = G.2.1 x ∧ P.e x = G.2.2 x
  -- @realizes \mathcal M_n^{\mathrm{fix}}(\mathcal G)(fixed geometry subclass)
/-- [The is interval partition object](goal) is defined from [the supplied inputs](hyp:cells). -/

def IsIntervalPartition (cells : Finset (Set ℝ)) : Prop :=
  (∀ cell ∈ cells, OrdConnected cell ∧ cell ⊆ covariateSpace ∧ cell.Nonempty) ∧
  ∀ x ∈ covariateSpace, ∃! cell : Set ℝ, cell ∈ cells ∧ x ∈ cell
/-- [The partition object](goal) is defined without additional inputs. -/

abbrev Partition := {cells : Finset (Set ℝ) // IsIntervalPartition cells}
  -- @realizes \Pi(fixed finite interval partition)

-- @node: def:finite-cell-subclass
/-- The finite-cell subclass records that [the supplied model and partition](hyp:c_f,C_f,L,P,n,partition) meet the finite-cell restrictions. -/
structure FiniteCellSubclass (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (partition : Partition) : Prop where
  sourceIid : SourceIid P n n
  targetIid : TargetIid P n n
  independence : SampleIndependence P n n
  sourceBounds : SourceDensityBounds c_f C_f P
  targetBounds : TargetDensityBounds c_f C_f P
  sourceHolder : SourceDensityHolder L P
  targetHolder : TargetDensityHolder L P
  overlap : PropensityOverlap P
  propensityHolder : PropensityHolder L P
  armHolder : ArmMeansHolder L P
  receipt : ReceiptConsistency P
  outcome : OutcomeConsistency P
  randomized : InstrumentRandomization P
  exclusion : Exclusion P
  monotone : Monotonicity P
  outcomeTransport : TransportComplierOutcome P
  shareTransport : TransportComplierShare P
  strength : PositiveStrength P
  cell_const : ∀ cell ∈ partition.1, ∀ x ∈ cell, ∀ y ∈ cell,
    P.fS x = P.fS y ∧ P.fT x = P.fT y ∧ P.e x = P.e y
    -- @realizes \mathcal M_n^{\mathrm{cell}}(\Pi)(constant geometry per cell)

-- @node: def:marked-density-vector
/-- [The marked density vector object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L,P,n,_hP,x). -/
noncomputable def markedDensityVector (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (_hP : ModelClass c_f C_f L P n) (x : ℝ) : Fin 7 → ℝ :=
  ![P.fT x, P.fS x * (1 - P.e x), P.fS x * P.e x,
    P.fS x * (1 - P.e x) * P.m true false x,
    P.fS x * P.e x * P.m true true x,
    P.fS x * (1 - P.e x) * P.m false false x,
    P.fS x * P.e x * P.m false true x]
  -- @realizes F(seven marked densities) @realizes q_z(assignment densities)
  -- @realizes r_{Az}(nonnegative marked arm density on the model domain)
  -- @realizes \mathcal I(Fin 7 labels)

-- @node: def:smooth-functional
/-- [The phi object](goal) is defined from [the supplied inputs](hyp:A,v). -/
noncomputable def Phi (A : Bool) (v : Fin 7 → ℝ) : ℝ :=
  v 0 * ((v (if A then 4 else 6)) / v 2 -
    (v (if A then 3 else 5)) / v 1)
  -- @realizes \Phi_A(rational transported integrand)
/-- [The known geometry envelope object](goal) is defined from [the supplied inputs](hyp:C_f,c_f). -/

noncomputable def knownGeometryEnvelope (C_f c_f : ℝ) : ℝ :=
  4 * C_f / c_f -- @realizes B_{\mathcal G}(4C_f/c_f)

/-- The [known-geometry expected-length constant](goal), computed from the
[noncoverage level](hyp:α) and the [density envelopes](hyp:C_f,c_f). -/
-- keep: realizes the frozen paper symbol C_fix even though no Lean theorem consumes the value
noncomputable def knownGeometryLengthConstant (α C_f c_f : ℝ) : ℝ :=
  2 + 8 * knownGeometryEnvelope C_f c_f *
    (Real.sqrt (2 * Real.log (4 / α)) + Real.exp (-1 / 2)) -- @realizes C_{\mathrm{fix}}(known-geometry expected-length constant)
/-- [The known geometry radius object](goal) is defined from [the supplied inputs](hyp:α,C_f,c_f,n,_hα,_hC,_hc,_hn). -/

noncomputable def knownGeometryRadius (α C_f c_f : ℝ) (n : ℕ)
    (_hα : 0 < α ∧ α < 1) (_hC : 1 < C_f)
    (_hc : 0 < c_f ∧ c_f < 1) (_hn : 0 < n) : ℝ :=
  knownGeometryEnvelope C_f c_f * Real.sqrt (2 * Real.log (4 / α) / n)
  -- @realizes \rho_n^{\mathcal G}(Hoeffding radius)

-- @node: def:known-geometry-score
/-- [The known geometry score object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L,G,_hG,A,n,_hn). -/
noncomputable def knownGeometryScore (c_f C_f L : ℝ) (G : Geometry)
    (_hG : AdmissibleGeometry c_f C_f L G) (A : Bool) (n : ℕ)
    (_hn : 0 < n) (ω : TwoSample n n) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n,
    G.2.1 (ω.1 i).1 / G.1 (ω.1 i).1 *
      (boolReal (ω.1 i).2.1 * armValue A (ω.1 i) / G.2.2 (ω.1 i).1 -
       (1 - boolReal (ω.1 i).2.1) * armValue A (ω.1 i) /
         (1 - G.2.2 (ω.1 i).1))
  -- @realizes \widetilde T_A^{\mathcal G}(known geometry score)

-- @node: def:known-geometry-interval
/-- [The known geometry interval object](goal) is defined from [the supplied inputs](hyp:G,α,C_f,c_f,L,hG,hα,hC,hc,n,hn). -/
noncomputable def knownGeometryInterval (G : Geometry) (α C_f c_f L : ℝ)
    (hG : AdmissibleGeometry c_f C_f L G)
    (hα : 0 < α ∧ α < 1) (hC : 1 < C_f)
    (hc : 0 < c_f ∧ c_f < 1)
    (n : ℕ) (hn : 0 < n) (ω : TwoSample n n) : Set ℝ :=
  by
    classical
    let A := Causalean.Stat.affineInversionSet parameterSpace
      (knownGeometryScore c_f C_f L G hG true n hn ω)
      (knownGeometryScore c_f C_f L G hG false n hn ω)
      (2 * knownGeometryRadius α C_f c_f n hα hC hc hn)
    exact if A.Nonempty then A else {0}
  -- @realizes \mathcal A_n^{\mathcal G}(affine inversion)
  -- @realizes I_n^{\mathcal G}(nonempty fallback)

-- @env: S4
variable (C : TwoSample n n → Set ℝ)
/-- [The restricted length object](goal) is defined from [the supplied inputs](hyp:C). -/
noncomputable def restrictedLength (C : Set ℝ) : ℝ :=
  Causalean.Stat.restrictedSetVolume parameterSpace C -- @realizes \lambda_{\Theta}(volume of C intersect [-1,1])
/-- Restricted Lebesgue length always lies between zero and two.  Under [the displayed assumptions and inputs](hyp:C), [the stated conclusion holds](goal). -/
-- @node: restrictedLength_mem_Icc
lemma restrictedLength_mem_Icc (C : Set ℝ) :
    restrictedLength C ∈ Icc (0 : ℝ) 2 := by -- @realizes \lambda_{\Theta}(derived length range [0,2])
  change 0 ≤ (volume (C ∩ parameterSpace)).toReal ∧
    (volume (C ∩ parameterSpace)).toReal ≤ 2
  constructor
  · exact ENNReal.toReal_nonneg
  · calc
      (volume (C ∩ parameterSpace)).toReal ≤ (volume parameterSpace).toReal :=
        ENNReal.toReal_mono (by simp [parameterSpace, Real.volume_Icc])
          (measure_mono Set.inter_subset_right)
      _ = 2 := by norm_num [parameterSpace, Real.volume_Icc]
/-- [The expected length object](goal) is defined from [the supplied inputs](hyp:P,nS,nT,C). -/

noncomputable def expectedLength (P : TransportLaw) (nS nT : ℕ)
    (C : TwoSample nS nT → Set ℝ) : ℝ :=
  ∫ ω, restrictedLength (C ω) ∂dataLaw P nS nT

-- @node: def:honest-intervals
/-- [The honest intervals object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,n). -/
def HonestIntervals (α c_f C_f L : ℝ) (n : ℕ) :
    Set (TwoSample n n → Set ℝ) :=
  {C | 0 < α ∧ α < 1 ∧ -- @realizes \alpha(domain (0,1))
    (∀ ω, C ω ⊆ parameterSpace ∧ OrdConnected (C ω)) ∧
    MeasurableSet {p : TwoSample n n × ℝ | p.2 ∈ C p.1} ∧
    ∀ P, ModelClass c_f C_f L P n →
      1 - α ≤ (dataLaw P n n {ω | targetCACE P ∈ C ω}).toReal}
      -- @realizes \alpha(noncoverage level)
  -- @realizes C_n(random connected interval) @realizes \mathfrak H_n(honest class)

-- @node: def:strength-slice
/-- [The strength slice object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L,a,n). -/
def StrengthSlice (c_f C_f L a : ℝ) (n : ℕ) : Set TransportLaw :=
  {P | 0 < a ∧ a ≤ 1 / 4 ∧ ModelClass c_f C_f L P n ∧
    a ≤ firstStage P ∧ firstStage P ≤ 1 / 4}
  -- @realizes a(strength floor in (0,1/4])
  -- @realizes \mathcal M_n(a)(strength restricted class)

-- @node: def:length-frontier
/-- [The length frontier object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,a,n). -/
noncomputable def lengthFrontier (α c_f C_f L a : ℝ) (n : ℕ) : ℝ :=
  ⨅ (C : {C // C ∈ HonestIntervals α c_f C_f L n}),
    ⨆ (P : {P // P ∈ StrengthSlice c_f C_f L a n}),
      expectedLength P.1 n n C.1
  -- @realizes L_n(a)(minimax expected restricted length)

-- @env: S7
variable (nS nT : ℕ)
-- @realizes N_{\mathrm S}(source count) @realizes N_{\mathrm T}(target count)
/-- [The unequal data law object](goal) is defined from [the supplied inputs](hyp:P,nS,nT). -/
noncomputable def unequalDataLaw (P : TransportLaw) (nS nT : ℕ) :
    Measure (TwoSample nS nT) := P.sampleLaw nS nT
/-- [The unequal model class object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L,P,nS,nT). -/

def UnequalModelClass (c_f C_f L : ℝ) (P : TransportLaw) (nS nT : ℕ) : Prop := -- @realizes \mathcal M^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}(unequal product-law class)
  SourceIid P nS nT ∧ TargetIid P nS nT ∧ SampleIndependence P nS nT ∧
  SourceDensityBounds c_f C_f P ∧ TargetDensityBounds c_f C_f P ∧
  SourceDensityHolder L P ∧ TargetDensityHolder L P ∧
  PropensityOverlap P ∧ PropensityHolder L P ∧ ArmMeansHolder L P ∧
  ReceiptConsistency P ∧ OutcomeConsistency P ∧
  InstrumentRandomization P ∧ Exclusion P ∧ Monotonicity P ∧
  TransportComplierOutcome P ∧ TransportComplierShare P ∧
  PositiveStrength P
/-- [The unequal honest intervals object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,nS,nT). -/

def UnequalHonestIntervals (α c_f C_f L : ℝ) (nS nT : ℕ) :
    Set (TwoSample nS nT → Set ℝ) :=
  {C | 0 < α ∧ α < 1 ∧ -- @realizes C_{N_{\mathrm S},N_{\mathrm T}}(random interval binder)
    (∀ ω, C ω ⊆ parameterSpace ∧ OrdConnected (C ω)) ∧
    MeasurableSet {p : TwoSample nS nT × ℝ | p.2 ∈ C p.1} ∧
    ∀ P, UnequalModelClass c_f C_f L P nS nT →
      1 - α ≤ (unequalDataLaw P nS nT
        {ω | targetCACE P ∈ C ω}).toReal} -- @realizes \mathfrak H^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}(honest interval class)

-- @node: def:unequal-sample-handle
/-- [The unequal sample frontier object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,a,nS,nT,_hS,_hT,_ha,_hα). -/
noncomputable def unequalSampleFrontier (α c_f C_f L a : ℝ) -- @realizes a(strength-floor parameter)
    (nS nT : ℕ) (_hS : 0 < nS) (_hT : 0 < nT)
    (_ha : 0 < a ∧ a ≤ 1 / 4) (_hα : 0 < α ∧ α < 1) : ℝ := -- @realizes a(strength floor in (0,1/4])
  ⨅ (C : {C // C ∈ UnequalHonestIntervals α c_f C_f L nS nT}),
    ⨆ (P : {P // UnequalModelClass c_f C_f L P nS nT ∧
      a ≤ firstStage P ∧ firstStage P ≤ 1 / 4}), -- @realizes \mathcal M^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}(a)(strength-restricted law binder)
      expectedLength P.1 nS nT C.1
  -- @realizes R_{N_{\mathrm S},N_{\mathrm T}}(a)(unequal-sample frontier)

-- @node: oeq:unequal-sample-frontier
/-- [The unequal sample frontier question object](goal) is defined without additional inputs. -/
def unequalSampleFrontierQuestion : _root_.String :=
  "Open: determine the exact piecewise order of R_(N_S,N_T)(a) when source and target counts diverge at unrelated rates, and find one finite-sample honest interval and a matching legal monotone-IV lower family in every phase. " ++
  "The equal-count frontier has order min{1,n^(-1/3)/a}; a source-only construction gives an off-diagonal lower term min{1,N_S^(-1/3)/a} when its strength range is nonempty. " ++
  "Mixed source-target quadratic and cubic projections have distinct variance powers; the target-limited term and matching multiresolution upper bound remain undetermined. This text poses a question and asserts no solution."

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
