module
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-! Public schedule space, structural laws, model assumptions and decision problems.
The model has bounded fixed-dose potential outcomes; ranks constrain only lower witnesses. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The compact public dose and rank domain. -/
abbrev Dose := Set.Icc (0 : ℝ) 1
/-- Continuous threshold profiles with the uniform topology and its Borel sigma algebra. -/
abbrev ThresholdProfile := C(Dose, Dose)
/-- The threshold-profile space is equipped with [its Borel measurable structure](goal). -/
instance : MeasurableSpace ThresholdProfile := borel ThresholdProfile

-- @env: S1
variable {S : Type*} [MeasurableSpace S] -- @realizes Yspace(public measurable schedule carrier)

/-- Data carried by a public Borel schedule space. -/
structure PathSpaceData (S : Type*) [MeasurableSpace S] where
  eval : S → ℝ → ℝ -- @realizes evalpath(schedule evaluation on the dose domain)
  measurable_eval : Measurable (fun p : S × Dose => eval p.1 p.2) -- @realizes evalpath(joint measurability on S × [0,1])
  eval_injective : Function.Injective (fun s : S => fun a : Dose => eval s a) -- @realizes Yspace(extensional identity of functions on [0,1])
  embed : ThresholdProfile × Dose → S
  measurable_embed : Measurable embed -- @realizes Yspace(measurable threshold-schedule inclusion)
  eval_embed : ∀ f u a, eval (embed (f, u)) (a : Dose) = if (u : ℝ) ≤ (f a : ℝ) then 1 else 0

/-- Public Borel schedules with jointly measurable evaluation and measurable threshold embedding. -/
-- @node: def:potential-path-space
def PathSpace (S : Type*) [MeasurableSpace S] : Type _ := PathSpaceData S

/-- Structural coordinates (X,A,Z,schedule,Y,U). -/
abbrev StructSpace (S : Type*) := Bool × ℝ × ℝ × S × ℝ × ℝ
/-- Stratum coordinate of a structural record. -/
abbrev sX (w : StructSpace S) : Bool := w.1 -- @realizes X(carrier Bool = {0,1})
/-- Latent treatment coordinate of a structural record. -/
abbrev sA (w : StructSpace S) : ℝ := w.2.1 -- @realizes A(real carrier; support below)
/-- Classical error coordinate of a structural record. -/
abbrev sZ (w : StructSpace S) : ℝ := w.2.2.1 -- @realizes Z(real Gaussian coordinate)
/-- Whole potential-outcome schedule coordinate of a structural record. -/
abbrev sSched (w : StructSpace S) : S := w.2.2.2.1 -- @realizes Yprocess(schedule coordinate)
/-- Observed outcome coordinate of a structural record. -/
abbrev sY (w : StructSpace S) : ℝ := w.2.2.2.2.1 -- @realizes Y(observed outcome coordinate)
/-- Auxiliary rank coordinate of a structural record. -/
abbrev sU (w : StructSpace S) : ℝ := w.2.2.2.2.2 -- @realizes U(auxiliary real rank; range constrained for witnesses)
/-- The two public confounder strata. -/
abbrev Xset := Bool -- @realizes Xset(two strata)
/-- The prespecified target dose is one half. -/
-- @node: a0
def a0 : ℝ := 1 / 2 -- @realizes a0(target dose 1/2 ∈ [0,1])
/-- [The noncoverage level one tenth](goal), recorded as an example value only: no result of this development uses it, since the honest-interval and frontier results quantify over the noncoverage level α. -/
def honestyAlpha : ℝ := 1 / 10
/-- Latent dose centered at the target. -/
def latentCentered (w : StructSpace S) : ℝ := sA w - a0 -- @realizes T(T=A-a0; latent support supplies range)
/-- Observed contaminated dose, formed by adding scaled classical error to the latent treatment. -/
def contaminatedDose (sigma : ℝ) (w : StructSpace S) : ℝ := sA w + sigma * sZ w -- @realizes W(W=A+sigma Z)
/-- Observed dose centered at the target. -/
def observedCentered (sigma : ℝ) (w : StructSpace S) : ℝ := contaminatedDose sigma w - a0 -- @realizes V(V=W-a0)
/-- Public observed record consisting of stratum, contaminated dose and outcome. -/
abbrev Obs := Bool × ℝ × ℝ -- @realizes O(record carrier)
/-- The structural-to-observed record map. -/
def obsMap (sigma : ℝ) (w : StructSpace S) : Obs := (sX w, contaminatedDose sigma w, sY w) -- @realizes O(O=(X,W,Y))
/-- One-record observed law obtained by pushing forward the structural law. -/
def obsLaw (sigma : ℝ) (P : Measure (StructSpace S)) : Measure Obs := P.map (obsMap sigma)
/-- Probability mass of a public confounder stratum. -/
def strataProb (P : Measure (StructSpace S)) (x : Bool) : ℝ := P.real {w | sX w = x} -- @realizes px(p_x=P(X=x))
/-- Evaluation of a subject’s potential-outcome schedule at a fixed dose. -/
def potentialOutcome (E : PathSpace S) (w : StructSpace S) (a : ℝ) : ℝ := E.eval (sSched w) a -- @realizes Yprocess(Y(a)=evalpath(Yprocess,a))
/-- Population potential-outcome expectation at the target dose. -/
def causalTarget (E : PathSpace S) (P : Measure (StructSpace S)) : ℝ := ∫ w, potentialOutcome E w a0 ∂P -- @realizes theta(theta=E[Y(a0)])

/-- Conditional potential mean, defined by its stratum-restricted integral divided by stratum mass. -/
-- @node: def:conditional-potential-mean
def condPotMean (E : PathSpace S) (P : Measure (StructSpace S)) (x : Bool) (a : ℝ) : ℝ :=
  (∫ w, (if sX w = x then potentialOutcome E w a else 0) ∂P) / strataProb P x -- @realizes mux(conditional potential mean ratio)

/-- Public constants of the model class: a minimum stratum mass in (0, 1/2] and lower and upper weak-design envelope constants with 0 < lower ≤ upper. -/
structure ClassConstants where
  pmin : ℝ
  clo : ℝ
  chi : ℝ
  pmin_pos : 0 < pmin
  pmin_le_half : pmin ≤ 1/2
  clo_pos : 0 < clo
  clo_le_chi : clo ≤ chi

/-- [Both strata](hyp:P) [have mass at least the public minimum and at most one minus it](goal), [the minimum being the given number](hyp:pmin). -/
-- @node: ass:stratum-overlap
def StratumOverlap (pmin : ℝ) (P : Measure (StructSpace S)) : Prop :=
  ∀ x, pmin ≤ strataProb P x ∧ strataProb P x ≤ 1 - pmin -- @realizes px(range [pmin,1-pmin])
/-- [Both strata of the law](hyp:P) [have strictly positive mass](goal). -/
def StratumPositive (P : Measure (StructSpace S)) : Prop :=
  ∀ x, 0 < strataProb P x
/-- The latent treatment has compact support. -/
-- @node: ass:latent-support
def LatentSupport (P : Measure (StructSpace S)) : Prop :=
  ∀ᵐ w ∂P, sA w ∈ Icc 0 1 -- @realizes A(a.s. range [0,1]) @realizes T(centered support [-1/2,1/2])
/-- Structural law conditioned on a finite confounder stratum, by normalized restriction. -/
def stratumLaw (P : Measure (StructSpace S)) (x : Bool) : Measure (StructSpace S) :=
  (P {w | sX w = x})⁻¹ • P.restrict {w | sX w = x}
/-- [In each stratum of the law](hyp:P), [the centered latent dose has a density lying between the lower envelope constant and the upper envelope constant times the absolute centered dose raised to the design exponent](goal), [the lower constant](hyp:clo), [the upper constant](hyp:chi) and [the design exponent](hyp:kappa) being given. -/
-- @node: ass:weak-design
def WeakDesign (clo chi kappa : ℝ) (P : Measure (StructSpace S)) : Prop :=
  ∃ g : Bool → ℝ → ℝ, -- @realizes gx(density carrier)
    (∀ x, Measurable (g x)) ∧
    (∀ x, (stratumLaw P x).map latentCentered =
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))).withDensity (fun t => ENNReal.ofReal (g x t))) ∧ -- @realizes gx(density of T conditional on X)
    (∀ x, ∀ᵐ t ∂(volume.restrict (Icc (-1/2 : ℝ) (1/2))),
      clo * |t| ^ kappa ≤ g x t ∧ g x t ≤ chi * |t| ^ kappa) -- @realizes gx(nonnegative polynomial envelopes)
/-- Radius-one Holder increment bound on the public dose interval. -/
-- @node: ass:holder-mean
def HolderMean (E : PathSpace S) (beta : ℝ) (P : Measure (StructSpace S)) : Prop :=
  ∀ x, ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
    |condPotMean E P x a - condPotMean E P x b| ≤ |a-b| ^ beta -- @realizes mux(Holder-beta seminorm at most one)
/-- The conditional potential means lie in the unit interval. -/
-- @node: ass:mean-range
def MeanRange (E : PathSpace S) (P : Measure (StructSpace S)) : Prop :=
  ∀ x, ∀ a ∈ Icc (0 : ℝ) 1, condPotMean E P x a ∈ Icc 0 1 -- @realizes mux(range [0,1])
/-- Standard Gaussian measurement-error coordinate. -/
-- @node: ass:gaussian-channel
def GaussianChannel (P : Measure (StructSpace S)) : Prop :=
  P.map sZ = gaussianReal 0 1 -- @realizes Z(standard Gaussian law)
/-- Classical error is independent of stratum, treatment and the whole schedule. -/
-- @node: ass:error-independence
def ErrorIndependence (P : Measure (StructSpace S)) : Prop :=
  IndepFun sZ (fun w => (sX w, sA w, sSched w)) P
/-- Uniform auxiliary rank in each stratum, used only in the lower witnesses. -/
-- @node: ass:rank-uniform
def RankUniform (P : Measure (StructSpace S)) : Prop :=
  ∀ x, (stratumLaw P x).map sU = volume.restrict (Icc 0 1) -- @realizes U(conditional uniform [0,1] law)
/-- Rank-dose conditional independence through finite-stratum factorization. -/
-- @node: ass:rank-treatment-independence
def RankTreatmentIndependence (P : Measure (StructSpace S)) : Prop :=
  ∀ x (B D : Set ℝ), MeasurableSet B → MeasurableSet D →
    P.real {w | sU w ∈ B ∧ sA w ∈ D ∧ sX w = x} * strataProb P x =
    P.real {w | sU w ∈ B ∧ sX w = x} * P.real {w | sA w ∈ D ∧ sX w = x}
/-- Common-rank threshold schedules for the lower subclass. -/
-- @node: ass:structural-threshold
def StructuralThreshold (E : PathSpace S) (P : Measure (StructSpace S)) : Prop :=
  ∀ᵐ w ∂P, ∀ a ∈ Icc (0 : ℝ) 1,
    potentialOutcome E w a = if sU w ≤ condPotMean E P (sX w) a then 1 else 0
/-- Observed outcomes are consistent with the realized latent dose. -/
-- @node: ass:consistency
def DoseConsistency (E : PathSpace S) (P : Measure (StructSpace S)) : Prop :=
  ∀ᵐ w ∂P, sY w = potentialOutcome E w (sA w) -- @realizes Y(Y=Y(A) a.s.)
/-- Whole-schedule exchangeability through exact finite-stratum factorization. -/
-- @node: ass:conditional-unconfoundedness
def ScheduleUnconfoundedness (P : Measure (StructSpace S)) : Prop :=
  ∀ x (B : Set S) (D : Set ℝ), MeasurableSet B → MeasurableSet D →
    P.real {w | sSched w ∈ B ∧ sA w ∈ D ∧ sX w = x} * strataProb P x =
    P.real {w | sSched w ∈ B ∧ sX w = x} * P.real {w | sA w ∈ D ∧ sX w = x}
/-- Binary outcomes at every fixed dose; fixed-dose null sets may differ. -/
-- @node: ass:binary-potential-outcomes
def BinaryPotentialOutcomes (E : PathSpace S) (P : Measure (StructSpace S)) : Prop :=
  ∀ a ∈ Icc (0 : ℝ) 1, ∀ᵐ w ∂P, potentialOutcome E w a = 0 ∨ potentialOutcome E w a = 1
/-- Bounded outcomes at every fixed dose, with exactly the fixed-dose quantifier order. -/
-- @node: ass:bounded-potential-outcomes
def BoundedPotentialOutcomes (E : PathSpace S) (P : Measure (StructSpace S)) : Prop :=
  ∀ a ∈ Icc (0 : ℝ) 1, ∀ᵐ w ∂P, potentialOutcome E w a ∈ Icc 0 1 -- @realizes Yprocess(fixed-dose a.s. range [0,1])

/-- The bounded causal model bundles exactly its ten declared member assumptions. -/
-- @node: def:model-class
structure NoisyDoseModelClass (E : PathSpace S) (K : ClassConstants) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) : Prop where
  stratumOverlap : StratumOverlap K.pmin P
  latentSupport : LatentSupport P
  weakDesign : WeakDesign K.clo K.chi kappa P
  holderMean : HolderMean E beta P
  meanRange : MeanRange E P
  gaussianChannel : GaussianChannel P
  errorIndependence : ErrorIndependence P
  scheduleUnconfoundedness : ScheduleUnconfoundedness P
  boundedPO : BoundedPotentialOutcomes E P
  consistency : DoseConsistency E P

/-- [Every member law of the model](hyp:hP) [gives both strata strictly positive mass](goal), since the public minimum stratum mass is positive. -/
lemma NoisyDoseModelClass.strataPos {E : PathSpace S} {K : ClassConstants} {beta kappa sigma : ℝ}
    {P : Measure (StructSpace S)} (hP : NoisyDoseModelClass E K beta kappa sigma P) :
    StratumPositive P :=
  fun x => lt_of_lt_of_le K.pmin_pos (hP.stratumOverlap x).1

/-- Probability laws satisfying exactly the bounded noisy-dose causal model assumptions. -/
def modelClass (E : PathSpace S) (K : ClassConstants) (beta kappa sigma : ℝ) : Set (ProbabilityMeasure (StructSpace S)) := -- @realizes P(probability-law carrier on structural coordinates)
  {P | NoisyDoseModelClass E K beta kappa sigma (P : Measure (StructSpace S))} -- @realizes Pclass(probability laws satisfying the ten assumptions)

/-- Independent observed records from the pushed-forward structural law. -/
-- @node: def:observed-experiment
def experiment (n : ℕ) (sigma : ℝ) (P : Measure (StructSpace S)) : Measure (Fin n → Obs) :=
  Measure.pi (fun _ => obsLaw sigma P) -- @realizes Qn(n-fold observed product law)
/-- The sample law is the iid observed product law. -/
-- @node: ass:iid
def IIDSampling (n : ℕ) (sigma : ℝ) (P : Measure (StructSpace S)) (Qs : Measure (Fin n → Obs)) : Prop :=
  Qs = Measure.pi (fun _ => obsLaw sigma P)
/-- The constructed observed experiment satisfies the declared iid sampling predicate. [This is the stated conclusion](goal). -/
-- @node: iidSampling_holds
lemma iidSampling_holds (n : ℕ) (sigma : ℝ) (P : Measure (StructSpace S)) :
    IIDSampling n sigma P (experiment n sigma P) := by
  rfl

/-- An independent uniform seed on the unit interval for randomized procedures. -/
def seedLaw : Measure ℝ := volume.restrict (Icc 0 1)
/-- Observed iid records together with an independent uniform randomization seed. -/
def randomizedExperiment (n : ℕ) (sigma : ℝ) (P : Measure (StructSpace S)) : Measure ((Fin n → Obs) × ℝ) :=
  (experiment n sigma P).prod seedLaw

/-- All measurable estimators, including independent uniform randomization. -/
abbrev Estimator (n : ℕ) := {T : ((Fin n → Obs) × ℝ) → ℝ // Measurable T}
/-- Complete-lattice minimax absolute risk, with non-integrable losses retaining infinite risk. -/
-- @node: def:minimax-risk
def minimaxRisk (E : PathSpace S) (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal (fun (T : Estimator n) (P : modelClass E K beta kappa sigma) =>
    ∫⁻ z, ENNReal.ofReal |T.1 z - causalTarget E (P.1 : Measure (StructSpace S))|
      ∂randomizedExperiment n sigma (P.1 : Measure (StructSpace S))) -- @realizes Rn(randomized minimax absolute risk)
/-- Measurable connected intervals based solely on the observed sample, with unrestricted endpoint types. -/
structure IntervalProcedure (n : ℕ) where
  C : (Fin n → Obs) → Set ℝ
  connected : ∀ z, (C z).OrdConnected
  measurable : MeasurableSet {p : (Fin n → Obs) × ℝ | p.2 ∈ C p.1}
/-- A connected interval procedure covers the causal target with the required probability under every member law. -/
def IsHonest (E : PathSpace S) (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ) (C : IntervalProcedure n) : Prop :=
  ∀ P : modelClass E K beta kappa sigma,
    ENNReal.ofReal (1-alpha) ≤ experiment n sigma (P.1 : Measure (StructSpace S))
      {z | causalTarget E (P.1 : Measure (StructSpace S)) ∈ C.C z}
/-- Minimum worst-law expected length among honest connected interval procedures. -/
-- @node: def:honest-length
def honestLength (E : PathSpace S) (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  ⨅ C : {C : IntervalProcedure n // IsHonest E K beta kappa alpha n sigma C},
    ⨆ P : modelClass E K beta kappa sigma,
      ∫⁻ z, volume (C.1.C z) ∂experiment n sigma (P.1 : Measure (StructSpace S)) -- @realizes Hn(minimum honest expected connected-interval length)

-- @env: S2
variable (beta kappa sigma : ℝ) (n : ℕ) -- @realizes n(sample size ℕ)
/-- Effective dimension of the direct weak-design estimation problem. -/
def effDim : ℝ := 2*beta+kappa+1 -- @realizes d(effective dimension)
/-- The public logarithmic sample scale. -/
def logScale : ℝ := Real.log (Real.exp 1 * n) -- @realizes Ln(log(en))
/-- Direct weak-design localization scale. -/
def directScale : ℝ := (n : ℝ) ^ (-1 / effDim beta kappa)
/-- Gaussian Fourier-inversion localization scale. -/
def fourierScale : ℝ := sigma / Real.sqrt (Real.log (Real.exp 1 + n * sigma ^ effDim beta kappa))
/-- Compact-support polynomial-inversion localization scale. -/
def polynomialScale : ℝ := Real.log (Real.exp 1 + sigma^2 * logScale n) / logScale n
/-- The exact three-regime localization scale. -/
-- @node: def:frontier-rate
def frontierScale : ℝ :=
  if sigma ≤ directScale beta kappa n then directScale beta kappa n
  else if sigma ≤ (logScale n) ^ (-1/2 : ℝ) then fourierScale beta kappa sigma n
  else polynomialScale sigma n -- @realizes bns(three branches at the stated elbows)
/-- Absolute-risk frontier obtained by raising the localization scale to the smoothness exponent. -/
def frontierRate : ℝ := frontierScale beta kappa sigma n ^ beta -- @realizes rho(bns^beta)
end CausalSmith.Stat.NoisydoseWeakdesignTransition
