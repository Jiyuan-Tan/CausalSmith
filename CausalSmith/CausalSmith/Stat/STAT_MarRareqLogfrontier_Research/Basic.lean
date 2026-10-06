module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.Main
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite full-data and observed experiments for the rare-arrival MAR frontier.
The finite-table encoding is deliberate: the available POSystem and MinimaxATE
models have a different observational alphabet. The generic minimax value is reused. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @env: S1
variable (n d : ℕ) (q : ℝ)
/-- For [the specified inputs and assumptions](hyp:d), [the mathematical structure](goal) records the components specified by this declaration. -/
structure FullRecord (d : ℕ) where
  X : Fin d -- @realizes \(X\)(baseline category); @realizes \(d\)(alphabet size)
  A : Bool -- @realizes \(A\)(binary randomized arm)
  S0 : Bool -- @realizes \(S(a)\)(control surrogate)
  S1 : Bool -- @realizes \(S(a)\)(treated surrogate)
  Y0 : Bool -- @realizes \(Y(a)\)(control outcome)
  Y1 : Bool -- @realizes \(Y(a)\)(treated outcome)
  R : Bool -- @realizes \(R\)(arrival flag)
  deriving DecidableEq

attribute [inherit_doc FullRecord] instDecidableEqFullRecord

/-- For [the specified inputs and assumptions](hyp:d,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def FullRecord.S {d : ℕ} (r : FullRecord d) : Bool :=
  if r.A then r.S1 else r.S0 -- @realizes \(S\)(assigned-arm surrogate)

/-- For [the specified inputs and assumptions](hyp:d,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def FullRecord.Y {d : ℕ} (r : FullRecord d) : Bool :=
  if r.A then r.Y1 else r.Y0 -- @realizes \(Y\)(assigned-arm outcome)

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
instance (d : ℕ) : MeasurableSpace (FullRecord d) := ⊤

/-- For [the specified inputs and assumptions](hyp:d), [the mathematical structure](goal) records the components specified by this declaration. -/
structure ObsRecord (d : ℕ) where
  X : Fin d
  A : Bool
  S : Bool
  R : Bool
  RY : Bool
  deriving DecidableEq, Fintype

attribute [inherit_doc ObsRecord] instDecidableEqObsRecord instFintypeObsRecord

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
instance (d : ℕ) : MeasurableSpace (ObsRecord d) := ⊤

/-- For [the specified inputs and assumptions](hyp:d,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def obs {d : ℕ} (r : FullRecord d) : ObsRecord d :=
  ⟨r.X, r.A, r.S, r.R, r.R && r.Y⟩ -- @realizes \(O\)(X,A,S,R,RY)

-- @realizes \(a\)(arm index)
-- @realizes \(x\)(baseline index)
-- @realizes \(s\)(surrogate index)
/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev Cell (d : ℕ) := Bool × Fin d × Bool
  -- @realizes \(\mathcal J_d\)(cell alphabet)
/-- For [the specified inputs and assumptions](hyp:d,r,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def inCell {d : ℕ} (r : FullRecord d) (j : Cell d) : Prop :=
  r.A = j.1 ∧ r.X = j.2.1 ∧ r.S = j.2.2 -- @realizes \(j\)(a,x,s)

/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev FullLaw (d : ℕ) := {P : Measure (FullRecord d) // IsProbabilityMeasure P}
  -- @realizes \(P\)(probability law on full records)

/-- For [the specified inputs and assumptions](hyp:d,n,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def sampleLaw {d : ℕ} (n : ℕ) (P : FullLaw d) : Measure (Fin n → ObsRecord d) :=
  Measure.pi (fun _ : Fin n => P.1.map obs) -- @realizes \(\mathbf O_n\)(canonical iid law)

/-- For [the specified inputs and assumptions](hyp:d,P,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def arrivedCell {d : ℕ} (P : FullLaw d) (j : Cell d) : ℝ :=
  P.1.real {r | inCell r j ∧ r.R = true}

/-- For [the specified inputs and assumptions](hyp:d,P,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def cellProb {d : ℕ} (P : FullLaw d) (j : Cell d) : ℝ :=
  P.1.real {r | inCell r j} -- @realizes \(p_{axs}(P)\)(cell probability)

/-- For [the specified inputs and assumptions](hyp:d,P,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def arrivalProb {d : ℕ} (P : FullLaw d) (j : Cell d) : ℝ :=
  if 0 < cellProb P j then arrivedCell P j / cellProb P j else 0
  -- @realizes \(\rho_{axs}(P)\)(occupied-cell arrival probability)

/-- For [the specified inputs and assumptions](hyp:d,P,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def cellMean {d : ℕ} (P : FullLaw d) (j : Cell d) : ℝ :=
  if 0 < arrivedCell P j then
    P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} / arrivedCell P j
  else 0
  -- @realizes \(\mu_{axs}(P)\)(zero when the arrived-cell mass is zero)

/-- For [the specified inputs and assumptions](hyp:d,P,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def cellContribution {d : ℕ} (P : FullLaw d) (j : Cell d) : ℝ :=
  if 0 < arrivedCell P j then cellProb P j * cellMean P j else 0
  -- @realizes \(c_{axs}(P)\)(zero when the arrived-cell mass is zero)

/-- For [the specified inputs and assumptions](hyp:a), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def armSign (a : Bool) : ℝ := if a then 1 else -1 -- @realizes \(g(a)\)(arm sign)

-- @node: ass:iid-sampling
/-- For [the specified inputs and assumptions](hyp:Ω,d,n,μ,O,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def IIDSampling {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (n : ℕ)
    (μ : Measure Ω) (O : Fin n → Ω → ObsRecord d) (P : FullLaw d) : Prop :=
  (∀ i, Measurable (O i)) ∧ iIndepFun O μ ∧ ∀ i, μ.map (O i) = P.1.map obs
  -- @realizes \(O_i\)(iid coordinate)

-- @node: ass:randomized-independence
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def RandomizedIndependence {d : ℕ} (P : FullLaw d) : Prop :=
  IndepFun FullRecord.A (fun r : FullRecord d => (r.X, r.S0, r.S1, r.Y0, r.Y1)) P.1

-- @node: ass:balanced-randomization
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def BalancedRandomization {d : ℕ} (P : FullLaw d) : Prop :=
  P.1.real {r | r.A = true} = 1 / 2
  -- @realizes \(\Phi(P)\)(standing balanced-randomization domain)

-- @node: ass:surrogate-consistency
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def SurrogateConsistency {d : ℕ} (P : FullLaw d) : Prop :=
  ∀ᵐ r : FullRecord d ∂(P.1), r.S = if r.A then r.S1 else r.S0

-- @node: ass:outcome-consistency
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def OutcomeConsistency {d : ℕ} (P : FullLaw d) : Prop :=
  ∀ᵐ r : FullRecord d ∂(P.1), r.Y = if r.A then r.Y1 else r.Y0

-- @node: ass:arrival-mar
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def ArrivalMAR {d : ℕ} (P : FullLaw d) : Prop :=
  ∀ (j : Cell d) (y r : Bool),
    P.1.real {w | inCell w j ∧ w.R = r ∧ w.Y = y} * cellProb P j =
      P.1.real {w | inCell w j ∧ w.R = r} *
        P.1.real {w | inCell w j ∧ w.Y = y}

-- @node: ass:occupied-cell-arrival
/-- For [the specified inputs and assumptions](hyp:d,q,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def OccupiedCellArrival {d : ℕ} (q : ℝ) (P : FullLaw d) : Prop :=
  ∀ j : Cell d, 0 < cellProb P j → q * cellProb P j ≤ arrivedCell P j

/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- keep: explicit standing-domain realization for the frozen symbols N and N₀
def EffectiveSizeScope (n : ℕ) (q : ℝ) : Prop :=
  1 ≤ n ∧ -- @realizes \(N\)(standing domain: n ≥ 1); @realizes \(N_0\)(standing domain: n ≥ 1)
  0 < q -- @realizes \(N\)(standing domain: q > 0); @realizes \(N_0\)(standing domain: q > 0)

/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def effectiveSize (n : ℕ) (q : ℝ) : ℝ := n * q -- @realizes \(N\)(nq)

/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def logScale (n : ℕ) (q : ℝ) : ℝ := Real.log (Real.exp 1 + effectiveSize n q)
  -- @realizes \(\ell\)(log(e+N))

-- @node: ass:rare-arrival-slice
/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def RareArrivalSlice (n : ℕ) (q : ℝ) : Prop :=
  q * (logScale n q) ^ 2 ≤ 1 / 64

-- @node: def:unrestricted-arrival-model-class
/-- For [the specified inputs and assumptions](hyp:n,d,q,P), [the mathematical structure](goal) records the components specified by this declaration. -/
structure UnrestrictedArrivalModelClass (n d : ℕ) (q : ℝ) (P : FullLaw d) : Prop where
  n_pos : 1 ≤ n -- @realizes \(n\)(positive sample size); @realizes \(m\)(standing domain: n ≥ 1); @realizes \(B\)(standing domain: n ≥ 1); @realizes \(H\)(standing domain: n ≥ 1)
  d_pos : 1 ≤ d -- @realizes \(d\)(nonempty alphabet)
  q_pos : 0 < q -- @realizes \(q\)(positive arrival floor); @realizes \(B\)(standing domain: q > 0); @realizes \(H\)(standing domain: q > 0)
  q_le_one : q ≤ 1 -- @realizes \(q\)(at most one)
  randomized : RandomizedIndependence P
  balanced : BalancedRandomization P
  surrogate : SurrogateConsistency P
  outcome : OutcomeConsistency P
  mar : ArrivalMAR P
  arrival : OccupiedCellArrival q P
  -- @realizes \(\mathcal M^{+}_{n,d,q}\)(unrestricted law class)

-- @node: def:model-class
/-- For [the specified inputs and assumptions](hyp:n,d,q,P), [the mathematical structure](goal) records the components specified by this declaration. -/
structure RareArrivalModelClass (n d : ℕ) (q : ℝ) (P : FullLaw d) : Prop where
  iid : IIDSampling n (sampleLaw n P) (fun (i : Fin n) (ω : Fin n → ObsRecord d) => ω i) P
  randomized : RandomizedIndependence P
  balanced : BalancedRandomization P
  surrogate : SurrogateConsistency P
  outcome : OutcomeConsistency P
  mar : ArrivalMAR P
  arrival : OccupiedCellArrival q P
  slice : RareArrivalSlice n q
  n_pos : 1 ≤ n
  d_pos : 1 ≤ d
  q_pos : 0 < q
  q_le_one : q ≤ 1
  -- @realizes \(\mathcal M_{n,d,q}\)(rare-arrival law class)

-- @node: def:observed-experiment
/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def observedExperiment (n d : ℕ) (q : ℝ) : Set (Measure (Fin n → ObsRecord d)) :=
  {ν | ∃ P : FullLaw d, RareArrivalModelClass n d q P ∧ ν = sampleLaw n P}
  -- @realizes \(\mathcal E_{n,d,q}\)(observed sample laws)

-- @node: def:ate-functional
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def ate {d : ℕ} (P : FullLaw d) : ℝ :=
  ∫ r : FullRecord d, ((if r.Y1 then (1 : ℝ) else 0) - (if r.Y0 then (1 : ℝ) else 0)) ∂(P.1)
  -- @realizes \(\tau(P)\)(E[Y1-Y0])

-- @node: def:cell-functional
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def cellFunctional {d : ℕ} (P : FullLaw d) : ℝ :=
  2 * ∑ j : Cell d, armSign j.1 * cellContribution P j
  -- @realizes \(\Phi(P)\)(observed-cell contrast)

-- @node: def:frontier-rate
/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def frontierRate (n d : ℕ) (q : ℝ) : ℝ :=
  min 1 ((effectiveSize n q)⁻¹ +
    ((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2)
  -- @realizes \(r_{n,d,q}\)(candidate rate)

/-- For [the specified inputs and assumptions](hyp:Z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev BoundedRealKernel (Z : Type*) [MeasurableSpace Z] :=
  {K : Kernel Z ℝ // IsMarkovKernel K ∧ ∀ o, K o (Icc (-1 : ℝ) 1) = 1}

/-- For [the specified inputs and assumptions](hyp:n,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev Estimator (n d : ℕ) := BoundedRealKernel (Fin n → ObsRecord d)
  -- @realizes \(\mathsf T\)(all bounded parameter-independent Markov kernels)
  -- @realizes \(\mathcal T_n\)(all bounded Markov kernels, including Dirac kernels)

/-- For [the specified inputs and assumptions](hyp:n,d,f,hf), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def Estimator.ofMap {n d : ℕ}
    (f : (Fin n → ObsRecord d) → ℝ)
    (hf : Measurable f ∧ ∀ s, f s ∈ Icc (-1 : ℝ) 1) : Estimator n d :=
  ⟨Kernel.deterministic f hf.1, inferInstance, by
    intro s
    rw [Kernel.deterministic_apply, Measure.dirac_apply]
    rw [Set.indicator_of_mem (hf.2 s)]
    rfl⟩

/-- For [the specified inputs and assumptions](hyp:n,d,T), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev Estimator.toBoundedKernel {n d : ℕ} (T : Estimator n d) := T

/-- Given [the specified inputs and assumptions](hyp:n,d,T), [the stated mathematical conclusion holds](goal). -/
@[simp] lemma Estimator.toBoundedKernel_val {n d : ℕ} (T : Estimator n d) :
    T.toBoundedKernel.1 = T.1 := rfl

/-- For [the specified inputs and assumptions](hyp:n,d,T,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def squaredRisk {n d : ℕ} (T : Estimator n d) (P : FullLaw d) : ℝ :=
  ∫ s, (∫ t, (t - ate P) ^ 2 ∂(T.1 s)) ∂(sampleLaw n P)

/-- For [the specified inputs and assumptions](hyp:n,d,f,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def deterministicRisk {n d : ℕ}
    (f : (Fin n → ObsRecord d) → ℝ) (P : FullLaw d) : ℝ :=
  ∫ s, (f s - ate P) ^ 2 ∂(sampleLaw n P)

-- @node: def:minimax-risk
/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def minimaxRisk (n d : ℕ) (q : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (E := Estimator n d) (Θ := {P : FullLaw d // RareArrivalModelClass n d q P})
    (fun T P => squaredRisk T P.1)
  -- @realizes \(\mathfrak R_{n,d,q}\)(rare-arrival minimax risk)

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev EndpointPair := {p : ℝ × ℝ // -1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}
/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def ConnectedInterval : Type := EndpointPair

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
instance : MeasurableSpace ConnectedInterval := by
  unfold ConnectedInterval
  infer_instance

/-- Given [the specified inputs and assumptions](hyp:I), [the stated mathematical conclusion holds](goal). -/
@[simp] def ConnectedInterval.lo (I : ConnectedInterval) : ℝ := I.1.1
/-- The [interval](hyp:I) has [right endpoint equal to its second coordinate](goal). -/
@[simp] def ConnectedInterval.hi (I : ConnectedInterval) : ℝ := I.1.2
/-- The [interval](hyp:I) has [left endpoint at least minus one](goal). -/
lemma ConnectedInterval.lower (I : ConnectedInterval) : -1 ≤ I.lo := I.2.1
/-- Given [the specified inputs and assumptions](hyp:I), [the stated mathematical conclusion holds](goal). -/
lemma ConnectedInterval.ordered (I : ConnectedInterval) : I.lo ≤ I.hi := I.2.2.1
/-- Given [the specified inputs and assumptions](hyp:I), [the stated mathematical conclusion holds](goal). -/
lemma ConnectedInterval.upper (I : ConnectedInterval) : I.hi ≤ 1 := I.2.2.2

/-- [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_connectedInterval_lo : Measurable ConnectedInterval.lo :=
  measurable_fst.comp measurable_subtype_coe
/-- [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_connectedInterval_hi : Measurable ConnectedInterval.hi :=
  measurable_snd.comp measurable_subtype_coe

/-- For [the specified inputs and assumptions](hyp:I,t), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
@[simp] def ConnectedInterval.closedLeft (_I : ConnectedInterval) : Bool := true
/-- The [connected interval](hyp:_I) is [closed at its right endpoint](goal). -/
@[simp] def ConnectedInterval.closedRight (_I : ConnectedInterval) : Bool := true

/-- The [interval](hyp:I) [contains the point](hyp:t) exactly when both endpoint tests hold. -/
def intervalContains (I : ConnectedInterval) (t : ℝ) : Prop :=
  (if I.closedLeft then I.lo ≤ t else I.lo < t) ∧
  (if I.closedRight then t ≤ I.hi else t < I.hi)

/-- For [the specified inputs and assumptions](hyp:n,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev IntervalProcedure (n d : ℕ) :=
  {K : Kernel (Fin n → ObsRecord d) ConnectedInterval // IsMarkovKernel K}
  -- @realizes \(\mathsf I\)(all kernels to Borel ordered endpoint pairs)

/-- A [measurable interval-valued map](hyp:f,hf) defines the corresponding [deterministic interval procedure](goal). -/
noncomputable def IntervalProcedure.ofMap {n d : ℕ}
    (f : (Fin n → ObsRecord d) → ConnectedInterval) (hf : Measurable f) :
    IntervalProcedure n d := ⟨Kernel.deterministic f hf, inferInstance⟩

/-- For [the specified inputs and assumptions](hyp:n,d,q,α,T), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def HonestInterval (n d : ℕ) (q α : ℝ) (T : IntervalProcedure n d) : Prop :=
  ∀ P : FullLaw d, RareArrivalModelClass n d q P →
    1 - α ≤ ∫ s, (T.1 s).real {I | intervalContains I (ate P)} ∂(sampleLaw n P)
  -- @realizes \(\mathcal C_{n,d,q,\alpha}\)(uniform coverage)

/-- For [the specified inputs and assumptions](hyp:n,d,T,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def intervalRisk {n d : ℕ} (T : IntervalProcedure n d)
    (P : FullLaw d) : ℝ :=
  ∫ s, (∫ I : ConnectedInterval, I.hi - I.lo ∂(T.1 s)) ∂(sampleLaw n P)

/-- For [the specified inputs and assumptions](hyp:n,d,f,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def deterministicIntervalRisk {n d : ℕ}
    (f : (Fin n → ObsRecord d) → ℝ × ℝ) (P : FullLaw d) : ℝ :=
  ∫ s, (f s).2 - (f s).1 ∂(sampleLaw n P)

-- @node: def:interval-length-risk
/-- For [the specified inputs and assumptions](hyp:n,d,q,α), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def intervalLengthRisk (n d : ℕ) (q α : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (E := {T : IntervalProcedure n d // HonestInterval n d q α T})
    (Θ := {P : FullLaw d // RareArrivalModelClass n d q P})
    (fun T P => intervalRisk T.1 P.1)
  -- @realizes \(\mathfrak L_{n,d,q,\alpha}\)(honest interval length risk)

-- @node: def:unrestricted-minimax-risk
/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def unrestrictedMinimaxRisk (n d : ℕ) (q : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (E := Estimator n d)
    (Θ := {P : FullLaw d // UnrestrictedArrivalModelClass n d q P})
    (fun T P => squaredRisk T P.1)
  -- @realizes \(\mathfrak R^{+}_{n,d,q}\)(unrestricted minimax risk)

/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev ZengRecord (d : ℕ) := Fin d × Bool × Bool
  -- @realizes \(B^{\mathrm{obs}}\)(observational treatment)
/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev ZengLaw (d : ℕ) := {P : Measure (ZengRecord d) // IsProbabilityMeasure P}

/-- For [the specified inputs and assumptions](hyp:d,P,x), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def zengCategory {d : ℕ} (P : ZengLaw d) (x : Fin d) : ℝ :=
  P.1.real {r | r.1 = x}
/-- For [the specified inputs and assumptions](hyp:d,P,x,b), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def zengArm {d : ℕ} (P : ZengLaw d) (x : Fin d) (b : Bool) : ℝ :=
  P.1.real {r | r.1 = x ∧ r.2.1 = b}
/-- For [the specified inputs and assumptions](hyp:d,P,x,b,_h), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengMean {d : ℕ} (P : ZengLaw d) (x : Fin d) (b : Bool)
    (_h : 0 < zengCategory P x) : ℝ :=
  P.1.real {r | r.1 = x ∧ r.2.1 = b ∧ r.2.2 = true} / zengArm P x b

-- @node: def:zeng-discrete-ate-class
/-- For [the specified inputs and assumptions](hyp:d,ε), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def zengDiscreteClass (d : ℕ) (ε : ℝ) : Set (ZengLaw d) :=
  -- @realizes \(\epsilon\)(strict positivity margin)
  {P | 0 < ε ∧ ε < 1 / 2 ∧ 1 ≤ d ∧
    ∀ x : Fin d, 0 < zengCategory P x →
      ε * zengCategory P x ≤ zengArm P x true ∧
        zengArm P x true ≤ (1 - ε) * zengCategory P x}
  -- @realizes \(\mathcal D_{d,\epsilon}\)(occupied-category positivity)

-- @node: def:zeng-ate-functional
/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengATE {d : ℕ} (P : ZengLaw d) : ℝ :=
  ∑ x : Fin d, if h : 0 < zengCategory P x then
    zengCategory P x * (zengMean P x true h - zengMean P x false h) else 0
  -- @realizes \(\theta_Z(P_Z)\)(total observational ATE)

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def ReciprocalBestApproximation : Sort 0 :=
  ∀ K : ℕ, 2 ≤ K →
    Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.bestUniformApproxError
      (fun z : ℝ => z⁻¹) 1 ((K : ℝ) ^ 2) K =
      (((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2)) *
        (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K

/-- [the stated mathematical conclusion holds](goal). -/
-- keep: discharges cited node lem:reciprocal-best-approximation; stable staging theorem, relink to promoted Causalean module after study
-- @node: lem:reciprocal-best-approximation
lemma reciprocalBestApproximation_proved : ReciprocalBestApproximation := by
  intro K hK
  exact bestUniformApproxError_reciprocal_one_sq K hK

end CausalSmith.Stat.MarRareqLogfrontier
