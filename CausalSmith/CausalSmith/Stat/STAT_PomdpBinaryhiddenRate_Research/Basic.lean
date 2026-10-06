module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Causalean.Mathlib.Probability.Certified.FiniteKernel
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Basic
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthMembership

/-!
# Fixed-binary POMDP minimax model

The paper-local carrier for a finite partially observed Markov decision process,
its observable-data decision problem, and the partial-history importance-weighted
estimators.  Causalean's generic real-valued minimax API is reused, while the
dependent-trajectory model is defined locally because the substrate contains no
POMDP experiment at this abstraction level.
-/

@[expose] public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- A memoryless policy on the finite observed-state alphabet. -/
abbrev Policy (nX : Nat) := Fin nX → Bool → ℝ
  -- @realizes \(\mathcal A\)(Bool)

/-- The finite observed/latent joint-state alphabet. -/
abbrev JointState (nX nH : Nat) := Fin nX × Fin nH

/-- The observed alphabet of this fixed-binary paper. -/
abbrev BinaryObservedState := Fin 2
  -- @realizes \(\mathcal X\)(exactly Fin 2)

/-- The hidden alphabet of this fixed-binary paper. -/
abbrev BinaryHiddenState := Fin 2
  -- @realizes \(\mathcal H\)(exactly Fin 2)

/-- The four-state product used by the paper's model class. -/
abbrev BinaryJointState := BinaryObservedState × BinaryHiddenState
  -- @realizes \(\mathcal X\)(first Fin 2 coordinate) @realizes \(\mathcal H\)(second Fin 2 coordinate) @realizes \(\mathcal S\)(binary product)

/-- Memoryless policies on the paper's binary observed alphabet. -/
abbrev BinaryPolicy := BinaryObservedState → Bool → ℝ
  -- @realizes \(\mathcal X\)(policy domain Fin 2)

/-- One reward and successor-state block emitted by the POMDP kernel. -/
abbrev Step (nX nH : Nat) := ℝ × JointState nX nH

/-- A length-`T` trajectory has `T+1` states and `T` action/reward pairs. -/
abbrev FullTrajectory (T nX nH : Nat) :=
  (Fin (T + 1) → JointState nX nH) × (Fin T → Bool × ℝ)
  -- @realizes \(T\)(T epochs and T+1 states) @realizes \(S_t\)(state block) @realizes \(A_t\)(action block) @realizes \(Y_t\)(real reward block)

/-- The observable trajectory, with latent and terminal states removed. -/
abbrev ObsView (T nX : Nat) := Fin T → (Fin nX × Bool × ℝ)
  -- @realizes \(\mathsf O_T\)(observed X,A,Y triples)

/-- Raw ingredients of one trajectory experiment. -/
structure RawPomdpExperiment (T nX nH : Nat) where
  K : JointState nX nH → Bool → Measure (Step nX nH) -- @realizes \(K\)(joint reward-successor law)
  b : Policy nX -- @realizes \(b\)(behavior policy carrier)
  e : Policy nX -- @realizes \(e\)(target policy carrier)
  /-- Auxiliary initialization vector used only by finite witness constructors.
  Model-class membership is deliberately independent of this field. -/
  init : JointState nX nH → ℝ
  law : Measure (FullTrajectory T nX nH)
  law_isProbability : IsProbabilityMeasure law

/-- The binary experiment carrier used by every class member and testing law. -/
abbrev BinaryPomdpExperiment (T : Nat) := RawPomdpExperiment T 2 2
  -- @realizes \(\mathcal X\)(observed Fin 2) @realizes \(\mathcal H\)(hidden Fin 2)

/-- For [the M input](hyp:M), [this supplies the inst Is Probability Measure Full Trajectory Law instance](goal). -/
instance {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) :
    IsProbabilityMeasure M.law := M.law_isProbability

-- @env: S1
variable (T : Nat) (t0 zeta : ℝ) (M : RawPomdpExperiment T 2 2)
  -- @realizes \(T\)(trajectory length) @realizes \(t_0\)(mixing scale) @realizes \(\zeta\)(log overlap)

/-- The joint state at a path coordinate, including the terminal coordinate. -/
def stateAt {T nX nH : Nat} (i : Fin (T + 1))
    (tau : FullTrajectory T nX nH) : JointState nX nH := tau.1 i

/-- The current state at epoch `t`. -/
def curState {T nX nH : Nat} (t : Fin T)
    (tau : FullTrajectory T nX nH) : JointState nX nH :=
  tau.1 t.castSucc
  -- @realizes \(S_t\)(current joint state) @realizes \(X_t\)(current observed component) @realizes \(H_t\)(current latent component)

/-- The successor state at epoch `t`, including the final transition. -/
def nextState {T nX nH : Nat} (t : Fin T)
    (tau : FullTrajectory T nX nH) : JointState nX nH :=
  tau.1 t.succ

/-- The observed action at epoch `t`. -/
def actionAt {T nX nH : Nat} (t : Fin T) (tau : FullTrajectory T nX nH) : Bool := tau.2 t |>.1
  -- @realizes \(A_t\)(binary action coordinate)

/-- The observed real reward at epoch `t`. -/
def rewardAt {T nX nH : Nat} (t : Fin T) (tau : FullTrajectory T nX nH) : ℝ := tau.2 t |>.2
  -- @realizes \(Y_t\)(real reward coordinate)

/-- Projection from the full trajectory to exactly the information observed by an estimator. -/
def obsProj {T nX nH : Nat} (tau : FullTrajectory T nX nH) : ObsView T nX :=
  fun t ↦ ((curState t tau).1, actionAt t tau, rewardAt t tau)

/-- The observed trajectory law. -/
noncomputable def obsLaw {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) :
    Measure (ObsView T nX) := M.law.map obsProj
  -- @realizes \(\mathsf O_T\)(pushforward observed law)

/-- Embed an index strictly before `t` into the epoch index set. -/
def prefixIndex {T : Nat} (t : Fin T) (j : Fin t.val) : Fin T := ⟨j.val, lt_trans j.isLt t.isLt⟩

/-- State-and-epoch history strictly before `t`, together with the current state. -/
abbrev StateHistoryView (T nX nH : Nat) (t : Fin T) :=
  ((Fin t.val → JointState nX nH) × (Fin t.val → Bool × ℝ)) × JointState nX nH

/-- A state-history view with the current action adjoined. -/
abbrev ActionHistoryView (T nX nH : Nat) (t : Fin T) :=
  StateHistoryView T nX nH t × Bool

/-- State-and-epoch history strictly before `t`, together with the current state. -/
def histStateView {T nX nH : Nat} (t : Fin T) (tau : FullTrajectory T nX nH) :
    StateHistoryView T nX nH t :=
  (((fun j ↦ curState (prefixIndex t j) tau),
    (fun j ↦ tau.2 (prefixIndex t j))), curState t tau)

/-- The state history with the current action adjoined. -/
def histActionPair {T nX nH : Nat} (t : Fin T) (tau : FullTrajectory T nX nH) :=
  (histStateView t tau, actionAt t tau)

/-- The conditioning view for the reward-transition kernel identity. -/
abbrev histView {T nX nH : Nat} (t : Fin T) :=
  histActionPair (T := T) (nX := nX) (nH := nH) t

/-- The kernel conditioning view with `(Y_t,S_{t+1})` adjoined. -/
def histNextPair {T nX nH : Nat} (t : Fin T) (tau : FullTrajectory T nX nH) :=
  (histView t tau, (rewardAt t tau, nextState t tau))

/-- Read the observed current state from the state-history view. -/
def currentObsState {T nX nH : Nat} (t : Fin T) (h :
    StateHistoryView T nX nH t) : Fin nX := h.2.1

/-- Read `(S_t,A_t)` from the kernel-conditioning view. -/
def currentStateAction {T nX nH : Nat} (t : Fin T) (h :
    ActionHistoryView T nX nH t) :
    JointState nX nH × Bool := (h.1.2, h.2)

/-- The time-homogeneous reward-transition kernel as a Mathlib kernel. -/
noncomputable def kernelOfK {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) :
    Kernel (JointState nX nH × Bool) (Step nX nH) :=
  Kernel.ofFunOfCountable (fun sa ↦ M.K sa.1 sa.2)

/-- The behavior action kernel. -/
noncomputable def behaviourKernel {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) :
    Kernel (Fin nX) Bool :=
  Kernel.ofFunOfCountable fun x ↦
    ∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a

/-- [the measurable current State Action assertion holds](goal). -/
lemma measurable_currentStateAction {T nX nH : Nat} (t : Fin T) :
    Measurable (currentStateAction (nX := nX) (nH := nH) t) := by
  unfold currentStateAction
  fun_prop

/-- [the measurable current Obs State assertion holds](goal). -/
lemma measurable_currentObsState {T nX nH : Nat} (t : Fin T) :
    Measurable (currentObsState (nX := nX) (nH := nH) t) := by
  unfold currentObsState
  fun_prop

/-- A finite vector is a probability vector. -/
def ProbabilityVector {S : Type*} [Fintype S] (p : S → ℝ) : Prop :=
  Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsProbabilityVector p

/-- A policy is pointwise a probability vector on the binary action set. -/
def PolicyVector {nX : Nat} (p : Policy nX) : Prop :=
  ∀ x, (∀ a, 0 ≤ p x a) ∧ ∑ a : Bool, p x a = 1

/-- The joint-state transition matrix induced by a memoryless policy. -/
noncomputable def policyKernel {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (p : Policy nX) (s s' : JointState nX nH) : ℝ :=
  ∑ a : Bool, p s.1 a * (M.K s a {q | q.2 = s'}).toReal
  -- @realizes \(P_p\)(reward-marginalized policy kernel)

/-- Stationarity of a finite probability vector for a transition matrix. -/
def IsStationary {S : Type*} [Fintype S] (P : S → S → ℝ) (d : S → ℝ) : Prop :=
  Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStationary P d

/-- A totalized stationary law, equal to a stationary probability vector whenever one exists. -/
noncomputable def stationaryLaw {S : Type*} [Fintype S]
    (P : S → S → ℝ) : S → ℝ :=
  Classical.epsilon (IsStationary P)
  -- @realizes \(d_p\)(stationary law selected from the stationarity equations)

/-- The selected stationary law satisfies the stationarity equations whenever a witness exists. [the h condition](hyp:h). [the stated conclusion](goal). -/
lemma stationaryLaw_isStationary_of_exists {S : Type*} [Fintype S]
    {P : S → S → ℝ} (h : ∃ d, IsStationary P d) :
    IsStationary P (stationaryLaw P) := by
  exact Classical.epsilon_spec h

/-- Half the finite `ℓ1` norm, the discrete total-variation norm. -/
noncomputable def tvNorm {S : Type*} [Fintype S] (v : S → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |v i|

/-- Apply a finite row kernel to a signed row vector. -/
noncomputable def applyKernel {S : Type*} [Fintype S] (v : S → ℝ)
    (P : S → S → ℝ) : S → ℝ :=
  fun s' ↦ ∑ s, v s * P s s'

/-- Target-policy conditional mean reward at a joint state. -/
noncomputable def rewardRegression {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (s : JointState nX nH) : ℝ :=
  ∑ a : Bool, M.e s.1 a * ∫ p, p.1 ∂(M.K s a)
  -- @realizes \(r_e\)(target-policy reward regression)

/-- The derived contraction factor. -/
noncomputable def mixingAlpha (t0 : ℝ) : ℝ := Real.exp (-(1 / t0))
  -- @realizes \(\alpha\)(exp(-1/t0))

/-- The derived policy-overlap factor. -/
noncomputable def policyFactor (zeta : ℝ) : ℝ := Real.exp zeta
  -- @realizes \(L\)(exp(zeta))


-- @node: ass:pomdp-kernel
/-- The time-homogeneous reward/successor law, with rewards supported on `[0,1]`. -/
def PomdpKernelLaw {T : Nat} (M : RawPomdpExperiment T 2 2) : Prop :=
  (∀ s a, IsProbabilityMeasure (M.K s a)) ∧ -- @realizes \(K\)(probability rows)
  (∀ s a, M.K s a {q | q.1 ∈ Set.Icc (0 : ℝ) 1} = 1) ∧ -- @realizes \(\mathcal Y\)(reward support) @realizes \(Y_t\)(bounded rewards)
  ∀ t : Fin T,
    M.law.map (histNextPair t) =
      (M.law.map (histView t)).compProd
        (Kernel.comap (kernelOfK M) (currentStateAction t)
          (measurable_currentStateAction t)) -- @realizes \(\mathcal F_t^-\)(conditional kernel history)

-- @node: ass:sequential-ignorability
/-- Conditional action randomization through the observed state. -/
def SequentialIgnorability {T : Nat} (M : RawPomdpExperiment T 2 2) : Prop :=
  PolicyVector M.b ∧ -- @realizes \(b\)(behavior policy simplex)
  ∀ t : Fin T,
    M.law.map (histActionPair t) =
      (M.law.map (histStateView t)).compProd
        (Kernel.comap (behaviourKernel M) (currentObsState t)
          (measurable_currentObsState t)) -- @realizes \(\mathcal F_t^-\)(action given full history)

-- @node: ass:stationary-start
/-- The trajectory starts in the behavior stationary law. -/
def StationaryStart {T : Nat} (M : RawPomdpExperiment T 2 2) : Prop :=
  IsStationary (policyKernel M M.b) (stationaryLaw (policyKernel M M.b)) ∧ -- @realizes \(d_p\)(behavior stationary law)
  ∀ s, (M.law.map (stateAt (T := T) (nX := 2) (nH := 2) 0)) {s} =
    ENNReal.ofReal (stationaryLaw (policyKernel M M.b) s) -- @realizes \(S_t\)(stationary initial state)

-- @node: ass:policy-overlap
/-- The target policy is a probability policy dominated by `L` times behavior. -/
def PolicyOverlap {T : Nat} (L : ℝ) (M : RawPomdpExperiment T 2 2) : Prop :=
  PolicyVector M.e ∧ -- @realizes \(e\)(target policy simplex)
  ∀ x a, M.e x a ≤ L * M.b x a -- @realizes \(L\)(domination factor) @realizes \(e\)(dominated target policy)

-- @node: ass:behavior-contraction
/-- Behavior-induced joint-state kernel contracts probability vectors. -/
def BehaviorContraction {T : Nat} (alpha : ℝ)
    (M : RawPomdpExperiment T 2 2) : Prop :=
  Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.ContractsL1
    (policyKernel M M.b) alpha
  -- @realizes \(P_p\)(behavior transition) @realizes \(\alpha\)(behavior contraction)

-- @node: ass:target-contraction
/-- Target-induced joint-state kernel contracts probability vectors. -/
def TargetContraction {T : Nat} (alpha : ℝ)
    (M : RawPomdpExperiment T 2 2) : Prop :=
  Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.ContractsL1
    (policyKernel M M.e) alpha
  -- @realizes \(P_p\)(target transition) @realizes \(\alpha\)(target contraction)

-- @node: def:binary-pomdp-class
/-- The six-condition binary observed/hidden POMDP class. -/
structure BinaryPomdpClass (t0 zeta : ℝ) {T : Nat}
    (M : BinaryPomdpExperiment T) : Prop where
    -- @realizes \(\mathcal X\)(Fin 2 observed alphabet) @realizes \(\mathcal H\)(Fin 2 hidden alphabet)
    -- @realizes \(X_t\)(binary observed coordinate) @realizes \(H_t\)(binary hidden coordinate)
  t0_pos : 0 < t0 -- @realizes \(t_0\)(positive scale)
  zeta_nonneg : 0 ≤ zeta -- @realizes \(\zeta\)(nonnegative log overlap)
  pomdp_kernel : PomdpKernelLaw M -- @realizes \(K\)(kernel condition)
  sequential_ignorability : SequentialIgnorability M -- @realizes \(b\)(action law)
  stationary_start : StationaryStart M -- @realizes \(d_p\)(stationary start)
  policy_overlap : PolicyOverlap (policyFactor zeta) M -- @realizes \(e\)(target overlap)
  behavior_contraction : BehaviorContraction (mixingAlpha t0) M -- @realizes \(P_p\)(behavior mixing)
  target_contraction : TargetContraction (mixingAlpha t0) M -- @realizes \(\mathcal M_T^{(2)}(t_0,\zeta)\)(six law conditions)

-- @node: def:target-value
/-- Stationary target-policy expected reward. -/
noncomputable def targetValue {T : Nat} (M : RawPomdpExperiment T 2 2) : ℝ :=
  ∑ s, stationaryLaw (policyKernel M M.e) s * rewardRegression M s
  -- @realizes \(\theta\)(d_e r_e) @realizes \(r_e\)(target reward regression)

/-- The likelihood ratio with zero-cell convention. -/
noncomputable def ratio (b e : Policy 2) (x : Fin 2) (a : Bool) : ℝ :=
  if b x a = 0 then 0 else e x a / b x a
  -- @realizes \(\rho_t\)(action ratio, zero at zero behavior cells)

/-- The score at zero-based epoch `t`; valid in statements when `k ≤ t.val`. -/
noncomputable def score {T : Nat} (k : Nat) (b e : Policy 2)
    (w : ObsView T 2) (t : Fin T) : ℝ :=
  (w t).2.2 * ∏ j ∈ Finset.univ.filter
    (fun j : Fin T ↦ j.val ≤ t.val ∧ t.val - j.val ≤ k),
    ratio b e (w j).1 (w j).2.1
  -- @realizes \(Z_t(k)\)(k+1 ratios through current action)

/-- Population score expectation at a specified eligible epoch. -/
noncomputable def populationMoment {T : Nat} (M : RawPomdpExperiment T 2 2)
    (k : Nat) (t : Fin T) : ℝ :=
  ∫ tau, score k M.b M.e (obsProj tau) t ∂M.law
  -- @realizes \(m_k\)(stationary population intervention moment)

-- @node: def:observable-moments
/-- Seven empirical intervention moments use epochs 7 through `T`. -/
noncomputable def empiricalMoment {T : Nat} (k : Nat) (b e : Policy 2)
    (w : ObsView T 2) : ℝ :=
  (((T - 6 : Nat) : ℝ)⁻¹) *
    ∑ t ∈ Finset.univ.filter (fun t : Fin T ↦ 6 ≤ t.val), score k b e w t
  -- @realizes \(\widehat m_k\)(average over epochs 7 through T)

/-- A four-state matrix. -/
abbrev FourMatrix := Matrix (JointState 2 2) (JointState 2 2) ℝ

/-- Finite Dobrushin coefficient: maximal row total-variation distance. -/
noncomputable def dobrushin (P : FourMatrix) : ℝ :=
  ⨆ i : JointState 2 2, ⨆ j : JointState 2 2,
    (1 / 2 : ℝ) * ∑ s, |P i s - P j s|

/-- Transient characteristic factor, dividing by the stationary root. -/
noncomputable def transientPoly (P : FourMatrix) : Polynomial ℝ :=
  Matrix.charpoly P /ₘ (Polynomial.X - Polynomial.C 1)
  -- @realizes \(q_P\)(charpoly/(z-1)) @realizes \(q_{P'}\)(same construction on P')

/-- Product of two transient characteristic factors. -/
noncomputable def pairPoly (P P' : FourMatrix) : Polynomial ℝ :=
  transientPoly P * transientPoly P'
  -- @realizes \(Q_{P,P'}\)(product polynomial)

/-- Seven-moment modulus factor. -/
noncomputable def stabilityFactor (alpha : ℝ) : ℝ :=
  ((1 + alpha) / (1 - alpha)) ^ (6 : Nat)
  -- @realizes \(B_\alpha\)(seven-moment stability constant)

/-- Variance constant for the seven scores. -/
noncomputable def varianceFactor (alpha L : ℝ) : ℝ :=
  13 * L ^ (7 : Nat) + 2 / (1 - alpha)
  -- @realizes \(V_{\alpha,L}\)(variance constant)

-- @env: S2
variable (P P' : FourMatrix) (nu nu' pi pi' r r' : JointState 2 2 → ℝ)
  -- @realizes \(P\)(four-state stochastic matrix) @realizes \(P'\)(second matrix)
  -- @realizes \(\nu\)(initial law) @realizes \(\nu'\)(second initial law)
  -- @realizes \(r\)(reward vector) @realizes \(r'\)(second reward vector)
  -- @realizes \(\pi\)(stationary law) @realizes \(\pi'\)(second stationary law)

/-- The overlap radius in the cardinality-uniform comparator. -/
noncomputable def overlapRadius (C : ℝ) : ℝ := (C - 1) / C
  -- @realizes \(q_C\)((C-1)/C)

/-- The exponent in the cardinality-uniform comparator. -/
noncomputable def rateExponent (t0 zeta : ℝ) : ℝ := 2 / (2 + t0 * zeta)
  -- @realizes \(\beta\)(2/(2+t0*zeta))

-- @env: S4
variable (C : ℝ) (Q : Nat → Nat)
  -- @realizes \(C\)(stationary-overlap bound; C>1 in gate)
  -- @realizes \(Q\)(reset-depth sequence)

/-- Hidden alphabet used by the comparator reset construction at depth `Q T`. -/
abbrev ComparatorHiddenAlphabet (Q : Nat → Nat) (T : Nat) :=
  Fin (2 * (Q T + 1))
  -- @realizes \(Q\)(hidden alphabet of size 2(Q_T+1))

/-- The cited reset-depth family at the same logarithmic depth witnesses the
fixed-radius two-point lower bound. -/
def ComparatorResetLowerWitness (t0 zeta C cReset : ℝ) (Q : Nat → Nat)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) : Prop :=
  ∀ᶠ T : Nat in Filter.atTop,
    ∃ (hT : 1 ≤ T) (hQ : 1 ≤ Q T),
      let M0 := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthModel
        T (Q T) t0 zeta C false hT ht0 hzeta hC hQ
      let M1 := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthModel
        T (Q T) t0 zeta C true hT ht0 hzeta hC hQ
      M0.nH = 2 * (Q T + 1) ∧
      M1.nH = 2 * (Q T + 1) ∧
      ∀ est : CausalSmith.Stat.PomdpLatentOverlapMinimax.ObservableEstimator T,
        cReset * (T : ℝ) ^
          (-CausalSmith.Stat.PomdpLatentOverlapMinimax.rateExponent t0 zeta) ≤
          max
            (CausalSmith.Stat.PomdpLatentOverlapMinimax.observedRisk est M0)
            (CausalSmith.Stat.PomdpLatentOverlapMinimax.observedRisk est M1)

/-- The cited cardinality-uniform comparator. CausalSmith (2026),
*Latent Stationary Overlap and Minimax Off-Policy Evaluation in Finite POMDPs*,
main minimax theorem and reset-chain lower-bound construction,
handle `CausalSmithLatentOverlap2026`. This is a cited input. -/
-- @node: lem:cardinality-uniform-comparator
def CardinalityUniformComparator (t0 zeta : ℝ)
    (C : { c : ℝ // 1 < c }) : Sort 0 :=
  ∀ (ht0 : 0 < t0) (hzeta : 0 < zeta),
  ∃ c1 c2 cReset : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < cReset ∧
    (∀ᶠ T : Nat in Filter.atTop,
      c1 * ((T : ℝ)⁻¹ + (T : ℝ) ^ (-(rateExponent t0 zeta)) *
        overlapRadius C.val ^ (2 * (1 - rateExponent t0 zeta))) ≤
          CausalSmith.Stat.PomdpLatentOverlapMinimax.minimaxRisk T t0 zeta C.val ∧
      CausalSmith.Stat.PomdpLatentOverlapMinimax.minimaxRisk T t0 zeta C.val ≤
        c2 * ((T : ℝ)⁻¹ + (T : ℝ) ^ (-(rateExponent t0 zeta)) *
          overlapRadius C.val ^ (2 * (1 - rateExponent t0 zeta)))) ∧
  ∃ Q : Nat → Nat,
    (∃ a1 a2 : ℝ, 0 < a1 ∧ 0 < a2 ∧
      ∀ᶠ T : Nat in Filter.atTop,
        a1 * Real.log T ≤ Q T ∧ Q T ≤ a2 * Real.log T) ∧
    ComparatorResetLowerWitness t0 zeta C.val cReset Q ht0 hzeta C.property
  -- @realizes \(C\)(strict stationary-overlap bound in comparator class) @realizes \(Q\)(existing logarithmic-depth signed reset lower family)

/-- The handle is the problem of constructing a cost-certified algorithm in an explicit
arithmetic or bit-complexity and precision model. Start from the 3×3 Hankel matrix of
m̂_(i+j+1)−m̂_(i+j); adapt over recurrence ranks 0–3; constrain transient roots to
|z|≤α; return a stable four-state scalar realization with globally certified
seven-moment objective gap at most T⁻¹, uniformly on rank-deficient strata and
without a positive singular-value margin. The exhaustive grid has a finite
candidate list of size O(T^19) for fixed t0, but no runtime or arithmetic-operation
bound for fitting and selection is asserted. -/
-- @node: def:polynomial-time-handle
def polynomialTimeHandle : _root_.String :=
  "The handle is the problem of constructing, in an explicit arithmetic or bit-complexity and precision model, a cost-certified algorithm that starts from the 3x3 Hankel matrix of differences mhat_(i+j+1)-mhat_(i+j), adapts over recurrence ranks zero through three, enforces transient roots in |z| <= alpha, and returns a stable four-state scalar realization whose seven-moment objective is globally certified within T^-1 of the optimum, uniformly over rank-deficient strata and without a positive singular-value margin. The exhaustive estimator is defined over a finite candidate list of size O(T^19) for fixed t0, but no runtime or arithmetic-operation bound for fitting and selection is asserted."
  -- @realizes \(\mathfrak H_{\mathrm{poly}}\)(nonassertive research handle)

/-- The frozen open question, recorded as a nonassertive string. -/
-- @node: oeq:polynomial-time-attainment
def polynomialTimeAttainmentQuestion : _root_.String :=
  "Can the handle H_poly implement fitting and lexicographic selection over, or replace, the O(T^19)-sized stable-grid candidate list by a rank-adaptive algorithm with explicit runtime, bit-complexity, and precision semantics that returns over M_T^(2)(t0,zeta) a globally certified seven-moment stable fit within objective gap T^-1, uniformly over every rank-deficient Hankel stratum and without a positive singular-value margin?"

end CausalSmith.Stat.PomdpBinaryhiddenRate
