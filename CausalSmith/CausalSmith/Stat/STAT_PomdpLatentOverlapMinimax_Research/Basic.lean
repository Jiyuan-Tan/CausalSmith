module
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Minimax.MinimaxRisk
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.style.longLine false

/-!
# Latent-overlap POMDP minimax model

The paper-local carrier for a finite partially observed Markov decision process,
its observable-data decision problem, and the partial-history importance-weighted
estimators.  Causalean's generic real-valued minimax API is reused, while the
dependent-trajectory model is defined locally because the substrate contains no
POMDP experiment at this abstraction level.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- A memoryless policy on the finite observed-state alphabet. -/
abbrev Policy (nX : Nat) := Fin nX → Bool → ℝ
  -- @realizes \(\mathcal X\)(Fin nX) @realizes \(\mathcal A\)(Bool)

/-- The finite observed/latent joint-state alphabet. -/
abbrev JointState (nX nH : Nat) := Fin nX × Fin nH
  -- @realizes \(\mathcal X\)(first coordinate) @realizes \(\mathcal H\)(second coordinate) @realizes \(\mathcal S\)(product alphabet)

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
  K : JointState nX nH → Bool → Measure (Step nX nH)
    -- @realizes \(K\)(law of reward and successor state)
  b : Policy nX -- @realizes \(b\)(behavior policy carrier)
  e : Policy nX -- @realizes \(e\)(target policy carrier)
  /-- Auxiliary initialization vector used only by finite witness constructors.
  Model-class membership is deliberately independent of this field. -/
  init : JointState nX nH → ℝ
  law : Measure (FullTrajectory T nX nH)
    -- @realizes \(X_t\)(observed coordinate of state path) @realizes \(H_t\)(latent coordinate of state path)
  law_isProbability : IsProbabilityMeasure law

/-- For [the M input](hyp:M), [this supplies the inst Is Probability Measure Full Trajectory Law instance](goal). -/
instance {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) :
    IsProbabilityMeasure M.law := M.law_isProbability

-- @env: S1
variable (T : Nat) (t0 zeta C : ℝ) (nX nH : Nat)
  -- @realizes \(T\)(trajectory length) @realizes \(t_0\)(real carrier; positivity in LatentOverlapClass) @realizes \(\zeta\)(real carrier; positivity in LatentOverlapClass) @realizes \(C\)(real carrier; lower bound in LatentStationaryOverlap)
variable (M : RawPomdpExperiment T nX nH)

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
  exact (measurable_snd.comp measurable_fst).prodMk measurable_snd

/-- [the measurable current Obs State assertion holds](goal). -/
lemma measurable_currentObsState {T nX nH : Nat} (t : Fin T) :
    Measurable (currentObsState (nX := nX) (nH := nH) t) := by
  exact measurable_fst.comp measurable_snd

/-- A finite vector is a probability vector. -/
def ProbabilityVector {S : Type*} [Fintype S] (p : S → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

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
  ProbabilityVector d ∧ ∀ s', ∑ s, d s * P s s' = d s'

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
  -- @realizes \(g_e\)(target-policy reward regression)

/-- The derived contraction factor. -/
noncomputable def mixingAlpha (t0 : ℝ) : ℝ := Real.exp (-(1 / t0))
  -- @realizes \(\alpha\)(exp(-1/t0))

/-- The derived policy-overlap factor. -/
noncomputable def policyFactor (zeta : ℝ) : ℝ := Real.exp zeta
  -- @realizes \(L\)(exp(zeta))

-- @node: ass:pomdp-kernel
/-- Every reward-transition law is probabilistic and every epoch factors through the same kernel. -/
def PomdpKernelLaw {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) : Prop :=
  (∀ s a, IsProbabilityMeasure (M.K s a)) ∧
  ∀ t : Fin T,
      M.law.map (histNextPair t) =
      (M.law.map (histView t)).compProd
        (Kernel.comap (kernelOfK M)
          (currentStateAction t) (measurable_currentStateAction t))

-- @node: ass:sequential-ignorability
/-- Conditional on the observed current state, each action is drawn from the behavior policy. -/
def SequentialIgnorability {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) : Prop :=
  PolicyVector M.b ∧
  ∀ t : Fin T,
      M.law.map (histActionPair t) =
      (M.law.map (histStateView t)).compProd
        (Kernel.comap (behaviourKernel M)
          (currentObsState t) (measurable_currentObsState t))

-- @node: ass:stationary-start
/-- The first-state marginal is the derived behavior stationary law.
This predicate is independent of the auxiliary `RawPomdpExperiment.init` field. -/
def StationaryStart {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) : Prop :=
  IsStationary (policyKernel M M.b) (stationaryLaw (policyKernel M M.b)) ∧
  ∀ s, (M.law.map (stateAt (T := T) (nX := nX) (nH := nH) 0)) {s} =
    ENNReal.ofReal (stationaryLaw (policyKernel M M.b) s)
  -- @realizes \(d_p\)(behavior stationary law initializes S_1)

-- @node: ass:bounded-reward
/-- At every observed epoch, the trajectory reward lies in `[-1,1]` almost surely.
This deliberately imposes no condition on kernel rows that the trajectory law never visits. -/
def BoundedReward {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) : Prop :=
  ∀ t : Fin T, M.law {tau | |rewardAt t tau| ≤ 1} = 1
  -- @realizes \(Y_t\)(trajectory-law almost-sure bound in [-1,1])

-- @node: ass:policy-overlap
/-- The target policy is a probability policy dominated by `L` times the behavior policy. -/
def PolicyOverlap {T nX nH : Nat} (L : ℝ) (M : RawPomdpExperiment T nX nH) : Prop :=
  PolicyVector M.e ∧ ∀ x a, M.e x a ≤ L * M.b x a
  -- @realizes \(e\)(probability policy) @realizes \(b\)(dominating policy) @realizes \(L\)(ratio bound)

-- @node: ass:uniform-contraction
/-- Both policy-induced kernels contract total variation by the common factor `alpha`. -/
def UniformContraction {T nX nH : Nat} (alpha : ℝ)
    (M : RawPomdpExperiment T nX nH) : Prop :=
  ∀ p, (p = M.b ∨ p = M.e) →
    ∀ nu nu', ProbabilityVector nu → ProbabilityVector nu' →
      tvNorm (applyKernel nu (policyKernel M p) - applyKernel nu' (policyKernel M p)) ≤
        alpha * tvNorm (nu - nu')
  -- @realizes \(\alpha\)(uniform TV contraction factor) @realizes \(P_p\)(both policy kernels)

-- @node: ass:latent-stationary-overlap
/-- The target stationary law is pointwise dominated by `C` times the behavior stationary law. -/
def LatentStationaryOverlap {T nX nH : Nat} (C : ℝ)
    (M : RawPomdpExperiment T nX nH) : Prop :=
  1 ≤ C ∧ -- @realizes \(C\)(radius lies in [1,∞))
  ∀ s, stationaryLaw (policyKernel M M.e) s ≤
    C * stationaryLaw (policyKernel M M.b) s
  -- @realizes \(C\)(stationary density-ratio bound) @realizes \(d_p\)(target versus behavior stationary laws)

-- @node: def:model-class
/-- The paper's seven-restriction latent-overlap POMDP model class. -/
structure LatentOverlapClass (t0 zeta C : ℝ) {T nX nH : Nat}
    (M : RawPomdpExperiment T nX nH) : Prop where
  t0_pos : 0 < t0 -- @realizes \(t_0\)(positive mixing scale)
  zeta_pos : 0 < zeta -- @realizes \(\zeta\)(positive log-overlap scale)
  pomdp_kernel : PomdpKernelLaw M
  sequential_ignorability : SequentialIgnorability M
  stationary_start : StationaryStart M
  bounded_reward : BoundedReward M
  policy_overlap : PolicyOverlap (policyFactor zeta) M
  uniform_contraction : UniformContraction (mixingAlpha t0) M
  latent_stationary_overlap : LatentStationaryOverlap C M
    -- @realizes \(\mathcal M_T(t_0,\zeta,C)\)(seven-predicate model class)

/-- The behavior stationary law is selected from the witness supplied by the stationary start. [the h M condition](hyp:hM). [the stated conclusion](goal). -/
lemma LatentOverlapClass.behavior_stationary_law {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M) :
    IsStationary (policyKernel M M.b) (stationaryLaw (policyKernel M M.b)) := by
  exact hM.stationary_start.1

-- @node: def:target-value
/-- The stationary target-policy mean reward. -/
noncomputable def targetValue {T nX nH : Nat} (M : RawPomdpExperiment T nX nH) : ℝ :=
  ∑ s, stationaryLaw (policyKernel M M.e) s * rewardRegression M s
  -- @realizes \(\theta(K,e)\)(stationary target value)

/-- The observable one-step target-to-behavior likelihood ratio, totalized at zero cells. -/
noncomputable def ratio {nX : Nat} (b e : Policy nX) (x : Fin nX) (a : Bool) : ℝ :=
  if b x a = 0 then 0 else e x a / b x a
  -- @realizes \(\rho_t\)(policy ratio with zero-cell convention)

/-- Projection to the closed unit interval. -/
noncomputable def clipUnit (u : ℝ) : ℝ := max (-1) (min 1 u)

/-- One partial-history weighted reward. -/
noncomputable def phiwScore {T nX : Nat} (k : Nat) (b e : Policy nX)
    (w : ObsView T nX) (t : Fin T) : ℝ :=
  (w t).2.2 * ∏ j ∈ Finset.univ.filter
      (fun j : Fin T ↦ j.val ≤ t.val ∧ t.val - j.val ≤ k),
    ratio b e (w j).1 (w j).2.1
  -- @realizes \(Z_t(k)\)(reward times chronological ratio product)

/-- The unclipped partial-history average. -/
noncomputable def phiwRaw {T nX : Nat} (k : Nat) (b e : Policy nX)
    (w : ObsView T nX) : ℝ :=
  (((T - k : Nat) : ℝ)⁻¹) *
    ∑ t ∈ Finset.univ.filter (fun t : Fin T ↦ k ≤ t.val), phiwScore k b e w t

-- @node: def:phiw-estimator
/-- The clipped partial-history importance-weighted estimator. -/
noncomputable def phiwEstimator {T nX : Nat} (k : Nat) (_hk : k < T) (b e : Policy nX) :
    ObsView T nX → ℝ :=
  fun w ↦ clipUnit (phiwRaw k b e w)
  -- @realizes \(\widehat\theta_k\)(clipped PHIW estimator)

/-- Raw observable-data estimators, receiving only the revealed alphabet and policies. -/
abbrev RawEstimator (T : Nat) :=
  (nX : Nat) → Policy nX → Policy nX → ObsView T nX → ℝ

/-- Measurable observable-data estimators taking values in `[-1,1]`. -/
def ObservableEstimator (T : Nat) : Type :=
  {est : RawEstimator T //
    (∀ nX b e w, est nX b e w ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ nX b e, Measurable (est nX b e))}

/-- The PHIW estimator as an admissible observable estimator. Outside its stated
domain `k < T`, this convenience wrapper returns the constant-zero estimator. -/
noncomputable def phiwObservable (k : Nat) : ObservableEstimator T :=
  if hk : k < T then
  ⟨fun nX b e w ↦ phiwEstimator k hk b e w, by
    constructor
    · intro nX b e w
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    · intro nX b e
      have hratio (j : Fin T) : Measurable fun w : ObsView T nX ↦
          ratio b e (w j).1 (w j).2.1 := by
        have hcoord : Measurable fun w : ObsView T nX ↦ ((w j).1, (w j).2.1) := by
          measurability
        have hb : Measurable fun w : ObsView T nX ↦ b (w j).1 (w j).2.1 :=
          (measurable_of_countable fun xa : Fin nX × Bool ↦ b xa.1 xa.2).comp hcoord
        have he : Measurable fun w : ObsView T nX ↦ e (w j).1 (w j).2.1 :=
          (measurable_of_countable fun xa : Fin nX × Bool ↦ e xa.1 xa.2).comp hcoord
        rw [show (fun w : ObsView T nX ↦ ratio b e (w j).1 (w j).2.1) =
            fun w ↦ if b (w j).1 (w j).2.1 = 0 then 0
              else e (w j).1 (w j).2.1 / b (w j).1 (w j).2.1 by
          funext w
          rfl]
        exact Measurable.ite (measurableSet_eq_fun hb measurable_const)
          measurable_const (he.div hb)
      unfold phiwEstimator clipUnit phiwRaw phiwScore
      measurability⟩
  else
  ⟨fun _ _ _ _ ↦ 0, by
    constructor
    · intro nX b e w
      constructor <;> norm_num
    · intro nX b e
      exact measurable_const⟩

/-- For [`T`](hyp:T) and parameters [`t0`](hyp:t0), [`zeta`](hyp:zeta), and [`C`](hyp:C),
the [model index](goal) ranges over unrestricted finite observed and latent cardinalities
and carries the [positive-horizon condition](hyp:horizon_pos). -/
structure ModelIndex (T : Nat) (t0 zeta C : ℝ) where
  horizon_pos : 1 ≤ T -- @realizes \(T\)(positive trajectory horizon)
  nX : Nat -- @realizes \(\mathcal X\)(unrestricted finite observed alphabet)
  nH : Nat -- @realizes \(\mathcal H\)(unrestricted finite latent alphabet)
  raw : RawPomdpExperiment T nX nH
  mem : LatentOverlapClass t0 zeta C raw
    -- @realizes \(\mathcal M_T(t_0,\zeta,C)\)(cardinality-uniform membership)

/-- Squared risk of a raw estimator at one model. -/
noncomputable def rawObservedRisk {T : Nat} {t0 zeta C : ℝ}
    (est : RawEstimator T) (m : ModelIndex T t0 zeta C) : ℝ :=
  Causalean.Stat.sqRisk (obsLaw m.raw) (est m.nX m.raw.b m.raw.e) (targetValue m.raw)

/-- Squared risk on the bounded measurable estimator carrier. -/
noncomputable def observedRisk {T : Nat} {t0 zeta C : ℝ}
    (est : ObservableEstimator T) (m : ModelIndex T t0 zeta C) : ℝ :=
  rawObservedRisk est.1 m

-- @env: S2
variable (est : ObservableEstimator T)

-- @node: def:minimax-risk
/-- The cardinality-uniform observable-data minimax mean-squared error. -/
noncomputable def minimaxRisk : ℝ :=
  Causalean.Stat.minimaxValueReal (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
  -- @realizes \(R_T(t_0,\zeta,C)\)(bounded-carrier minimax squared risk)

/-- The hidden-state minimax exponent. -/
noncomputable def rateExponent (t0 zeta : ℝ) : ℝ := 2 / (2 + t0 * zeta)
  -- @realizes \(\beta\)(2/(2+t0*zeta))

-- @node: def:history-depth
/-- The mixing/overlap-balanced fixed-radius history depth. -/
noncomputable def historyDepth (T : Nat) (t0 zeta : ℝ) : Nat :=
  min (T / 2) (Int.toNat ⌊Real.log T /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)
  -- @realizes \(k_T\)(balanced integer history depth)

-- @node: def:overlap-distance-radius
/-- The normalized latent stationary-overlap radius. -/
noncomputable def overlapRadius (C : ℝ) : ℝ := (C - 1) / C
  -- @realizes \(q_C\)((C-1)/C)

-- @node: def:radius-adaptive-history-depth
/-- The radius-adaptive history depth, with an immediate-weighting branch at the elbow. -/
noncomputable def radiusAdaptiveDepth (T : Nat) (t0 zeta C : ℝ) : Nat :=
  if (T : ℝ) * overlapRadius C ^ 2 ≤ 1 then 0
  else min (T / 2) (Int.toNat ⌊Real.log ((T : ℝ) * overlapRadius C ^ 2) /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)
  -- @realizes \(\kappa_T^{\mathrm{rad}}(C)\)(two-branch radius-adaptive depth)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
