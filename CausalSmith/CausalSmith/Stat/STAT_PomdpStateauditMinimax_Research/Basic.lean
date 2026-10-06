module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepth
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Minimax.MinimaxRisk
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite POMDPs with independent state audits

This module gives the arbitrary finite action world, the audited observation law,
model classes, estimators, lower-bound constructions and minimax risks for the
state-audit paper. The `Fin` alphabets range over all finite cardinalities.
The controlled process keeps the joint reward--next-state kernel intact.
-/

@[expose] public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

-- @env: S1
variable (T : Nat) (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta)
  (nX nH k : Nat)
  -- @realizes \(T\)(trajectory length) @realizes \(t_0\)(positive binder ht0) @realizes \(\zeta\)(positive binder hzeta) @realizes \(C\)(fixed overlap radius)

abbrev JointState (nX nH : Nat) := Fin nX × Fin nH
  -- @realizes \(\mathcal X\)(observed Fin nX) @realizes \(\mathcal H\)(latent Fin nH) @realizes \(\mathcal S\)(product)
abbrev Policy (nX k : Nat) := Fin nX → Fin k → ℝ
  -- @realizes \(\mathcal A\)(arbitrary finite Fin k)
abbrev FullPath (T nX nH k : Nat) :=
  (Fin (T + 1) → JointState nX nH) × (Fin T → Fin k × ℝ)
  -- @realizes \(S_t\)(complete state path) @realizes \(A_t\)(action path) @realizes \(Y_t\)(real reward path)
abbrev ObsPath (T nX k : Nat) := Fin T → Fin nX × Fin k × ℝ

structure PomdpModel (T nX nH k : Nat) where
  K : JointState nX nH → Fin k → Measure (ℝ × JointState nX nH)
    -- @realizes \(K\)(joint reward--next-state kernel)
  b : Policy nX k -- @realizes \(b\)(known behavior policy)
  e : Policy nX k -- @realizes \(e\)(known target policy)
  law : Measure (FullPath T nX nH k) -- @realizes \(\mathbb P_b\)(full behavior trajectory law)
  law_prob : IsProbabilityMeasure law

instance {T nX nH k : Nat} (M : PomdpModel T nX nH k) :
    IsProbabilityMeasure M.law := M.law_prob

-- @env: S2
variable (eta : ℝ) (M : PomdpModel T nX nH k)
  -- @realizes \(\eta\)(audit probability in [0,1])

def stateAt {T nX nH k : Nat} (w : FullPath T nX nH k) (t : Fin (T + 1)) := w.1 t
  -- @realizes \(S_t\)(complete state) @realizes \(X_t\)(first projection) @realizes \(H_t\)(second projection)
def currentState {T nX nH k : Nat} (w : FullPath T nX nH k) (t : Fin T) := w.1 t.castSucc
def nextState {T nX nH k : Nat} (w : FullPath T nX nH k) (t : Fin T) := w.1 t.succ
def actionAt {T nX nH k : Nat} (w : FullPath T nX nH k) (t : Fin T) := (w.2 t).1
  -- @realizes \(A_t\)(finite action)
def rewardAt {T nX nH k : Nat} (w : FullPath T nX nH k) (t : Fin T) := (w.2 t).2
  -- @realizes \(Y_t\)(real reward)
def obsProj {T nX nH k : Nat} (w : FullPath T nX nH k) : ObsPath T nX k :=
  fun t => ((currentState w t).1, actionAt w t, rewardAt w t)
noncomputable def obsLaw {T nX nH k : Nat} (M : PomdpModel T nX nH k) :
    Measure (ObsPath T nX k) := M.law.map obsProj
  -- @realizes \(\mathbb P_M^{\mathrm{obs},T}\)(observed-path pushforward)

abbrev PreHistory (T nX nH k : Nat) (t : Fin T) :=
  (Fin t.val → JointState nX nH) × (Fin t.val → Fin k × ℝ) × JointState nX nH
  -- @realizes \(\mathcal F_t^-\)(complete pre-action history)
abbrev PostHistory (T nX nH k : Nat) (t : Fin T) := PreHistory T nX nH k t × Fin k
  -- @realizes \(\mathcal F_t^+\)(complete post-action history)
abbrev ObsHistory (T nX k : Nat) (t : Fin T) :=
  (Fin t.val → Fin nX) × (Fin t.val → Fin k × ℝ) × Fin nX
  -- @realizes \(\mathcal G_t^-\)(observed pre-action history)

def pastIndex {T : Nat} (t : Fin T) (j : Fin t.val) : Fin T := ⟨j.val, lt_trans j.isLt t.isLt⟩
def preHist {T nX nH k : Nat} (t : Fin T) (w : FullPath T nX nH k) :
    PreHistory T nX nH k t :=
  (fun j => currentState w (pastIndex t j), fun j => w.2 (pastIndex t j), currentState w t)
def postHist {T nX nH k : Nat} (t : Fin T) (w : FullPath T nX nH k) :
    PostHistory T nX nH k t := (preHist t w, actionAt w t)
def obsHist {T nX nH k : Nat} (t : Fin T) (w : FullPath T nX nH k) :
    ObsHistory T nX k t :=
  (fun j => (currentState w (pastIndex t j)).1,
    fun j => w.2 (pastIndex t j), (currentState w t).1)

noncomputable def kernelOfK {T nX nH k : Nat} (M : PomdpModel T nX nH k) :
    Kernel (JointState nX nH × Fin k) (ℝ × JointState nX nH) :=
  Kernel.ofFunOfCountable (fun sa => M.K sa.1 sa.2)
noncomputable def actionKernel {T nX nH k : Nat} (M : PomdpModel T nX nH k) :
    Kernel (Fin nX) (Fin k) :=
  Kernel.ofFunOfCountable (fun x => ∑ a : Fin k, ENNReal.ofReal (M.b x a) • Measure.dirac a)

/-- A finite probability vector. -/
def ProbabilityVector {S : Type*} [Fintype S] (p : S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1
/-- A memoryless probability policy. -/
def PolicyVector {nX k : Nat} (p : Policy nX k) : Prop :=
  ∀ x, ProbabilityVector (p x)

noncomputable def policyKernel {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (p : Policy nX k) (s s' : JointState nX nH) : ℝ :=
  ∑ a : Fin k, p s.1 a * (M.K s a {q | q.2 = s'}).toReal
  -- @realizes \(P_p\)(policy-induced state transition)
def IsStationary {S : Type*} [Fintype S] (P : S → S → ℝ) (d : S → ℝ) : Prop :=
  ProbabilityVector d ∧ ∀ s', ∑ s, d s * P s s' = d s'
noncomputable def stationaryLaw {S : Type*} [Fintype S] (P : S → S → ℝ) : S → ℝ :=
  Classical.epsilon (IsStationary P)
  -- @realizes \(d_p\)(stationary probability vector, under existence and uniqueness)
noncomputable def applyKernel {S : Type*} [Fintype S] (d : S → ℝ) (P : S → S → ℝ) : S → ℝ :=
  fun s' => ∑ s, d s * P s s'
noncomputable def tvNorm {S : Type*} [Fintype S] (d : S → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, |d s|
noncomputable def rewardRegression {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (s : JointState nX nH) : ℝ :=
  ∑ a : Fin k, M.e s.1 a * ∫ q, q.1 ∂(M.K s a)
  -- @realizes \(g_e\)(target conditional reward mean)
noncomputable def mixingAlpha (t0 : ℝ) : ℝ := Real.exp (-(1 / t0))
  -- @realizes \(\alpha\)(exp(-1/t0))
noncomputable def policyFactor (zeta : ℝ) : ℝ := Real.exp zeta
  -- @realizes \(L\)(exp(zeta))
noncomputable def rateExponent (t0 zeta : ℝ) : ℝ := 2 / (2 + t0 * zeta)
  -- @realizes \(\beta\)(2/(2+t0*zeta))

-- @node: ass:full-filtration-pomdp
/-- The reward and next state have kernel `K` conditional on the full post-action history. -/
def FullFiltrationPomdp {T nX nH k : Nat} (M : PomdpModel T nX nH k) : Prop :=
  (∀ s a, IsProbabilityMeasure (M.K s a)) ∧
  ∀ t : Fin T,
    M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t))) =
      (M.law.map (postHist t)).compProd
        (Kernel.comap (kernelOfK M)
          (fun h => (h.1.2.2, h.2)) (by fun_prop))

-- @node: ass:full-filtration-randomization
/-- The action given the complete pre-action history has the memoryless behavior policy. -/
def FullFiltrationRandomization {T nX nH k : Nat} (M : PomdpModel T nX nH k) : Prop :=
  PolicyVector M.b ∧ -- @realizes \(\rho_t\)(behavior policy nonnegative on each cell)
  ∀ t : Fin T,
    M.law.map (fun w => (preHist t w, actionAt w t)) =
      (M.law.map (preHist t)).compProd
        (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop))

-- @node: ass:bounded-reward
/-- Conditional first and second reward moments are bounded by one. -/
def RewardMomentEnvelope {T nX nH k : Nat} (M : PomdpModel T nX nH k) : Prop :=
  ∀ s a, Integrable (fun q : ℝ × JointState nX nH => q.1) (M.K s a) ∧
    Integrable (fun q : ℝ × JointState nX nH => q.1 ^ 2) (M.K s a) ∧
    |∫ q, q.1 ∂(M.K s a)| ≤ 1 ∧
    ∫ q, q.1 ^ 2 ∂(M.K s a) ≤ 1
  -- @realizes \(Y_t\)(conditional first/second moment envelope)

-- @node: ass:policy-overlap
/-- The target policy is dominated at every action by the behavior policy. -/
def PolicyOverlap {T nX nH k : Nat} (zeta : ℝ) (M : PomdpModel T nX nH k) : Prop :=
  PolicyVector M.e ∧ -- @realizes \(e\)(target probability vector) @realizes \(\rho_t\)(nonnegative numerator)
  ∀ x a, M.e x a ≤ policyFactor zeta * M.b x a -- @realizes \(L\)(policy factor) @realizes \(\rho_t\)(ratio bounded by L on behavior-supported cells)

-- @node: ass:uniform-contraction
/-- Both induced state kernels contract total variation. -/
def UniformContraction {T nX nH k : Nat} (t0 : ℝ) (M : PomdpModel T nX nH k) : Prop :=
  ∀ p, (p = M.b ∨ p = M.e) → ∀ d d', ProbabilityVector d → ProbabilityVector d' →
    tvNorm (applyKernel d (policyKernel M p) - applyKernel d' (policyKernel M p)) ≤
      mixingAlpha t0 * tvNorm (d - d')
  -- @realizes \(P_p\)(both induced kernels) @realizes \(\alpha\)(contraction factor)

-- @node: ass:stationary-start
/-- The initial state has the stationary behavior distribution. -/
def StationaryStart {T nX nH k : Nat} (M : PomdpModel T nX nH k) : Prop :=
  IsStationary (policyKernel M M.b) (stationaryLaw (policyKernel M M.b)) ∧
  ∀ s, (M.law.map (fun w => stateAt w 0)) {s} =
    ENNReal.ofReal (stationaryLaw (policyKernel M M.b) s)
  -- @realizes \(d_p\)(stationary behavior initialization)

-- @node: ass:stationary-overlap
/-- The fixed subclass bounds target stationary mass by behavior stationary mass. -/
def StationaryOverlap {T nX nH k : Nat} (C : ℝ) (M : PomdpModel T nX nH k) : Prop :=
  1 ≤ C ∧ -- @realizes \(C\)(radius in [1,∞))
  ∀ s, stationaryLaw (policyKernel M M.e) s ≤ C * stationaryLaw (policyKernel M M.b) s
  -- @realizes \(d_p\)(pointwise stationary overlap)

abbrev AuditMask (T : Nat) := Fin T → Bool
  -- @realizes \(R_t\)(Bernoulli audit indicators)
noncomputable def auditBitLaw (eta : ℝ) : Measure Bool :=
  ENNReal.ofReal eta • Measure.dirac true + ENNReal.ofReal (1 - eta) • Measure.dirac false
noncomputable def auditMaskLaw (T : Nat) (eta : ℝ) : Measure (AuditMask T) :=
  Measure.pi (fun _ => auditBitLaw eta)
noncomputable def auditJointLaw {T nX nH k : Nat} (eta : ℝ) (M : PomdpModel T nX nH k) :
    Measure (FullPath T nX nH k × AuditMask T) := M.law.prod (auditMaskLaw T eta)

-- @node: ass:bernoulli-audits
/-- The audit mask is an independent product of Bernoulli draws. -/
def BernoulliAudits {T nX nH k : Nat} (eta : ℝ) (M : PomdpModel T nX nH k)
    (joint : Measure (FullPath T nX nH k × AuditMask T)) : Prop :=
  eta ∈ Set.Icc (0 : ℝ) 1 ∧ joint = auditJointLaw eta M
  -- @realizes \(\eta\)(probability in [0,1]) @realizes \(R_t\)(independent Bernoulli mask)

instance (nX nH : Nat) : MeasurableSpace (Option (JointState nX nH)) := ⊤

abbrev AuditedRecord (T nX nH k : Nat) :=
  Fin T → Fin nX × Fin k × ℝ × Bool × Option (JointState nX nH)
  -- @realizes \(O_T^{\eta}\)(audited record with atomic complete-state labels)
def auditRecord {T nX nH k : Nat} (w : FullPath T nX nH k) (mask : AuditMask T) :
    AuditedRecord T nX nH k :=
  fun t => ((currentState w t).1, (actionAt w t, (rewardAt w t,
    (mask t, if mask t then some (currentState w t) else none))))
  -- @realizes \(O_T^{\eta}\)(raw state labels; estimator interface is permutation-invariant)

/-- Change only the names of complete-state labels. The observed state, action,
reward, and audit bit remain available to the estimator. -/
def relabelAudit {T nX nH k : Nat} (σ : Equiv.Perm (JointState nX nH))
    (w : AuditedRecord T nX nH k) : AuditedRecord T nX nH k :=
  fun t => ((w t).1, ((w t).2.1, ((w t).2.2.1,
    ((w t).2.2.2.1, Option.map σ (w t).2.2.2.2))))

/-- The equality-only repeated-label event used by the necessity test. -/
def RepeatedAuditLabel {T nX nH k : Nat} (w : AuditedRecord T nX nH k) : Prop :=
  ∃ t u : Fin T, t ≠ u ∧ (w t).2.2.2.1 = true ∧
    (w u).2.2.2.1 = true ∧
    (w t).2.2.2.2 = (w u).2.2.2.2 ∧
    (w t).2.2.2.2 ≠ none

-- @node: ass:atomic-audit-labels
/-- The bit and reported label match the audit; admissible readouts are invariant
under all permutations of the label alphabet. -/
def AtomicAuditLabels {T nX nH k : Nat} (record :
    FullPath T nX nH k → AuditMask T → AuditedRecord T nX nH k) : Prop :=
  (∀ w mask t,
    (record w mask t).2.2.2.1 = mask t ∧ -- @realizes \(R_t\)(reported bit equals audit mask)
    (record w mask t).2.2.2.2 =
      (if mask t then some (currentState w t) else none)) ∧ -- @realizes \(S_t\)(exact label when audited)
  (∀ (σ : Equiv.Perm (JointState nX nH)) w mask t,
    (relabelAudit σ (record w mask) t).2.2.2.2 =
      (if mask t then some (σ (currentState w t)) else none)) -- @realizes \(S_t\)(equivariant under atomic relabeling)

-- @node: def:audited-experiment
/-- The behavior path with an independent audit mask, pushed to audited records. -/
noncomputable def auditedLaw {T nX nH k : Nat} (eta : ℝ) (M : PomdpModel T nX nH k) :
    Measure (AuditedRecord T nX nH k) :=
  (auditJointLaw eta M).map (fun q => auditRecord q.1 q.2)
  -- @realizes \(O_T^{\eta}\)(audited observation law)

-- @node: def:model-class
/-- The Hu--Wager class has full-history assumptions and no stationary-overlap requirement. -/
structure HuWagerClass (t0 zeta : ℝ) {T nX nH k : Nat} (M : PomdpModel T nX nH k) : Prop where
  t0_pos : 0 < t0 -- @realizes \(t_0\)(positive mixing scale)
  zeta_pos : 0 < zeta -- @realizes \(\zeta\)(positive log overlap bound)
  pomdp : FullFiltrationPomdp M
  randomization : FullFiltrationRandomization M
  moment : RewardMomentEnvelope M
  overlap : PolicyOverlap zeta M
  contraction : UniformContraction t0 M
  start : StationaryStart M
  -- @realizes \(\mathfrak M_T^{\mathrm{HW}}(t_0,\zeta)\)(six-member headline class)

def FixedOverlapClass {T nX nH k : Nat} (t0 zeta C : ℝ) (M : PomdpModel T nX nH k) : Prop :=
  HuWagerClass t0 zeta M ∧ StationaryOverlap C M
  -- @realizes \(\mathfrak M_T(t_0,\zeta,C)\)(nested fixed-overlap subclass)

structure HWIndex (T : Nat) (t0 zeta : ℝ) where
  nX : Nat -- @realizes \(\mathcal X\)(unrestricted positive cardinality)
  nH : Nat -- @realizes \(\mathcal H\)(unrestricted positive cardinality)
  k : Nat -- @realizes \(\mathcal A\)(unrestricted positive cardinality)
  nX_pos : 1 ≤ nX
  nH_pos : 1 ≤ nH
  k_pos : 1 ≤ k
  raw : PomdpModel T nX nH k
  mem : HuWagerClass t0 zeta raw

-- @node: def:target-value
/-- The stationary target-policy mean reward. -/
noncomputable def targetValue {T nX nH k : Nat} (M : PomdpModel T nX nH k) : ℝ :=
  ∑ s, stationaryLaw (policyKernel M M.e) s * rewardRegression M s
  -- @realizes \(\theta(K,e)\)(stationary target-policy value)

-- @realizes \(\rho_t\)(policy ratio on supported cells and zero on joint-zero cells)
noncomputable def ratio {nX k : Nat} (b e : Policy nX k) (x : Fin nX) (a : Fin k) : ℝ :=
  if b x a = 0 then 0 else e x a / b x a
noncomputable def clipUnit (u : ℝ) : ℝ := max (-1) (min 1 u)
-- @realizes \(k_T\)(balanced PHIW history depth for positive T)
noncomputable def historyDepth (T : Nat) (t0 zeta : ℝ) : Nat :=
  min (T / 2) (Int.toNat ⌊Real.log T /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)
noncomputable def phiwScore {T nX nH k : Nat} (depth : Nat) (b e : Policy nX k)
    (w : AuditedRecord T nX nH k) (t : Fin T) : ℝ :=
  (w t).2.2.1 * ∏ j ∈ Finset.univ.filter
    (fun j : Fin T => j.val ≤ t.val ∧ t.val - j.val ≤ depth),
      ratio b e (w j).1 (w j).2.1

-- @node: def:phiw
/-- The partial-history estimator uses only observed state, action, and reward. -/
noncomputable def phiwEstimator {T nX nH k : Nat} (t0 zeta : ℝ) (b e : Policy nX k)
    (w : AuditedRecord T nX nH k) : ℝ :=
  let depth := historyDepth T t0 zeta
  clipUnit ((((T - depth : Nat) : ℝ)⁻¹) *
    ∑ t ∈ Finset.univ.filter (fun t : Fin T => depth ≤ t.val), phiwScore depth b e w t)
  -- @realizes \(\widehat\theta_{\mathrm{PHIW}}\)(clipped windowed ratio estimator)

-- @node: def:immediate-iw
/-- The clipped immediate importance-weighted estimator. -/
noncomputable def iwEstimator {T nX nH k : Nat} (b e : Policy nX k)
    (w : AuditedRecord T nX nH k) : ℝ :=
  clipUnit (((T : ℝ)⁻¹) * ∑ t : Fin T,
    (w t).2.2.1 * ratio b e (w t).1 (w t).2.1)
  -- @realizes \(\widehat\theta_{\mathrm{IW}}\)(clipped one-step estimator)

abbrev RawAuditedEstimator (T : Nat) :=
  (nX nH k : Nat) → Policy nX k → Policy nX k → AuditedRecord T nX nH k → ℝ
/-- A cardinality-polymorphic family of bounded measurable audited estimators.
Clipping is part of admissibility; the labels are available as atomic record values. -/
def AuditedEstimator (T : Nat) : Type :=
  {est : RawAuditedEstimator T //
    (∀ nX nH k b e, Measurable (est nX nH k b e)) ∧
    (∀ nX nH k b e w, est nX nH k b e w ∈ Set.Icc (-1 : ℝ) 1)}
  -- @realizes \(O_T^{\eta}\)(all measurable readouts of the complete audited record)
-- @env: S3
variable (N : Nat) (est : AuditedEstimator T)
  -- @realizes \(N\)(complete-state cardinality cap)

noncomputable def auditedRisk {T : Nat} {t0 zeta : ℝ} (eta : ℝ)
    (est : AuditedEstimator T) (i : HWIndex T t0 zeta) : ℝ :=
  Causalean.Stat.sqRisk (auditedLaw eta i.raw)
    (est.1 i.nX i.nH i.k i.raw.b i.raw.e) (targetValue i.raw)

-- @node: def:minimax-risk
/-- Audited minimax risk over all finite state and action cardinalities. -/
noncomputable def auditedMinimaxRisk (T : Nat) (t0 zeta eta : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal (auditedRisk (T := T) (t0 := t0) (zeta := zeta) eta)
  -- @realizes \(R_T(\eta)\)(headline audited minimax risk)

-- @node: def:capped-minimax-risk
/-- Audited minimax risk with a cap on complete-state cardinality. -/
noncomputable def cappedMinimaxRisk (T N : Nat) (t0 zeta eta : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (fun (est : AuditedEstimator T) (i : {i : HWIndex T t0 zeta // i.nX * i.nH ≤ N}) =>
      auditedRisk eta est i.1)
  -- @realizes \(N\)(state-cardinality cap) @realizes \(R_T(N,\eta)\)(capped risk)

-- @node: def:stationary-invariance-submodel
/-- The nested class whose behavior and target stationary laws coincide. -/
def InvarianceClass {T nX nH k : Nat} (t0 zeta : ℝ) (M : PomdpModel T nX nH k) : Prop :=
  HuWagerClass t0 zeta M ∧
  stationaryLaw (policyKernel M M.e) = stationaryLaw (policyKernel M M.b)
  -- @realizes \(\mathfrak M_T^{\mathrm{inv}}(t_0,\zeta)\)(stationary-law invariant class)

-- @node: def:invariance-minimax-risk
/-- Audited minimax risk on the stationary-law-invariance submodel. -/
noncomputable def invarianceMinimaxRisk (T : Nat) (t0 zeta eta : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (fun (est : AuditedEstimator T)
      (i : {i : HWIndex T t0 zeta // InvarianceClass t0 zeta i.raw}) =>
        auditedRisk eta est i.1)
  -- @realizes \(R_T^{\mathrm{inv}}(\eta)\)(invariance-submodel risk)

/-- A uniform distribution on a finite clone coordinate alphabet. -/
noncomputable def uniformFin (m : Nat) : Measure (Fin m) :=
  ∑ i : Fin m, ENNReal.ofReal (1 / (m : ℝ)) • Measure.dirac i

-- @node: uniformFin_prob
lemma uniformFin_prob (m : Nat) (hm : 1 ≤ m) :
    IsProbabilityMeasure (uniformFin m) := by
  constructor
  simp [uniformFin]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm), ENNReal.ofReal_natCast]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hm)) (by simp)

/-- Copy a base path while independently refreshing the latent clone coordinate. -/
def clonePath {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) :
    FullPath T 1 (n * m) k :=
  (fun t => ((w.1 t).1, π ((w.1 t).2, coords t)), w.2)
  -- @realizes \(\pi\)(fixed bijection) @realizes \(m\)(refreshed clone coordinate)

noncomputable def clonePathLaw {T n k m : Nat}
    (M : PomdpModel T 1 n k) (π : Fin n × Fin m ≃ Fin (n * m)) :
    Measure (FullPath T 1 (n * m) k) :=
  (M.law.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m))).map
    (fun q => clonePath π q.1 q.2)

/-- A clone path generated from a probability base law and nonempty uniform clone
coordinates remains a probability law. -/
lemma clonePathLaw_prob {T n k m : Nat} (M : PomdpModel T 1 n k)
    (hm : 1 ≤ m) (π : Fin n × Fin m ≃ Fin (n * m)) :
    IsProbabilityMeasure (clonePathLaw M π) := by
  have : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsProbabilityMeasure (uniformFin m) := this
  exact Measure.isProbabilityMeasure_map (by unfold clonePath; fun_prop)

/-- The relabeled joint kernel refreshes the clone coordinate uniformly. -/
noncomputable def cloneKernel {T n k m : Nat}
    (M : PomdpModel T 1 n k) (π : Fin n × Fin m ≃ Fin (n * m))
    (s : JointState 1 (n * m)) (a : Fin k) :
    Measure (ℝ × JointState 1 (n * m)) :=
  ∑ i : Fin m, ENNReal.ofReal (1 / (m : ℝ)) •
    (M.K (s.1, (π.symm s.2).1) a).map
      (fun q => (q.1, (q.2.1, π (q.2.2, i))))
  -- @realizes \(K^{m,\pi}\)(base transition with uniform next clone and fixed relabeling)

-- @node: def:clone-construction
/-- Clone a constant-observed-state model under one fixed state-label bijection. -/
noncomputable def cloneModel {T n k m : Nat} (M : PomdpModel T 1 n k)
    (hm : 1 ≤ m) (π : Fin n × Fin m ≃ Fin (n * m)) :
    PomdpModel T 1 (n * m) k where
  K := cloneKernel M π
  b := M.b
  e := M.e
  law := clonePathLaw M π
  law_prob := clonePathLaw_prob M hm π
  -- @realizes \(n\)(base latent cardinality) @realizes \(m\)(clone multiplicity) @realizes \(\pi\)(fixed permutation)

/-- The uniform prior over fixed bijections is used only for testing. -/
noncomputable def permutationMixture {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m) (eta : ℝ) :
    Measure (AuditedRecord T 1 (n * m) k) :=
  ∑ π : Fin n × Fin m ≃ Fin (n * m),
    ENNReal.ofReal (1 / (Fintype.card (Fin n × Fin m ≃ Fin (n * m)) : ℝ)) •
      auditedLaw eta (cloneModel M hm π)
  -- @realizes \(\overline{\mathbb P}_{M,m,\eta}\)(uniform fixed-atom permutation mixture)

instance (n m : Nat) : MeasurableSpace (Fin n × Fin m ≃ Fin (n * m)) := ⊤

/-- Draw the relabeling once, before the trajectory is initialized. -/
noncomputable def uniformRelabeling (n m : Nat) :
    Measure (Fin n × Fin m ≃ Fin (n * m)) :=
  ∑ π : Fin n × Fin m ≃ Fin (n * m),
    ENNReal.ofReal (1 / (Fintype.card (Fin n × Fin m ≃ Fin (n * m)) : ℝ)) •
      Measure.dirac π

/-- A single base path, independent clone coordinates, one fixed relabeling, and
an independent audit mask. -/
noncomputable def fixedPermutationCoupling {T n k m : Nat}
    (M : PomdpModel T 1 n k) (eta : ℝ) :
    Measure ((FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) :=
  (M.law.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m))).prod
    ((uniformRelabeling n m).prod (auditMaskLaw T eta))

def fixedPermutationRecord {T n k m : Nat}
    (q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) :
    AuditedRecord T 1 (n * m) k :=
  auditRecord (clonePath q.2.1 q.1.1 q.1.2) q.2.2

/-- The chronological rank of an audited epoch among earlier audits. -/
def auditRank {T : Nat} (mask : AuditMask T) (t : Fin T) : Nat :=
  (Finset.univ.filter (fun j : Fin T => j.val < t.val ∧ mask j)).card

/-- Assign distinct labels until exhaustion and then repeat the first label. -/
def freshRecord {T n k m : Nat} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (w : ObsPath T 1 k) (mask : AuditMask T)
    (σ : Equiv.Perm (Fin (n * m))) : AuditedRecord T 1 (n * m) k :=
  fun t =>
    let label : Fin (n * m) :=
      if h : auditRank mask t < n * m then σ ⟨auditRank mask t, h⟩
      else σ ⟨0, Nat.mul_pos hn hm⟩
    ((w t).1, ((w t).2.1, ((w t).2.2,
      (mask t, if mask t then some (⟨0, by decide⟩, label) else none))))

instance (r : Nat) : MeasurableSpace (Equiv.Perm (Fin r)) := ⊤

noncomputable def uniformPermutation (r : Nat) : Measure (Equiv.Perm (Fin r)) :=
  ∑ σ : Equiv.Perm (Fin r),
    ENNReal.ofReal (1 / (Fintype.card (Equiv.Perm (Fin r)) : ℝ)) • Measure.dirac σ

/-- Measurability of the path-indexed fresh-label law. -/
lemma freshKernel_measurable {T n k m : Nat} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) :
    Measurable (fun w : ObsPath T 1 k =>
      ((auditMaskLaw T eta).prod (uniformPermutation (n * m))).map
        (fun q => freshRecord hn hm w q.1 q.2)) := by
  have hf : Measurable (fun p : ObsPath T 1 k ×
      (AuditMask T × Equiv.Perm (Fin (n * m))) =>
      freshRecord hn hm p.1 p.2.1 p.2.2) := by
    unfold freshRecord
    apply measurable_pi_lambda
    intro t
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    exact (Measurable.of_discrete : Measurable
      (fun q : AuditMask T × Equiv.Perm (Fin (n * m)) =>
        if q.1 t then
          some ((⟨0, by decide⟩ : Fin 1),
            if h : auditRank q.1 t < n * m then q.2 ⟨auditRank q.1 t, h⟩
            else q.2 ⟨0, Nat.mul_pos hn hm⟩)
        else none)).comp measurable_snd
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hq (w : ObsPath T 1 k) : Measurable
      (fun q : AuditMask T × Equiv.Perm (Fin (n * m)) =>
        freshRecord hn hm w q.1 q.2) :=
    hf.comp measurable_prodMk_left
  simp_rw [Measure.map_apply (hq _) hs]
  exact measurable_measure_prodMk_left (hf hs)

/-- The same audit and label kernel is used for every base model and sign. -/
noncomputable def freshKernel {T n k m : Nat} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) : Kernel (ObsPath T 1 k) (AuditedRecord T 1 (n * m) k) where
  toFun := fun w =>
    ((auditMaskLaw T eta).prod (uniformPermutation (n * m))).map
      (fun q => freshRecord hn hm w q.1 q.2)
  measurable' := freshKernel_measurable hn hm eta

-- @node: def:fresh-label-law
/-- The observed path followed by the sign-independent fresh-label kernel. -/
noncomputable def freshLabelLaw {T n k m : Nat} (M : PomdpModel T 1 n k)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (eta : ℝ) :
    Measure (AuditedRecord T 1 (n * m) k) :=
  (obsLaw M).bind (freshKernel hn hm eta)
  -- @realizes \(\mathbb Q_{M,m,\eta}^{\mathrm{fresh}}\)(sign-independent fresh-label kernel)

/-- Decode binary actions in the arbitrary finite-action world. -/
def finActionBool (a : Fin 2) : Bool := a = 1
def boolActionFin (a : Bool) : Fin 2 := if a then 1 else 0

/-- Mapping Boolean actions to `Fin 2` preserves total probability. -/
lemma embedBinary_prob {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH) :
    IsProbabilityMeasure
      (M.law.map (fun w => (w.1, fun t => (boolActionFin (w.2 t).1, (w.2 t).2)))) := by
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- A real-reward Boolean-action predecessor model embedded into `Fin 2` actions. -/
noncomputable def embedBinary {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH) :
    PomdpModel T nX nH 2 where
  K := fun s a => M.K s (finActionBool a)
  b := fun x a => M.b x (finActionBool a)
  e := fun x a => M.e x (finActionBool a)
  law := M.law.map (fun w => (w.1, fun t => (boolActionFin (w.2 t).1, (w.2 t).2)))
  law_prob := embedBinary_prob M

/-- The signed-depth family is the binary-action instance of the headline world. -/
-- @node: def:signed-depth-family
noncomputable def signedDepthModel (T Q : Nat) (t0 zeta C : ℝ) (v : Bool)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (hQ : 1 ≤ Q) :
    PomdpModel T 1 (2 * (Q + 1)) 2 :=
  embedBinary (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
    T t0 zeta C Q v ht0 hzeta hC hQ)
  -- @realizes \(Q\)(rare terminal depth) @realizes \(M_{Q,v}\)(signed-depth binary-action model)

-- @realizes \(\varepsilon_C\)(reset sign bias for C > 1)
noncomputable def signBias (C : ℝ) (_hC : 1 < C) : ℝ := min ((C - 1) / 2) (1 / 2)
-- @realizes \(c_0\)(reward amplitude for positive t0)
noncomputable def rewardAmplitude (t0 : ℝ) (_ht0 : 0 < t0) : ℝ :=
  (1 - mixingAlpha t0) / 4
-- @realizes \(w_Q\)(terminal stationary mass for positive t0 and Q ≥ 1)
noncomputable def terminalMass (t0 : ℝ) (Q : Nat)
    (_ht0 : 0 < t0) (_hQ : 1 ≤ Q) : ℝ :=
  (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q / (1 - mixingAlpha t0 ^ (Q + 1))
noncomputable def separationRadius (t0 C : ℝ) (Q : Nat)
    (ht0 : 0 < t0) (hC : 1 < C) (hQ : 1 ≤ Q) : ℝ :=
  rewardAmplitude t0 ht0 * signBias C hC * terminalMass t0 Q ht0 hQ
  -- @realizes \(a_Q\)(signed target-value radius)

noncomputable def collisionEnvelope (T : Nat) (eta : ℝ) (m : Nat) : ℝ :=
  ∑ r ∈ Finset.range (T + 1),
    (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) *
      (1 - (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r)
  -- @realizes \(\psi_{T,\eta}(m)\)(binomial collision envelope)

/-- The first positive clone budget whose collision envelope meets the tolerance. -/
-- @realizes \(m_\star(T,\eta,\delta)\)(critical collision budget)
noncomputable def cloneBudget (T : Nat) (eta delta : ℝ)
    (_hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) : Nat := -- @realizes \(\delta\)(tolerance in (0,1))
  sInf {m : Nat | 1 ≤ m ∧ collisionEnvelope T eta m ≤ delta}

/-- The occupancy handle includes its envelope, a fixed-permutation sufficiency
coupling, and a repeated-label necessity test on a stationary recurrent path. -/
-- @node: def:clone-budget-handle
def CloneBudgetHandle (T : Nat) (eta delta : ℝ)
    (_heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) : Prop :=
  (∀ m : Nat, 1 ≤ m →
    (collisionEnvelope T eta m ≤ delta ↔ cloneBudget T eta delta hdelta ≤ m)) ∧
  (∀ (n k m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m)
      (M : PomdpModel T 1 n k),
    FullFiltrationPomdp M → FullFiltrationRandomization M → StationaryStart M →
    (fixedPermutationCoupling M eta).map fixedPermutationRecord =
      permutationMixture M hm eta ∧
    Causalean.Stat.tvDist (permutationMixture M hm eta)
      (freshLabelLaw M hn hm eta) ≤ collisionEnvelope T eta m) ∧
  (∀ (n k m : Nat) (hn : 1 ≤ n) (_hk : 1 ≤ k) (hm : 1 ≤ m), T ≤ n * m →
    ∃ M : PomdpModel T 1 n k,
      FullFiltrationPomdp M ∧ FullFiltrationRandomization M ∧ StationaryStart M ∧
      (permutationMixture M hm eta) {w | RepeatedAuditLabel w} =
        ENNReal.ofReal (collisionEnvelope T eta m) ∧
      (freshLabelLaw M hn hm eta) {w | RepeatedAuditLabel w} = 0 ∧
      Causalean.Stat.tvDist (permutationMixture M hm eta)
        (freshLabelLaw M hn hm eta) = collisionEnvelope T eta m)

noncomputable def collisionScale (T : Nat) (eta : ℝ) : ℝ :=
  eta ^ 2 * T * (T - 1) / 2

noncomputable def collisionLowerEnvelope (T : Nat) (eta : ℝ) (m : Nat) : ℝ :=
  ∑ r ∈ Finset.range (T + 1),
    (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) *
      (1 - Real.exp (-(r * (r - 1) : ℝ) / (2 * m : ℝ)))

noncomputable def signedDepthHorizon (T : Nat) (t0 zeta B0 : ℝ) : Nat :=
  max 1 (Int.toNat ⌈Real.log (16 * B0 * T) /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌉)

noncomputable def signedDepthCardinality (T : Nat) (t0 zeta B0 : ℝ) : Nat :=
  2 * (signedDepthHorizon T t0 zeta B0 + 1)

end CausalSmith.Stat.PomdpStateauditMinimax
