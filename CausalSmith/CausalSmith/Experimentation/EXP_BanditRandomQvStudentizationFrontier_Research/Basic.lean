/-
# Adaptive bandit experiments with random quadratic variation

This file fixes the finite-dimensional adaptive-experiment world, its score and
quadratic-variation vocabulary, and the paper's named assumption predicates.
The design-based `FiniteDesign` API is intentionally not used: its finite
assignment-space expectation cannot express the filtration and conditional
expectations required here.  The single-row adaptive propensity interface is
reused later by the Saco triangular-array world.
-/

import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Matrix.Basic

/-! # Adaptive bandit experiments with random quadratic variation -/

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section
set_option linter.style.openClassical false
open Classical

/- `EuclideanSpace` is definitionally a finite real coordinate family, but its
norm and metric are the paper's Euclidean ones rather than the Pi sup norm. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def dot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i
def outer {d : ℕ} (x y : Vec d) : Mat d := fun i j => x i * y j
def matVec {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => ∑ j, A i j * x j)
def qform {d : ℕ} (A : Mat d) (x : Vec d) : ℝ := dot x (matVec A x)
def identMat (d : ℕ) : Mat d := fun i j => if i = j then 1 else 0
def transpose {d : ℕ} (A : Mat d) : Mat d := fun i j => A j i
def psdLE {d : ℕ} (A B : Mat d) : Prop := ∀ x, qform A x ≤ qform B x
def PositiveDefinite {d : ℕ} (A : Mat d) : Prop := ∀ x, x ≠ 0 → 0 < qform A x
def opNormLE {d : ℕ} (A : Mat d) (C : ℝ) : Prop := ∀ x, ‖matVec A x‖ ≤ C * ‖x‖
def matrixEntryNorm {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, |A i j|
def matrixOperatorNorm {d : ℕ} (A : Mat d) : ℝ :=
  sSup {r : ℝ | ∃ x : Vec d, ‖x‖ = 1 ∧ r = ‖matVec A x‖}

def conditionalEventProb {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) : ℝ :=
  (μ (A ∩ B)).toReal / (μ B).toReal

def indicator {Ω α : Type*} (f : Ω → α) (s : Set α) (ω : Ω) : ℝ :=
  if f ω ∈ s then 1 else 0

/-- Conditional independence expressed by conditional factorization of all
measurable rectangle indicators. -/
def ConditionallyIndependent {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → α) (g : Ω → β) : Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t →
    μ[(fun ω => indicator f s ω * indicator g t ω) | m] =ᵐ[μ]
      fun ω => μ[indicator f s | m] ω * μ[indicator g t | m] ω

/-- Convergence in probability under a triangular array of laws. -/
def TendstoInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (X Y : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => (μ n {ω | ε < |X n ω - Y n ω|}).toReal) atTop (𝓝 0)

/-- CDF formulation of convergence in distribution. -/
def CDFConverges {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  (∀ n, AEMeasurable (X n) (μ n)) ∧
    ∀ z, Tendsto (fun n => (μ n {ω | X n ω ≤ z}).toReal) atTop (𝓝 (F z))

/-- Uniform Kolmogorov convergence over a class-indexed family of laws. -/
def UniformCDFConverges {I Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (X : ℕ → I → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ i z,
    |(μ n i {ω | X n i ω ≤ z}).toReal - F z| ≤ ε

-- @env: S1
/-- A finite-arm adaptive causal experiment on a superpopulation probability
space.  Fields are data; substantive restrictions are the named Props below. -/
structure AdaptiveCausalExperiment (Ω 𝒳 : Type*)
    [MeasurableSpace Ω] [MeasurableSpace 𝒳] (K d q : ℕ) where
  horizon : ℕ -- @realizes T(carrier positive integer; positivity imposed by theorem/class)
  horizon_pos : 0 < horizon -- @realizes T(positive decision horizon)
  arm_count : 2 ≤ K -- @realizes K(number of arms is at least two)
  -- @realizes \mathcal A(Fin K finite action set)
  dim_nonempty : 0 < d -- @realizes d(positive parameter dimension)
  law : Measure Ω -- @realizes P(probability-law carrier)
  law_univ : law univ = 1 -- @realizes P(probability mass one)
  filtration : Filtration ℕ ‹MeasurableSpace Ω› -- @realizes \mathcal F_t(time-indexed filtration)
  fullData : ℕ → Ω → 𝒳 × (Fin K → ℝ) -- @realizes W_t(full-data draw)
  -- @realizes \mathcal X(measurable context carrier)
  action : ℕ → Ω → Fin K -- @realizes A_t(random action in finite arm set)
  observedOutcome : ℕ → Ω → ℝ -- @realizes Y_t(observed real outcome)
  consistency : ∀ t, observedOutcome t = fun ω => (fullData t ω).2 (action t ω)
    -- @realizes Y_t(Y_t = Y_t(A_t))
  preTreatment : ℕ → MeasurableSpace Ω
  past_le_preTreatment : ∀ t, filtration (t - 1) ≤ preTreatment t
  context_measurable : ∀ t, Measurable[preTreatment t] (fun ω => (fullData t ω).1)
  stateSpace : Set (Vec q) -- @realizes \mathsf H(subset of Euclidean R^q)
  stateSpace_compact : IsCompact stateSpace -- @realizes \mathsf H(compact state space)
  state : ℕ → Ω → Vec q -- @realizes \eta_t(Euclidean policy-state process)
  state_mem : ∀ t ω, state t ω ∈ stateSpace
  -- @realizes q(Euclidean policy-state dimension)
  initialState : Vec q -- @realizes \eta_0(initial policy state)
  initialState_mem : initialState ∈ stateSpace
  state_zero : state 0 = fun _ => initialState
  policy : Fin K → 𝒳 → Vec q → ℝ -- @realizes \Pi(action×context×Euclidean-state→real)
  policy_nonneg : ∀ a x η, η ∈ stateSpace → 0 ≤ policy a x η
    -- @realizes \Pi(range in [0,1] on H)
  policy_sum_one : ∀ x η, η ∈ stateSpace → ∑ a, policy a x η = 1
    -- @realizes \Pi(arm probabilities sum to one on H)
  score : Fin K → 𝒳 → ℝ → Vec d → Vec d -- @realizes g(vector moment map)
  parameterSet : Set (Vec d) -- @realizes \Theta(subset of R^d)
  parameterSet_compact : IsCompact parameterSet -- @realizes \Theta(compactness)
  thetaStar : Vec d -- @realizes \theta^*(distinguished parameter vector)
  thetaStar_mem : thetaStar ∈ parameterSet -- @realizes \theta^*(membership in Theta)
  root : (∫ ω, ∑ a, score a (fullData 1 ω).1 ((fullData 1 ω).2 a) thetaStar ∂law) = 0
    -- @realizes \theta^*(population moment root)
  jacobian : Mat d -- @realizes H(population Jacobian matrix)
  jacobianMap : Vec d →L[ℝ] Vec d
  jacobianMap_apply : ∀ x, jacobianMap x = matVec jacobian x
    -- @realizes H(matrix action)

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
variable {K d q : ℕ}

/-- Positive mathematical horizons, excluding the non-experimental index zero. -/
abbrev PositiveHorizon := {T : ℕ // 0 < T}

/-- The paper-facing decision-time domain. -/
def DecisionTime (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (t : ℕ) : Prop :=
  t ∈ Finset.Icc 1 E.horizon
  -- @realizes t(decision occasion lies in {1,...,T})

def AdaptiveCausalExperiment.context (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (t : ℕ) : Ω → 𝒳 := fun ω => (E.fullData t ω).1
  -- @realizes X_t(context component of W_t)

def AdaptiveCausalExperiment.potentialOutcome
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (t : ℕ) (a : Fin K) : Ω → ℝ :=
  fun ω => (E.fullData t ω).2 a
  -- @realizes Y_t(a)(potential-outcome component of W_t)

def AdaptiveCausalExperiment.loggedPropensity
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (t : ℕ) (a : Fin K) : Ω → ℝ :=
  fun ω => E.policy a (E.context t ω) (E.state (t - 1) ω)
  -- @realizes \pi_t(Pi evaluated at X_t and eta_{t-1})

def AdaptiveCausalExperiment.populationMoment
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (θ : Vec d) : Vec d :=
  ∫ ω, ∑ a, E.score a (E.context 1 ω) (E.potentialOutcome 1 a ω) θ ∂E.law
  -- @realizes M_P(expectation of full-data arm-summed score)

def AdaptiveCausalExperiment.ipwScore
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (t : ℕ) : Ω → Vec d :=
  fun ω => (E.loggedPropensity t (E.action t ω) ω)⁻¹ •
    E.score (E.action t ω) (E.context t ω) (E.observedOutcome t ω) E.thetaStar
  -- @realizes \xi_t(adaptive inverse-propensity score)

def AdaptiveCausalExperiment.scoreSum
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (T : ℕ) : Ω → Vec d :=
  fun ω => ∑ t ∈ Finset.Icc 1 T, E.ipwScore t ω
  -- @realizes S_T(cumulative score)

def AdaptiveCausalExperiment.realizedQV
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (T : ℕ) : Ω → Mat d :=
  fun ω => ∑ t ∈ Finset.Icc 1 T, outer (E.ipwScore t ω) (E.ipwScore t ω)
  -- @realizes [S]_T(realized quadratic variation)

def AdaptiveCausalExperiment.predictableQV
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (T : ℕ) : Ω → Mat d :=
  fun ω i j => ∑ t ∈ Finset.Icc 1 T,
    MeasureTheory.condExp (E.filtration (t - 1)) E.law
      (fun ω' => E.ipwScore t ω' i * E.ipwScore t ω' j) ω
  -- @realizes \langle S\rangle_T(predictable quadratic variation)

-- @node: ass:iid-full-data
def IIDFullData (E : AdaptiveCausalExperiment Ω 𝒳 K d q) : Prop :=
  iIndepFun (fun t : {t // DecisionTime E t} => E.fullData t.1) E.law ∧
    ∀ t, DecisionTime E t → IdentDistrib (E.fullData t) (E.fullData 1) E.law E.law

-- @node: ass:sequential-randomization
def SequentialRandomization (E : AdaptiveCausalExperiment Ω 𝒳 K d q) : Prop :=
  (∀ t, DecisionTime E t → E.preTreatment t =
      E.filtration (t - 1) ⊔ MeasurableSpace.comap (E.context t) inferInstance) ∧
  (∀ t, DecisionTime E t → ∀ a,
    E.law[indicator (E.action t) {a} | E.preTreatment t] =ᵐ[E.law]
    E.loggedPropensity t a) ∧
  ∀ t, DecisionTime E t → ConditionallyIndependent E.law (E.preTreatment t) (E.action t)
    (fun ω => (E.fullData t ω).2)

-- @node: ass:uniform-overlap
def UniformOverlap (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (ε : ℝ) : Prop :=
  0 < ε ∧ ε < 1 / K ∧ ∀ a x η, η ∈ E.stateSpace → ε ≤ E.policy a x η
  -- @realizes \varepsilon(uniform exploration floor in (0,1/K))

-- @node: ass:bounded-score
def BoundedScore (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (B : ℝ) : Prop :=
  0 < B ∧ ∀ t, DecisionTime E t → ∀ᵐ ω ∂E.law, ∀ a θ, θ ∈ E.parameterSet →
    ‖E.score a (E.context t ω) (E.potentialOutcome t a ω) θ‖ ≤ B
  -- @realizes B(common positive score envelope)

-- @node: ass:smooth-z-map
def SmoothZMap (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (ρ D1 D2 : ℝ) : Prop :=
  0 < ρ ∧ 0 < D1 ∧ 0 < D2 ∧
  ∃ U : Set (Vec d), IsOpen U ∧ convexHull ℝ E.parameterSet ⊆ U ∧
  (∀ a x y, ContDiffOn ℝ 1 (E.score a x y) U) ∧
  (∀ a x y θ, θ ∈ U → ‖fderiv ℝ (E.score a x y) θ‖ ≤ D1) ∧
  (∀ a x y, ContDiffOn ℝ 2 (E.score a x y) (Metric.closedBall E.thetaStar ρ)) ∧
  ∀ a x y θ, θ ∈ Metric.closedBall E.thetaStar ρ →
    ‖fderiv ℝ (fun z => fderiv ℝ (E.score a x y) z) θ‖ ≤ D2
  -- @realizes D_1(first-derivative envelope)
  -- @realizes D_2(second-derivative envelope)
  -- @realizes \rho(local smoothness radius)

-- @node: ass:uniform-root-separation
def UniformRootSeparation (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (κ : ℝ → ℝ) : Prop :=
  (∀ u > 0, 0 < κ u) ∧ ∀ u > 0, ∀ θ ∈ E.parameterSet,
    u ≤ ‖θ - E.thetaStar‖ → κ u ≤ ‖E.populationMoment θ‖
  -- @realizes \kappa(positive root-separation modulus)

-- @node: ass:root-interior
def RootInterior (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (sTheta : ℝ) : Prop :=
  0 < sTheta ∧ sTheta ≤ Metric.infDist E.thetaStar (frontier E.parameterSet)
  -- @realizes s_\Theta(positive root interior radius)

-- @node: ass:jacobian-nonsingular
def JacobianNonsingular (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (hmin : ℝ) : Prop :=
  0 < hmin ∧ ∀ v, hmin * ‖v‖ ≤ ‖matVec E.jacobian v‖
  -- @realizes h_-(positive lower singular-value bound)

-- @node: ass:policy-lipschitz
def PolicyLipschitz (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (LPi : ℝ) : Prop :=
  0 < LPi ∧ ∀ a x η, η ∈ E.stateSpace → ∀ η', η' ∈ E.stateSpace →
    |E.policy a x η - E.policy a x η'| ≤ LPi * ‖η - η'‖
  -- @realizes L_\Pi(strictly positive finite policy Lipschitz modulus)

-- @node: ass:finite-tail-selection
def FiniteTailSelection (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (m : ℕ) (etaBar : Fin m → Vec q) (etaInf : Ω → Vec q) : Prop :=
  ∃ J : Ω → Fin m,
    Measurable[⨆ t, E.filtration t] J ∧ etaInf =ᵐ[E.law] fun ω => etaBar (J ω)
  -- @realizes m(number of finite attractors)
  -- @realizes \mathcal J(Fin m basin index set)
  -- @realizes J(terminal measurable basin label)
  -- @realizes \eta_\infty(terminal random state)
  -- @realizes \bar\eta_j(fixed attractor family)
  -- @realizes \bar\eta_J(selected attractor)

-- @node: ass:uniform-attraction-modulus
def UniformAttractionModulus (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (J : Ω → Fin m) (r δ : ℕ → ℝ) : Prop :=
  ∀ T, (E.law {ω | r T < (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.Icc 1 T, dist (E.state (t - 1) ω) (etaBar (J ω))}).toReal ≤ δ T
  -- @realizes r_T(nonnegative attraction tolerance sequence)
  -- @realizes \delta_T(attraction failure sequence)

-- @node: ass:vanishing-modulus
def VanishingModulus (r δ : ℕ → ℝ) : Prop :=
  (∀ T, 0 ≤ r T) ∧ (∀ T, 0 ≤ δ T) ∧
    Tendsto (fun (T : ℕ) => ((T : ℝ)⁻¹).sqrt + r T + δ T) atTop (𝓝 0)
  -- @realizes e_T(T^{-1/2}+r_T+delta_T tending to zero)

-- @node: ass:basin-nondegeneracy
def BasinNondegeneracy (omegaInf : Ω → Mat d) (μ : Measure Ω) (omegaMin : ℝ) : Prop :=
  0 < omegaMin ∧ ∀ᵐ ω ∂μ, psdLE (omegaMin • identMat d) (omegaInf ω)
  -- @realizes \omega_-(positive terminal covariance eigenvalue floor)

-- @node: ass:finite-attractor-separation
def FiniteAttractorSeparation (etaBar : Fin m → Vec q) (sEta : ℝ) : Prop :=
  0 < sEta ∧ ∀ j k, j ≠ k → sEta ≤ dist (etaBar j) (etaBar k)
  -- @realizes s_\eta(positive pairwise attractor separation)

-- @node: ass:basin-mass-floor
def BasinMassFloor (μ : Measure Ω) (J : Ω → Fin m) (pmin : ℝ) : Prop :=
  0 < pmin ∧ pmin ≤ 1 / m ∧ ∀ j, pmin ≤ (μ {ω | J ω = j}).toReal
  -- @realizes p_-(uniform positive basin-mass floor)
  -- @realizes p_j(P(J=j) mixture weight)

-- @node: ass:uniform-projected-predictable-qv-growth
def UniformProjectedPredictableQVGrowth
    {ι 𝒳 : Type*} [MeasurableSpace 𝒳] {K d q : ℕ}
    (E : PositiveHorizon → ι → AdaptiveCausalExperiment Ω 𝒳 K d q) (c : Vec d)
    (laws : PositiveHorizon → ι → Measure Ω)
    (filtration : PositiveHorizon → ι → Filtration ℕ ‹MeasurableSpace Ω›)
    (X : PositiveHorizon → ι → ℕ → Ω → ℝ) (k : ℕ → ℕ) (omega : ℕ → ℝ)
    (Lambda : PositiveHorizon → ι → Ω → ℝ) : Prop :=
  c ≠ 0 ∧
  (∀ T : PositiveHorizon, ∀ i, (E T i).horizon = T) ∧
  (∀ T : PositiveHorizon, ∀ i, laws T i = (E T i).law) ∧
  (∀ T : PositiveHorizon, ∀ i, filtration T i = (E T i).filtration) ∧
  (∀ T : PositiveHorizon, ∀ i t ω', X T i t ω' =
    dot c (matVec ((E T i).jacobian)⁻¹ ((E T i).ipwScore t ω'))) ∧
  (∀ T : PositiveHorizon, k T < T) ∧
  (∀ T : PositiveHorizon, 0 < omega T) ∧
  (∀ T : PositiveHorizon, ∀ i, Measurable[filtration T i (k T)] (Lambda T i)) ∧
  (∀ T : PositiveHorizon, ∀ i, ∀ᵐ ω' ∂laws T i, omega T ≤ Lambda T i ω') ∧
  ∀ u > 0, ∀ ε > 0, ∀ᶠ T : PositiveHorizon in atTop, ∀ i,
    (laws T i {ω | u < |((T : ℝ) * Lambda T i ω)⁻¹ *
      (∑ t ∈ Finset.Icc (k T + 1) T,
        MeasureTheory.condExp (filtration T i (t - 1)) (laws T i)
          (fun ω' => (X T i t ω') ^ 2) ω) - 1|}).toReal ≤ ε
  -- @realizes k_T(deterministic early cutoff)
  -- @realizes \Lambda_T(early-measurable positive information scale)
  -- @realizes c(nonzero contrast defining every projected score)
  -- @realizes \mathfrak Q_T^{\mathrm{proj}}(c)(class-indexed law family)

end

end CausalSmith.Experimentation.BanditRandomQV
