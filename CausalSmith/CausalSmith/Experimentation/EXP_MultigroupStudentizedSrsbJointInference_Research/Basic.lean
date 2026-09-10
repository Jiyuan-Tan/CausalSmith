import Causalean.Experimentation.DesignBased.TwoStage
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Causalean.Mathlib.Analysis.TwoByTwoSpectralProjector
import Causalean.Stat.CLT.ChiSquared

/-!
# Multigroup studentized soft rerandomization

Shared finite-population objects for the paper's two-stage, history-adaptive design.
The probability space is the finite assignment-path space supplied by
`FiniteDesign`; potential outcomes themselves are fixed functions.
-/

open scoped BigOperators Matrix
open Filter Finset MeasureTheory ProbabilityTheory Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

noncomputable section

open Causalean.Experimentation.DesignBased
open Causalean.Mathlib.Analysis

abbrev Vec2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec3 := Fin 3 → ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Exposure := Bool × Bool
abbrev GlobalHistory (G B n : ℕ) := Fin (2 * B) → Fin G → (Fin n → Bool) × Bool
abbrev PotentialSchedule (G B n : ℕ) :=
  Fin G → Fin (2 * B) → Fin n → GlobalHistory G B n → ℝ
abbrev CellIndex (G n : ℕ) := Fin G × Fin n × Exposure
abbrev ObservedEndpoints (Omega : Type*) (G B n : ℕ) :=
  Omega → Fin G → Fin B → Fin n → ℝ
abbrev InclusionProbabilities (Omega : Type*) (G B n : ℕ) :=
  Omega → Fin B → CellIndex G n → ℝ
abbrev PairInclusionProbabilities (Omega : Type*) (G B n : ℕ) :=
  Omega → Fin B → CellIndex G n → CellIndex G n → ℝ

def vecDot (x y : Vec2) : ℝ := ∑ i, x i * y i
def outer (x y : Vec2) : Mat2 := fun i j => x i * y j
def matQuad (A : Mat2) (x : Vec2) : ℝ := vecDot x (A.mulVec x)
def matMaxAbs (A : Mat2) : ℝ := ∑ i, ∑ j, |A i j|

def vec3Dot (x y : Vec3) : ℝ := ∑ i, x i * y i
def mat3Quad (A : Mat3) (x : Vec3) : ℝ := vec3Dot x (A.mulVec x)

def IsCenteredGaussianWithCovariance (Q : Measure Vec3) (Sigma : Mat3) : Prop :=
  IsProbabilityMeasure Q ∧ ∀ t : Vec3,
    ∫ z, Complex.exp (Complex.I * (∑ i, (t i : ℂ) * (z i : ℂ))) ∂Q =
      Complex.exp (-(mat3Quad Sigma t : ℂ) / 2)

def gaussianSoftScalarMoment (Q : Measure Vec3) (eta kappa : ℝ) : ℝ :=
  ∫ z, eta + (1 - eta) * Real.exp (-kappa * (z 2) ^ 2) ∂Q

def gaussianSoftMatrixMoment (Q : Measure Vec3) (eta kappa : ℝ) : Mat2 := fun i j ↦
  ∫ z, z i.castSucc * z j.castSucc *
    (eta + (1 - eta) * Real.exp (-kappa * (z 2) ^ 2)) ∂Q

def signValue (x : Bool) : ℝ := if x then 1 else -1
def saturationValue (q : Bool) : ℝ := if q then (3 : ℝ) / 4 else 1 / 4
def radialWeight (eta kappa w : ℝ) : ℝ :=
  eta + (1 - eta) * Real.exp (-kappa * w ^ 2)
def treatmentProbability (d q : Bool) : ℝ :=
  if d then saturationValue q else 1 - saturationValue q
-- @realizes p_{dq}(p(1,q)=q and p(0,q)=1-q)

def contrast (d q : Bool) : Vec2 := fun j =>
  if j = 0 then (if d then 1 / 2 else -1 / 2)
  else if q then 1 / 2 else -1 / 2
-- @realizes c_{dq}(four fixed direct-and-spillover coefficients)

def historyAgreeThrough {G B n : ℕ} (t : ℕ)
    (h h' : GlobalHistory G B n) : Prop :=
  ∀ s : Fin (2 * B), s.val ≤ t → h s = h' s

def historyAgreeAt {G B n : ℕ} (g : Fin G) (t : ℕ)
    (h h' : GlobalHistory G B n) : Prop :=
  (∀ s : Fin (2 * B), (s.val = t ∨ s.val + 1 = t) → h s g = h' s g) ∧
  (∀ s : Fin (2 * B), ∀ g' : Fin G, g' ≠ g → h s g' = h' s g')

def assignmentHistory {Omega : Type*} {G B n : ℕ} (hB : 0 < B)
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (w : Omega) : GlobalHistory G B n := fun t g ↦
  (A w ⟨t.val / 2, by omega⟩ g, x w ⟨t.val / 2, by omega⟩ g)

def pathConditionalEvent {Omega : Type*} {G B n : ℕ}
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (b : Fin B) (w z : Omega) : Prop :=
  ∀ k : Fin B, k.val < b.val → x z k = x w k ∧ A z k = A w k

noncomputable def pathConditionalE {Omega : Type*} [Fintype Omega] {G B n : ℕ}
    (D : FiniteDesign Omega)
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (b : Fin B) (w : Omega) (X : Omega → ℝ) : ℝ := by
  classical
  let p := D.Pr (pathConditionalEvent x A b w)
  exact if p = 0 then 0 else
    D.E (fun z ↦ FiniteDesign.ind (pathConditionalEvent x A b w) z * X z) / p

-- @node: ass:design-based-finiteness
def DesignBasedFiniteness {Omega : Type*} {G B n : ℕ} {_hB : 0 < B}
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (Y : PotentialSchedule G B n)
    (realizedHistory : Omega → GlobalHistory G B n)
    (observed : Omega → Fin G → Fin B → Fin n → ℝ) : Prop :=
  (∀ w, realizedHistory w = assignmentHistory _hB x A w) ∧
  ∀ w g b i, observed w g b i =
    Y g ⟨2 * b.val + 1, by omega⟩ i (assignmentHistory _hB x A w)

-- @node: ass:partial-interference
def PartialInterference {G B n : ℕ} (Y : PotentialSchedule G B n) : Prop :=
  ∀ g t i h h', (∀ s, h s g = h' s g) → Y g t i h = Y g t i h'

-- @node: ass:stratified-interference
def StratifiedInterference {G B n : ℕ} (Y : PotentialSchedule G B n) : Prop :=
  ∀ g t i h h',
    (∀ s : Fin (2 * B), s ≠ t → h s = h' s) →
    (∀ g' : Fin G, g' ≠ g → h t g' = h' t g') →
    (h t g).1 i = (h' t g).1 i → (h t g).2 = (h' t g).2 →
    Y g t i h = Y g t i h'

-- @node: ass:nonanticipation
def Nonanticipation {G B n : ℕ} (Y : PotentialSchedule G B n) : Prop :=
  ∀ g t i h h', historyAgreeThrough t.val h h' → Y g t i h = Y g t i h'

-- @node: ass:finite-memory-lag-one
def FiniteMemoryLagOne {G B n : ℕ} (Y : PotentialSchedule G B n) : Prop :=
  ∀ g (t : Fin (2 * B)) i, 1 ≤ t.val → ∀ h h',
    historyAgreeAt g t.val h h' → Y g t i h = Y g t i h'

-- @node: ass:imbalance-variance-window
def ImbalanceVarianceWindow {Omega : Type*} {B : ℕ}
    (cσ Cσ : ℝ) (σsq : Omega → Fin B → ℝ) : Prop :=
  0 < cσ ∧ ∀ w b, cσ ≤ σsq w b ∧ σsq w b ≤ Cσ
  -- @realizes c_\sigma(uniform positive lower bound)
  -- @realizes \sigma_b^2(exact variance inside the uniform window)
  -- @realizes C_\sigma(uniform finite upper bound)

noncomputable def rowMatrixConvergesInProbability {O : ℕ → Type*}
    [∀ N, Fintype (O N)] (D : (N : ℕ) → FiniteDesign (O N))
    (X : (N : ℕ) → O N → Mat2) (L : Mat2) : Prop := by
  classical
  exact ∀ (i j : Fin 2) (ε : ℝ), 0 < ε →
    Tendsto (fun N ↦ (D N).Pr (fun w ↦ ε ≤ |X N w i j - L i j|)) atTop (nhds 0)

-- @node: ass:rr-covariance-stabilization
noncomputable def RRCovarianceStabilization {O : ℕ → Type*}
    [∀ N, Fintype (O N)] (D : (N : ℕ) → FiniteDesign (O N))
    (avgSigmaRR : (N : ℕ) → O N → Mat2) (OmegaRR : Mat2) : Prop :=
  rowMatrixConvergesInProbability D avgSigmaRR OmegaRR
  -- @realizes \Sigma_{b,\mathrm{RR}}(block-average predictable covariance process)
  -- @realizes \Omega_{\mathrm{RR}}(deterministic probability limit)

-- @node: ass:rr-limit-positive
def RRLimitPositive (OmegaRR : Mat2) : Prop := Matrix.PosDef OmegaRR
-- @realizes \Omega_{\mathrm{RR}}(positive-definite limiting covariance)

-- @node: ass:cr-covariance-stabilization
noncomputable def CRCovarianceStabilization {O : ℕ → Type*}
    [∀ N, Fintype (O N)] (D : (N : ℕ) → FiniteDesign (O N))
    (avgSigmaCR : (N : ℕ) → O N → Mat2) (OmegaCR : Mat2) : Prop :=
  rowMatrixConvergesInProbability D avgSigmaCR OmegaCR
  -- @realizes \Sigma_{b,0}(block-average complete-randomization covariance process)
  -- @realizes \Omega_{\mathrm{CR}}(deterministic probability limit)

-- @node: ass:projection-stabilization
noncomputable def ProjectionStabilization {O : ℕ → Type*}
    [∀ N, Fintype (O N)] (D : (N : ℕ) → FiniteDesign (O N))
    (avgProjection : (N : ℕ) → O N → Mat2) (P : Mat2) : Prop :=
  rowMatrixConvergesInProbability D avgProjection P
  -- @realizes \beta_b(block-average rank-one projection process)
  -- @realizes P(deterministic projection-covariance limit)

def balancedSignSupport (G : ℕ) (z : Fin G → Bool) : Prop :=
  2 * (Finset.univ.filter fun g ↦ z g).card = G
-- @realizes \mathcal X_G(exact balanced-sign support)

def uniformBalancedSignMass (G : ℕ) (z : Fin G → Bool) : ℝ :=
  by
    classical
    exact if balancedSignSupport G z then (Nat.choose G (G / 2) : ℝ)⁻¹ else 0
-- @realizes P_0(uniform mass on the exact balanced-sign support)

def secondStageTreatedCount (n : ℕ) (z : Fin G → Bool) (g : Fin G) : ℕ :=
  if z g then 3 * (n / 4) else n / 4

def uniformSecondStageMass (n : ℕ) (z : Fin G → Bool)
    (a : Fin G → Fin n → Bool) : ℝ :=
  ∏ g, if (Finset.univ.filter fun i ↦ a g i).card = secondStageTreatedCount n z g
    then (Nat.choose n (secondStageTreatedCount n z g) : ℝ)⁻¹ else 0

def blockAssignmentIndicator {Omega : Type*} {G B n : ℕ}
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (b : Fin B) (z : Fin G → Bool) (a : Fin G → Fin n → Bool) (w : Omega) : ℝ :=
  if x w b = z ∧ A w b = a then 1 else 0

def softKernelNormalizer (G : ℕ) (eta kappa sigma : ℝ) (V : Fin G → ℝ) : ℝ :=
  ∑ z : Fin G → Bool, uniformBalancedSignMass G z *
    radialWeight eta kappa ((Real.sqrt G)⁻¹ * ∑ g, signValue (z g) * V g / Real.sqrt sigma)

def softBlockKernelMass (G n : ℕ) (eta kappa sigma : ℝ) (V : Fin G → ℝ)
    (z : Fin G → Bool) (a : Fin G → Fin n → Bool) : ℝ :=
  uniformBalancedSignMass G z *
      radialWeight eta kappa
        ((Real.sqrt G)⁻¹ * ∑ g, signValue (z g) * V g / Real.sqrt sigma) /
      softKernelNormalizer G eta kappa sigma V * uniformSecondStageMass n z a

/-- The two full-path laws have, after every supported history, respectively the uniform
balanced-sign/fixed-count kernel and its stated radial soft tilt. -/
def PredictableSoftTwoStageLaw {Omega : Type*} [Fintype Omega] {G B n : ℕ}
    (D : FiniteDesign Omega) (P0 : Omega → Fin B → FiniteDesign Omega)
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (V : Omega → Fin B → Fin G → ℝ) (sigmaSq : Omega → Fin B → ℝ)
    (eta kappa : ℝ) : Prop := by
  classical
  exact
  ∀ w b, 0 < D.Pr (pathConditionalEvent x A b w) →
    0 < (P0 w b).Pr (pathConditionalEvent x A b w) ∧
    ∀ z a,
      pathConditionalE (P0 w b) x A b w (blockAssignmentIndicator x A b z a) =
          uniformBalancedSignMass G z * uniformSecondStageMass n z a ∧
      pathConditionalE D x A b w (blockAssignmentIndicator x A b z a) =
          softBlockKernelMass G n eta kappa (sigmaSq w b) (V w b) z a

def LoggedProbabilityCoherence {Omega : Type*} [Fintype Omega] {G B n : ℕ}
    (D : FiniteDesign Omega)
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (pi : InclusionProbabilities Omega G B n)
    (piPair : PairInclusionProbabilities Omega G B n) : Prop :=
  (∀ w b k, pi w b k = pathConditionalE D x A b w
      (fun z ↦ if x z b k.1 = k.2.2.2 ∧ A z b k.1 k.2.1 = k.2.2.1 then 1 else 0)) ∧
  (∀ w b k, 0 < pi w b k ∧ pi w b k < 1) ∧
    -- @realizes \pi_{gbi,dq}(actual conditional inclusion probability in (0,1))
  (∀ w b k l, piPair w b k l = pathConditionalE D x A b w
      (fun z ↦
        (if x z b k.1 = k.2.2.2 ∧ A z b k.1 k.2.1 = k.2.2.1 then 1 else 0) *
        (if x z b l.1 = l.2.2.2 ∧ A z b l.1 l.2.1 = l.2.2.1 then 1 else 0))) ∧
  (∀ w b k l, piPair w b k l ∈ Set.Icc (0 : ℝ) 1)
    -- @realizes \pi_{k\ell,b}(actual conditional pair inclusion probability in [0,1])

-- @env: S1
-- @env: S2
-- @env: S3
-- @env: S4
-- @env: S5
variable {Omega : Type*} [Fintype Omega]

-- @node: def:model-class
structure BoundedLagOnePartialInterferenceClass (Omega : Type*) [Fintype Omega] where
  G : ℕ -- @realizes G(even group count)
  B : ℕ -- @realizes B(number of two-period blocks)
  n : ℕ -- @realizes n(group size divisible by four)
  B_pos : 0 < B
  G_pos : 0 < G
  n_pos : 0 < n
  G_even : 2 ∣ G
  n_four : 4 ∣ n
  M : ℝ -- @realizes M(positive outcome envelope)
  KH : ℝ -- @realizes K_H(positive score envelope)
  cSigma : ℝ -- @realizes c_\sigma(lower imbalance-variance constant)
  CSigma : ℝ -- @realizes C_\sigma(upper imbalance-variance constant)
  cRho : ℝ -- @realizes c_\rho(inert relative-growth lower constant)
  CRho : ℝ -- @realizes C_\rho(inert relative-growth upper constant)
  eta : ℝ -- @realizes \eta(soft-weight floor)
  kappa : ℝ -- @realizes \kappa(soft-weight curvature)
  lambda : ℝ -- @realizes \lambda(predictable-balance loading)
  alpha : ℝ -- @realizes \alpha(nominal noncoverage level)
  M_pos : 0 < M
  KH_pos : 0 < KH
  cSigma_pos : 0 < cSigma
  CSigma_pos : 0 < CSigma
  cRho_pos : 0 < cRho
  CRho_pos : 0 < CRho
  eta_mem : eta ∈ Set.Ioo (0 : ℝ) 1
  kappa_pos : 0 < kappa
  lambda_pos : 0 < lambda
  alpha_mem : alpha ∈ Set.Ioo (0 : ℝ) 1
  rClip : ℕ → ℝ -- @realizes r_B(positive clipping sequence)
  rClip_pos : ∀ N, 0 < rClip N
  rClip_zero : Tendsto rClip atTop (nhds 0)
  design : FiniteDesign Omega -- @realizes P_{\mathrm{RR},b}(finite assignment-path law)
  referenceDesign : Omega → Fin B → FiniteDesign Omega -- @realizes P_0(history-indexed uniform balanced-sign benchmark)
  x : Omega → Fin B → Fin G → Bool -- @realizes x_b(realized balanced sign vector)
  Aassign : Omega → Fin B → Fin G → Fin n → Bool -- @realizes A_{gbi}(own-treatment draw)
  realizedHistory : Omega → GlobalHistory G B n
  Y : PotentialSchedule G B n -- @realizes Y_{gti}(fixed schedule on complete histories)
  observed : ObservedEndpoints Omega G B n -- @realizes \bar Y^{\mathrm{obs}}_{gb}(carrier)
  H : Fin G → ℝ -- @realizes H_g(centered baseline group score)
  V : Omega → Fin B → Fin G → ℝ -- @realizes V_{gb}(prefix-measurable balance score)
  sigmaSq : Omega → Fin B → ℝ -- @realizes \sigma_b^2((G-1) inverse sum of squared scores)
  pi : InclusionProbabilities Omega G B n -- @realizes \pi_{gbi,dq}(logged probability)
  piPair : PairInclusionProbabilities Omega G B n -- @realizes \pi_{k\ell,b}(logged)
  outcome_bounded : ∀ g t i h, |Y g t i h| ≤ M
  score_bounded : ∀ g, |H g| ≤ KH
  score_centered : ∑ g, H g = 0
  x_balanced : ∀ w b, 2 * (Finset.univ.filter fun g ↦ x w b g).card = G
  treated_count : ∀ w b g,
    (Finset.univ.filter fun i ↦ Aassign w b g i).card =
      if x w b g then 3 * (n / 4) else n / 4
  sigma_formula : ∀ w b,
    sigmaSq w b = ((G - 1 : ℕ) : ℝ)⁻¹ * ∑ g, (V w b g) ^ 2
  designLaw : PredictableSoftTwoStageLaw design referenceDesign x Aassign V sigmaSq eta kappa
  loggedProbabilities : LoggedProbabilityCoherence design x Aassign pi piPair
  designBased : DesignBasedFiniteness (_hB := B_pos) x Aassign Y realizedHistory observed
  partialInterference : PartialInterference Y
  stratified : StratifiedInterference Y
  nonanticipating : Nonanticipation Y
  lagOne : FiniteMemoryLagOne Y
  varianceWindow : ImbalanceVarianceWindow cSigma CSigma sigmaSq
-- @realizes \mathcal H_t(prefixes of the complete history carrier)
-- @realizes \mathcal H_{2B}(Fin (2*B) indexed exposure histories)
-- @realizes \mathcal F_b(assignment-path prefixes through block b)
-- @realizes \mathcal M_{G,B}(six-condition structural design class)

namespace BoundedLagOnePartialInterferenceClass

variable (Mdl : BoundedLagOnePartialInterferenceClass Omega)

def groups := Fin Mdl.G
-- @realizes \mathcal G_G(computed as Fin G)
def blocks := Fin Mdl.B
-- @realizes \mathcal B_B(computed as Fin B)
def units := Fin Mdl.n
-- @realizes \mathcal I_n(computed as Fin n)
def qLow : ℝ := 1 / 4
-- @realizes q_L(exactly one quarter)
def qHigh : ℝ := 3 / 4
-- @realizes q_H(exactly three quarters)
def saturations : Finset ℝ := {qLow, qHigh}
-- @realizes \mathcal Q(computed two-point menu contained in (0,1))
def treatments : Finset Bool := {false, true}
-- @realizes \mathcal D(computed full binary menu)

def groupSaturation (w : Omega) (b : Fin Mdl.B) (g : Fin Mdl.G) : Bool := Mdl.x w b g
-- @realizes Q_{gb}(high iff the balanced sign is positive)

def cellIndicator (w : Omega) (b : Fin Mdl.B) (k : CellIndex Mdl.G Mdl.n) : ℝ :=
  if groupSaturation Mdl w b k.1 = k.2.2.2 ∧ Mdl.Aassign w b k.1 k.2.1 = k.2.2.1 then 1 else 0
-- @realizes I_{gbi,dq}(indicator of realized saturation and treatment cell)

def observedGroupMean (w : Omega) (b : Fin Mdl.B) (g : Fin Mdl.G) : ℝ :=
  (Mdl.n : ℝ)⁻¹ * ∑ i, Mdl.observed w g b i
-- @realizes \bar Y^{\mathrm{obs}}_{gb}(unit-average observed endpoint)

def observedGrandMean (w : Omega) (b : Fin Mdl.B) : ℝ :=
  (Mdl.G : ℝ)⁻¹ * ∑ g, observedGroupMean Mdl w b g
-- @realizes \bar Y^{\mathrm{obs}}_b(group-average observed endpoint)

def canonicalHistory (d q : Bool) : GlobalHistory Mdl.G Mdl.B Mdl.n :=
  fun _ _ ↦ (fun _ ↦ d, q)

def sustainedEndpoint (g : Fin Mdl.G) (b : Fin Mdl.B) (i : Fin Mdl.n)
    (d q : Bool) : ℝ :=
  Mdl.Y g ⟨2 * b.val + 1, by omega⟩ i (canonicalHistory Mdl d q)
-- @realizes Y_{gbi}(d,q)(lag-one sustained-exposure endpoint)

def blockTarget (b : Fin Mdl.B) : Vec2 := fun j ↦
  ((Mdl.G * Mdl.n : ℕ) : ℝ)⁻¹ *
    ∑ g, ∑ i, ∑ d : Bool, ∑ q : Bool,
      contrast d q j * sustainedEndpoint Mdl g b i d q
-- @realizes \tau_b(block direct-and-spillover target)

def exposureMean (d q : Bool) : ℝ :=
  ((Mdl.G * Mdl.B * Mdl.n : ℕ) : ℝ)⁻¹ *
    ∑ b, ∑ g, ∑ i, sustainedEndpoint Mdl g b i d q
-- @realizes \mu_{dq}(finite-population sustained-exposure mean)

-- @node: def:joint-estimand
def jointEstimand : Vec2 := fun j ↦ ∑ d : Bool, ∑ q : Bool,
  contrast d q j * exposureMean Mdl d q
-- @realizes \tau(four-cell joint causal estimand)

def exposureMeanEstimator (w : Omega) (d q : Bool) : ℝ :=
  ((Mdl.G * Mdl.B * Mdl.n : ℕ) : ℝ)⁻¹ *
    ∑ b, ∑ g, ∑ i,
      let k : CellIndex Mdl.G Mdl.n := (g, i, d, q)
      cellIndicator Mdl w b k * Mdl.observed w g b i / Mdl.pi w b k
-- @realizes \widehat\mu_{dq}(logged-probability Horvitz--Thompson exposure mean)

def blockEstimator (w : Omega) (b : Fin Mdl.B) : Vec2 := fun j ↦
  ((Mdl.G * Mdl.n : ℕ) : ℝ)⁻¹ *
    ∑ g, ∑ i, ∑ d : Bool, ∑ q : Bool,
      let k : CellIndex Mdl.G Mdl.n := (g, i, d, q)
      contrast d q j * cellIndicator Mdl w b k * Mdl.observed w g b i / Mdl.pi w b k
-- @realizes \widehat\tau_b(block Horvitz--Thompson effect vector)

-- @node: def:joint-ht-estimator
def jointHTEstimator (w : Omega) : Vec2 := fun j ↦ ∑ d : Bool, ∑ q : Bool,
  contrast d q j * exposureMeanEstimator Mdl w d q
-- @realizes \widehat\tau(joint logged-probability Horvitz--Thompson estimator)

def groupScore (g : Fin Mdl.G) (b : Fin Mdl.B) (q : Bool) : Vec2 := fun j ↦
  ∑ d : Bool, contrast d q j * ((Mdl.n : ℝ)⁻¹ * ∑ i, sustainedEndpoint Mdl g b i d q)
-- @realizes m_{gbq}(saturation-specific causal score)

def groupScoreEstimator (w : Omega) (g : Fin Mdl.G) (b : Fin Mdl.B) (q : Bool) : Vec2 := fun j ↦
  ∑ d : Bool, contrast d q j * ((Mdl.n : ℝ)⁻¹ *
    ∑ i, (if Mdl.Aassign w b g i = d then 1 else 0) * sustainedEndpoint Mdl g b i d q /
      treatmentProbability d q)
-- @realizes \widehat m_{gbq}(within-group Horvitz--Thompson score)

def groupSamplingError (w : Omega) (g : Fin Mdl.G) (b : Fin Mdl.B) (q : Bool) : Vec2 :=
  groupScoreEstimator Mdl w g b q - groupScore Mdl g b q
-- @realizes e_{gbq}(centered within-group sampling error)

def scoreDifference (g : Fin Mdl.G) (b : Fin Mdl.B) : Vec2 :=
  groupScore Mdl g b true - groupScore Mdl g b false
-- @realizes a_{gb}(high-minus-low group score)

def blockR (w : Omega) (b : Fin Mdl.B) : Vec2 :=
  Real.sqrt Mdl.G • (blockEstimator Mdl w b - blockTarget Mdl b)
-- @realizes R_b(normalized block estimation error)

def blockA (w : Omega) (b : Fin Mdl.B) : Vec2 :=
  (Real.sqrt Mdl.G)⁻¹ • ∑ g, signValue (Mdl.x w b g) • scoreDifference Mdl g b
-- @realizes A_b(balanced-sign score component)

def blockU (w : Omega) (b : Fin Mdl.B) : Vec2 :=
  (2 * (Real.sqrt Mdl.G)⁻¹) •
    ∑ g, groupSamplingError Mdl w g b (groupSaturation Mdl w b g)
-- @realizes U_b(within-group score component)

def conditionalEvent (b : Fin Mdl.B) (w z : Omega) : Prop :=
  pathConditionalEvent Mdl.x Mdl.Aassign b w z
-- @realizes \mathcal F_b(path-prefix conditioning event)

noncomputable def conditionalE (b : Fin Mdl.B) (w : Omega) (X : Omega → ℝ) : ℝ :=
  pathConditionalE Mdl.design Mdl.x Mdl.Aassign b w X

def conditionalCovVec (b : Fin Mdl.B) (w : Omega) (X : Omega → Vec2) : Mat2 := fun i j ↦
  conditionalE Mdl b w (fun z ↦
    (X z i - conditionalE Mdl b w (fun u ↦ X u i)) *
    (X z j - conditionalE Mdl b w (fun u ↦ X u j)))

def withinCovariance (w : Omega) (g : Fin Mdl.G) (b : Fin Mdl.B) (q : Bool) : Mat2 :=
  conditionalCovVec Mdl b w (fun z ↦ groupSamplingError Mdl z g b q)
-- @realizes T_{gbq}(conditional within-group score covariance)

def withinCovarianceComponent (w : Omega) (b : Fin Mdl.B) : Mat2 :=
  (2 / Mdl.G : ℝ) • ∑ g, (withinCovariance Mdl w g b false + withinCovariance Mdl w g b true)
-- @realizes K_b(unchanged within-group covariance component)

def completeRandomizationCovariance (w : Omega) (b : Fin Mdl.B) : Mat2 :=
  let abar : Vec2 := (Mdl.G : ℝ)⁻¹ • ∑ g, scoreDifference Mdl g b
  ((Mdl.G - 1 : ℕ) : ℝ)⁻¹ •
      (∑ g, outer (scoreDifference Mdl g b - abar) (scoreDifference Mdl g b - abar)) +
    withinCovarianceComponent Mdl w b
-- @realizes \Sigma_{b,0}(complete-randomization block covariance)

def rrCovariance (w : Omega) (b : Fin Mdl.B) : Mat2 :=
  conditionalCovVec Mdl b w (fun z ↦ blockR Mdl z b)
-- @realizes \Sigma_{b,\mathrm{RR}}(soft-rerandomization conditional block covariance)

def rawBalance (w : Omega) (b : Fin Mdl.B) (z : Fin Mdl.G → Bool) : ℝ :=
  (Real.sqrt Mdl.G)⁻¹ * ∑ g, signValue (z g) * Mdl.V w b g
-- @realizes Z_b(x)(raw normalized balance statistic)

def standardizedBalance (w : Omega) (b : Fin Mdl.B) (z : Fin Mdl.G → Bool) : ℝ :=
  rawBalance Mdl w b z / Real.sqrt (Mdl.sigmaSq w b)
-- @realizes W_b(x)(exactly variance-one standardized imbalance)

def softWeight (w : ℝ) : ℝ :=
  Mdl.eta + (1 - Mdl.eta) * Real.exp (-Mdl.kappa * w ^ 2)
-- @realizes f_{\eta,\kappa}(eta-floor radial weight)

def softNormalizer (w : Omega) (b : Fin Mdl.B) : ℝ :=
  Mdl.design.E (fun z ↦ softWeight Mdl (standardizedBalance Mdl w b (Mdl.x z b)))
-- @realizes C_b(reference-law expectation of the soft weight)

def projectionLoading (w : Omega) (b : Fin Mdl.B) : Vec2 := fun i ↦
  Mdl.design.Cov (fun z ↦ blockR Mdl z b i)
    (fun z ↦ standardizedBalance Mdl w b (Mdl.x z b))
-- @realizes \beta_b(score-on-imbalance covariance loading)

def avgSigmaRR (w : Omega) : Mat2 :=
  (Mdl.B : ℝ)⁻¹ • ∑ b, rrCovariance Mdl w b

def avgSigmaCR (w : Omega) : Mat2 :=
  (Mdl.B : ℝ)⁻¹ • ∑ b, completeRandomizationCovariance Mdl w b

def avgProjection (w : Omega) : Mat2 :=
  (Mdl.B : ℝ)⁻¹ • ∑ b, outer (projectionLoading Mdl w b) (projectionLoading Mdl w b)

end BoundedLagOnePartialInterferenceClass

def SharedModelConstants {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N)) : Prop :=
  ∀ N,
    (Mdl N).M = (Mdl 0).M ∧ (Mdl N).KH = (Mdl 0).KH ∧
    (Mdl N).cSigma = (Mdl 0).cSigma ∧ (Mdl N).CSigma = (Mdl 0).CSigma ∧
    (Mdl N).eta = (Mdl 0).eta ∧ (Mdl N).kappa = (Mdl 0).kappa ∧
    (Mdl N).lambda = (Mdl 0).lambda

def SharedClippingSequence {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N)) : Prop :=
  ∀ N k, (Mdl N).rClip k = (Mdl 0).rClip k

def packScoreBalance (X : Vec2) (W : ℝ) : Vec3 := fun i ↦
  if h : i.val < 2 then X ⟨i.val, h⟩ else W

def scoreBalanceCovariance {Omega : Type*} [Fintype Omega]
    (D : FiniteDesign Omega) (X : Omega → Vec2) (W : Omega → ℝ) : Mat3 := fun i j ↦
  D.Cov (fun z ↦ packScoreBalance (X z) (W z) i)
    (fun z ↦ packScoreBalance (X z) (W z) j)

def rawSoftScalarMoment {Omega : Type*} [Fintype Omega]
    (D : FiniteDesign Omega) (eta kappa : ℝ) (W : Omega → ℝ) : ℝ :=
  D.E (fun z ↦ radialWeight eta kappa (W z))

def rawSoftMatrixMoment {Omega : Type*} [Fintype Omega]
    (D : FiniteDesign Omega) (eta kappa : ℝ) (X : Omega → Vec2) (W : Omega → ℝ) : Mat2 :=
  fun i j ↦ D.E (fun z ↦ X z i * X z j * radialWeight eta kappa (W z))

def discreteSoftScalarMoment {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) (b : Fin Mdl.B) : ℝ :=
  Mdl.design.E (fun z ↦ Mdl.softWeight (Mdl.standardizedBalance w b (Mdl.x z b)))

def discreteSoftMatrixMoment {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (X : Omega → Vec2)
    (w : Omega) (b : Fin Mdl.B) : Mat2 := fun i j ↦
  Mdl.design.E (fun z ↦ X z i * X z j *
    Mdl.softWeight (Mdl.standardizedBalance w b (Mdl.x z b)))

variable {Omega1 : Type*} [Fintype Omega1]
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

noncomputable def softTilt (D : FiniteDesign Omega1) (weight : Omega1 → ℝ)
    (hweight : ∀ z, 0 ≤ weight z) (hnorm : D.E weight ≠ 0) : FiniteDesign Omega1 where
  p z := D.p z * weight z / D.E weight
  p_nonneg z := div_nonneg (mul_nonneg (D.p_nonneg z) (hweight z)) (le_of_lt (lt_of_le_of_ne
    (by exact Finset.sum_nonneg fun z _ ↦ mul_nonneg (D.p_nonneg z) (hweight z)) (Ne.symm hnorm)))
  p_sum := by
    rw [← Finset.sum_div]
    simp only [FiniteDesign.E]
    exact div_self hnorm

abbrev BalancedSignAssignment (G : ℕ) :=
  {S : Finset (Fin G) // S.card = G / 2}

def balancedSign {G : ℕ} (S : BalancedSignAssignment G) (g : Fin G) : Bool := g ∈ S.1

abbrev FixedCountAssignment (n k : ℕ) :=
  {S : Finset (Fin n) // S.card = k}

abbrev SoftSecondStageCarrier (n : ℕ) {G : ℕ} (S : BalancedSignAssignment G) (g : Fin G) :=
  FixedCountAssignment n (if balancedSign S g then 3 * (n / 4) else n / 4)

-- @node: def:soft-two-stage-design
noncomputable def softTwoStageDesign (G n : ℕ) (eta kappa sigma : ℝ) (V : Fin G → ℝ)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    FiniteDesign (BalancedSignAssignment G) ×
      (∀ S : BalancedSignAssignment G, ∀ g : Fin G,
        FiniteDesign (SoftSecondStageCarrier n S g)) := by
  let P0 : FiniteDesign (BalancedSignAssignment G) :=
    completeRandomization (V := Fin G) (G / 2) (by simpa using Nat.div_le_self G 2)
  let weight := fun S : BalancedSignAssignment G ↦ radialWeight eta kappa
    ((Real.sqrt G)⁻¹ * ∑ g, signValue (balancedSign S g) * V g / Real.sqrt sigma)
  have hweight : ∀ S, 0 ≤ weight S := by
    intro S
    dsimp [weight, radialWeight]
    positivity
  have hweightLower : ∀ S, eta ≤ weight S := by
    intro S
    dsimp [weight, radialWeight]
    have hexp : 0 < Real.exp
        (-kappa * ((Real.sqrt ↑G)⁻¹ * ∑ g, signValue (balancedSign S g) * V g /
          Real.sqrt sigma) ^ 2) := Real.exp_pos _
    nlinarith
  have hnorm : P0.E weight ≠ 0 := by
    have hEpos : 0 < P0.E weight := calc
      0 < eta := heta0
      _ = P0.E (fun _ ↦ eta) := (P0.E_const eta).symm
      _ ≤ P0.E weight := by
        unfold FiniteDesign.E
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_left (hweightLower S) (P0.p_nonneg S)
    exact ne_of_gt hEpos
  let secondStage := fun S : BalancedSignAssignment G => fun g : Fin G =>
    completeRandomization (V := Fin n)
      (if balancedSign S g then 3 * (n / 4) else n / 4) (by
        simp only [Fintype.card_fin]
        split <;> omega)
  exact (softTilt P0 weight hweight hnorm, secondStage)
-- @realizes \mathcal X_G(exact balanced-sign carrier)
-- @realizes P_0(computed uniform complete-randomization design)
-- @realizes P_{\mathrm{RR},b}(specified radial tilt followed by fixed-count product design)
-- @realizes A_{gbi}(uniform exact-count independent second stage held as one block draw)

noncomputable def softTiltVariance (eta kappa : ℝ) : ℝ :=
  (eta + (1 - eta) * (1 + 2 * kappa) ^ (-(3 : ℝ) / 2)) /
    (eta + (1 - eta) * (1 + 2 * kappa) ^ (-(1 : ℝ) / 2))
-- @realizes v_{\eta,\kappa}(tagged scalar displayed ratio)

-- @node: def:projection-gain
noncomputable def projectionGain (eta kappa : ℝ) (P : Mat2) : Mat2 :=
  (1 - softTiltVariance eta kappa) • P
-- @realizes P(limiting projection covariance entering the gain)

noncomputable def impossiblePairs {G n : ℕ}
    (piPair : CellIndex G n → CellIndex G n → ℝ) :
    Finset (CellIndex G n × CellIndex G n) := by
  classical
  exact Finset.univ.filter fun kl ↦ kl.1 < kl.2 ∧ piPair kl.1 kl.2 = 0
-- @realizes \mathcal Z_b(unordered distinct zero-joint-probability pairs)

def cellOutcome {G n : ℕ} (Y : CellIndex G n → ℝ) (k : CellIndex G n) : Vec2 :=
  contrast k.2.2.1 k.2.2.2 • (fun _ ↦ Y k)
-- @realizes \mathcal K_b(group-unit-treatment-saturation index carrier)
-- @realizes u_{k,b}(contrast-weighted exposure-cell outcome)

noncomputable def spectralClip2 (r : ℝ) (A : Mat2) : Mat2 :=
  if lambda₁ A = lambda₂ A then max (lambda₁ A) r • 1
  else max (lambda₂ A) r • 1 +
    (max (lambda₁ A) r - max (lambda₂ A) r) • topProjector A

def chiSquareQuantile2 (alpha : ℝ) : ℝ :=
  sInf {q : ℝ | ENNReal.ofReal (1 - alpha) ≤ Causalean.Stat.chiSqDist 2 (Set.Iic q)}

-- @node: def:simultaneous-wald-region
def simultaneousWaldRegion (G B : ℕ) (tauHat : Vec2) (GammaPlus : Mat2)
    (alpha : ℝ) : Set Vec2 :=
  {t | (G * B : ℕ) * matQuad GammaPlus⁻¹ (tauHat - t) ≤ chiSquareQuantile2 alpha}
-- @realizes \mathcal C_\alpha(chi-square calibrated simultaneous Wald ellipse)
-- @realizes \alpha(level entering the chi-square quantile)
-- @realizes \widehat\Gamma_+(inverse spectrally clipped studentizer)

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
