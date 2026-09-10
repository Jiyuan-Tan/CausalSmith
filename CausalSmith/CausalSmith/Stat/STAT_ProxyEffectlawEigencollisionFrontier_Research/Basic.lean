import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.AtomicLaw
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SpectralSubstrate

/-!
Core carriers, model assumptions, observable summaries, and finite-product sampling laws for the
proxy effect-law collision frontier.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- One full-data record. -/
structure FullData (k dx dz : ℕ) where
  U : Fin k -- @realizes \(U\)(latent class in Fin k)
  T : Bool -- @realizes \(T\)(binary treatment)
  X : Fin dx → ℝ -- @realizes \(X\)(target proxy in real dx-space)
  Z : Fin dz → ℝ -- @realizes \(Z\)(reference proxy in real dz-space)
  Y0 : ℝ -- @realizes \(Y(t)\)(potential outcome at t=false)
  Y1 : ℝ -- @realizes \(Y(t)\)(potential outcome at t=true)
  Y : ℝ -- @realizes \(Y\)(observed outcome)

/-- One observed record. -/
structure Obs (dx dz : ℕ) where
  T : Bool -- @realizes \(T\)(observed treatment coordinate)
  X : Fin dx → ℝ -- @realizes \(X\)(observed target proxy)
  Z : Fin dz → ℝ -- @realizes \(Z\)(observed reference proxy)
  Y : ℝ -- @realizes \(Y\)(observed outcome)

def FullData.toCoordinates {k dx dz : ℕ} (w : FullData k dx dz) :=
  (w.U, w.T, w.X, w.Z, w.Y0, w.Y1, w.Y)

def Obs.toCoordinates {dx dz : ℕ} (o : Obs dx dz) := (o.T, o.X, o.Z, o.Y)

instance {k dx dz} : TopologicalSpace (FullData k dx dz) :=
  TopologicalSpace.induced FullData.toCoordinates inferInstance

/-- Standard product Borel structure on the full-data real coordinates and finite coordinates. -/
instance {k dx dz} : MeasurableSpace (FullData k dx dz) :=
  MeasurableSpace.comap FullData.toCoordinates inferInstance

instance {k dx dz} : BorelSpace (FullData k dx dz) := by
  constructor
  change MeasurableSpace.comap FullData.toCoordinates inferInstance = _
  rw [borel_comap]
  congr 1
  exact BorelSpace.measurable_eq

/-- Single full-data records are measurable in the induced product Borel structure. -/
-- @node: instMeasurableSingletonClassFullData
instance {k dx dz} : MeasurableSingletonClass (FullData k dx dz) := ⟨fun w => by
  change @MeasurableSet (FullData k dx dz)
    (MeasurableSpace.comap FullData.toCoordinates inferInstance) {w}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{FullData.toCoordinates w}, measurableSet_singleton _, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    cases x
    cases w
    simp_all [FullData.toCoordinates]
  · exact fun h => congrArg FullData.toCoordinates h⟩

instance {dx dz} : TopologicalSpace (Obs dx dz) :=
  TopologicalSpace.induced Obs.toCoordinates inferInstance

/-- Standard product Borel structure on the observed real coordinates and binary treatment. -/
instance {dx dz} : MeasurableSpace (Obs dx dz) :=
  MeasurableSpace.comap Obs.toCoordinates inferInstance

instance {dx dz} : BorelSpace (Obs dx dz) := by
  constructor
  change MeasurableSpace.comap Obs.toCoordinates inferInstance = _
  rw [borel_comap]
  congr 1
  exact BorelSpace.measurable_eq

/-- Generic probability-law carrier on a measurable space.  Model membership is deliberately
consumer-local rather than part of this carrier. -/
structure FullDataProbabilityLaw (α : Type*) [MeasurableSpace α] where
  measure : Measure α -- @realizes \(P\)(generic full-data measure carrier)
  prob : IsProbabilityMeasure measure -- @realizes \(P\)(probability-law constraint)

/-- Observed-coordinate map. @realizes \(O\)(tuple T,X,Z,Y) -/
def obsMap {k dx dz : ℕ} (w : FullData k dx dz) : Obs dx dz :=
  ⟨w.T, w.X, w.Z, w.Y⟩

lemma obsMap_measurable (k dx dz : ℕ) : Measurable (@obsMap k dx dz) := by
  rw [measurable_comap_iff]
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (Obs.toCoordinates ∘ obsMap) inferInstance ≤
    MeasurableSpace.comap FullData.toCoordinates inferInstance
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun x => (x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2))
  · fun_prop
  · rfl

/-- The observed margin of a full-data law. @realizes \(P_O\)(pushforward along O) -/
noncomputable def obsLaw {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    [IsProbabilityMeasure P] : Measure (Obs dx dz) :=
  P.map obsMap

instance obsLaw_isProbabilityMeasure {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (obsLaw P) := by
  exact Measure.isProbabilityMeasure_map (obsMap_measurable k dx dz).aemeasurable

/-- Finite observed iid product law. @realizes \(Q_P^{(n)}\)(P_O tensor n) -/
noncomputable def sampleLaw {k dx dz n : ℕ} (P : Measure (FullData k dx dz))
    [IsProbabilityMeasure P] : Measure (Fin n → Obs dx dz) :=
  Measure.pi (fun _ : Fin n => obsLaw P)

instance sampleLaw_isProbabilityMeasure {k dx dz n : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (sampleLaw (n := n) P) := by
  exact Measure.pi.instIsProbabilityMeasure (fun _ : Fin n => obsLaw P)

def potential {k dx dz : ℕ} (t : Bool) (w : FullData k dx dz) : ℝ :=
  if t then w.Y1 else w.Y0

def latentCell {k dx dz : ℕ} (u : Fin k) (t : Bool) : Set (FullData k dx dz) :=
  {w | w.U = u ∧ w.T = t}

def latentClass {k dx dz : ℕ} (u : Fin k) : Set (FullData k dx dz) := {w | w.U = u}

noncomputable def conditionalMean {α : Type*} [MeasurableSpace α]
    (P : Measure α) (A : Set α) (f : α → ℝ) : ℝ :=
  (P.real A)⁻¹ * (∫ x in A, f x ∂P)

/-- Latent-class mass. @realizes \(p_u\)(P(U=u)) -/
noncomputable def latentMass {k dx dz : ℕ} (P : Measure (FullData k dx dz)) (u : Fin k) : ℝ :=
  P.real (latentClass u)

/-- Conditional potential-outcome mean. @realizes \(\mu_{tu}\)(E[Y(t)|U=u]) -/
noncomputable def latentMean {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    (t : Bool) (u : Fin k) : ℝ := conditionalMean P (latentClass u) (potential t)

/-- Latent-class effect. @realizes \(\tau_u\)(mu_1u-mu_0u) -/
noncomputable def latentEffect {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    (u : Fin k) : ℝ := latentMean P true u - latentMean P false u

/-- Derived effect-support radius. @realizes \(L_{\tau}\)(4 L sqrt(dz)/sigma0) -/
noncomputable def effectRadius (dz : ℕ) (L sigma0 : ℝ) : ℝ :=
  4 * L * Real.sqrt dz / sigma0

/-- Conditional reference-proxy feature matrix. @realizes \(A_t\)(cell conditional Z means) -/
noncomputable def referenceFeature {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    (t : Bool) : RectMatrix dz k :=
  fun i u => conditionalMean P (latentCell u t) (fun w => w.Z i)

/-- Conditional target-proxy feature matrix. @realizes \(B\)(class conditional X means) -/
noncomputable def targetFeature {k dx dz : ℕ} (P : Measure (FullData k dx dz)) :
    RectMatrix dx k :=
  fun i u => conditionalMean P (latentClass u) (fun w => w.X i)

/-- First canonical target-proxy vector. @realizes \(e_1\)(first basis vector) -/
def firstBasis (dx : ℕ) : Fin dx → ℝ := fun i => if i.val = 0 then 1 else 0

/-- Fixed model-parameter domain used throughout the paper.  The individual conjuncts are the
load-bearing symbol-space realizations, rather than comments on an unrelated declaration. -/
def CoreParameterDomain (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : Prop :=
  2 ≤ k ∧ -- @realizes \(k\)(k in {2,3,...})
  k ≤ dx ∧ k ≤ dz ∧
  1 ≤ L ∧ -- @realizes \(L\)(L in [1,infinity))
  0 < pi0 ∧ pi0 ≤ 1 / (2 * k : ℝ) ∧ -- @realizes \(\pi_0\)(0 < pi0 <= 1/(2k))
  0 < sigma0 ∧ sigma0 ≤ 1 -- @realizes \(\sigma_0\)(0 < sigma0 <= 1)

/-- Domain of the effect-separation scale used by labeled-coordinate results. -/
def GapScaleDomain (g : ℝ) : Prop :=
  0 < g ∧ -- @realizes \(g\)(strictly positive gap scale)
  g ≤ 1 / 4 -- @realizes \(g\)(gap scale at most one quarter)

-- @env: S1
-- @realizes \(k\)(Nat with lower-bound premise) @realizes \(d_x\)(Nat dimension)
-- @realizes \(d_z\)(Nat dimension)
-- @realizes \(L\)(real envelope) @realizes \(\pi_0\)(real positivity margin)
-- @realizes \(\sigma_0\)(real rank margin)
-- @realizes \(P\)(probability measure on FullData)
variable {k dx dz : ℕ} {L pi0 sigma0 g : ℝ}
  (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]

variable (t : Bool) -- @realizes \(t\)(Bool arm realizes {0,1})
variable (u : Fin k) -- @realizes \(u\)(Fin k realizes {1,...,k})

/-- A real-valued function with a finite uniform envelope. -/
def UniformlyBounded {α : Type*} (f : α → ℝ) : Prop :=
  ∃ B : ℝ, ∀ x, |f x| ≤ B

-- @node: ass:reference-proxy-separation
def ReferenceProxySeparation : Prop :=
  ∀ (u : Fin k) (t : Bool) (f : (Fin dz → ℝ) → ℝ)
    (q : ((Fin dx → ℝ) × ℝ) → ℝ),
    Measurable f → Measurable q → UniformlyBounded f → UniformlyBounded q →
      conditionalMean P (latentCell u t) (fun w => f w.Z * q (w.X, w.Y)) =
      conditionalMean P (latentCell u t) (fun w => f w.Z) *
        conditionalMean P (latentCell u t) (fun w => q (w.X, w.Y))

-- @node: ass:target-proxy-separation
def TargetProxySeparation : Prop :=
  ∀ (u : Fin k) (f : (Fin dx → ℝ) → ℝ) (q : (ℝ × Bool) → ℝ),
    Measurable f → Measurable q → UniformlyBounded f → UniformlyBounded q →
      conditionalMean P (latentClass u) (fun w => f w.X * q (w.Y, w.T)) =
      conditionalMean P (latentClass u) (fun w => f w.X) *
        conditionalMean P (latentClass u) (fun w => q (w.Y, w.T))

-- @node: ass:consistency
def CausalConsistency : Prop := ∀ᵐ w ∂P, w.Y = potential w.T w

-- @node: ass:latent-ignorability
def ArmwiseLatentIgnorability : Prop :=
  ∀ (u : Fin k) (t : Bool) (f : ℝ → ℝ) (q : Bool → ℝ),
    Measurable f → Measurable q → UniformlyBounded f → UniformlyBounded q →
      conditionalMean P (latentClass u) (fun w => f (potential t w) * q w.T) =
        conditionalMean P (latentClass u) (fun w => f (potential t w)) *
          conditionalMean P (latentClass u) (fun w => q w.T)

-- @node: ass:anchor
def AnchorNormalization : Prop := ∀ᵐ w ∂P, ∀ i : Fin dx, i.val = 0 → w.X i = 1

-- @node: ass:bounded-x
def BoundedTargetProxy : Prop :=
  ∀ᵐ w ∂P, Real.sqrt (∑ i, (w.X i) ^ 2) ≤ L

def outerProduct {dx dz : ℕ} (z : Fin dz → ℝ) (x : Fin dx → ℝ) : RectMatrix dz dx :=
  fun i j => z i * x j

-- @node: ass:bounded-proxy-product
def BoundedProxyProduct : Prop :=
  ∀ᵐ w ∂P, ‖matrixCLM (outerProduct w.Z w.X)‖ ≤ L

-- @node: ass:bounded-outcome-proxy-product
def BoundedOutcomeProxyProduct : Prop :=
  ∀ᵐ w ∂P, ‖matrixCLM (w.Y • outerProduct w.Z w.X)‖ ≤ L

-- @node: ass:latent-arm-positivity
def LatentArmPositivity : Prop := ∀ u t, pi0 ≤ P.real (latentCell u t)

-- @node: ass:proxy-rank-margin
def ProxyRankMargin : Prop :=
  sigma0 ≤ signalMinSingular (referenceFeature P false) ∧
    sigma0 ≤ signalMinSingular (referenceFeature P true) ∧
    sigma0 ≤ signalMinSingular (targetFeature P)

/-- The uniformly conditioned causal VMW submodel. @realizes \(\mathcal M\)(ten model fields) -/
-- @node: def:model-class
structure UCVMWModel (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] : Prop where
  coreDomain : CoreParameterDomain k dx dz L pi0 sigma0
  referenceProxySeparation : ReferenceProxySeparation P
  targetProxySeparation : TargetProxySeparation P
  consistency : CausalConsistency P
  latentIgnorability : ArmwiseLatentIgnorability P
  anchor : AnchorNormalization P
  boundedX : BoundedTargetProxy (L := L) P
  boundedProxyProduct : BoundedProxyProduct (L := L) P
  boundedOutcomeProxyProduct : BoundedOutcomeProxyProduct (L := L) P
  latentArmPositivity : LatentArmPositivity (pi0 := pi0) P
  proxyRankMargin : ProxyRankMargin (sigma0 := sigma0) P

/-- Smallest positive pairwise effect gap, with `⊤` for a singleton support.
    @realizes \(\delta(P)\)(nearest positive effect gap) -/
noncomputable def effectGap : EReal :=
  sInf {d : EReal | ∃ u v : Fin k,
    0 < latentMass P u ∧ 0 < latentMass P v ∧ latentEffect P u ≠ latentEffect P v ∧
    d = |latentEffect P u - latentEffect P v|}

-- @node: ass:gap-window
def GapWindow : Prop := (g / 2 : EReal) ≤ effectGap P ∧ effectGap P ≤ (2 * g : ℝ)

-- @node: ass:distinct-effects
def DistinctEffects : Prop :=
  ((Finset.univ.filter fun u => 0 < latentMass P u).image (latentEffect P)).card = k

/-- Gap-localized model membership. @realizes \(\mathcal M(g)\)(model plus gap shell) -/
-- @node: def:gap-stratum
structure GapStratum (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] : Prop extends
    UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P where
  gapDomain : GapScaleDomain g
  gapWindow : GapWindow (g := g) P
  distinctEffects : DistinctEffects P

/-- Five-block observable summary space. -/
structure SummarySpace (dx dz : ℕ) where
  M0 : RectMatrix dz dx
  M1 : RectMatrix dz dx
  N0 : RectMatrix dz dx
  N1 : RectMatrix dz dx
  mX : Fin dx → ℝ

instance {dx dz} : Zero (SummarySpace dx dz) :=
  ⟨⟨0, 0, 0, 0, 0⟩⟩

abbrev SummaryCoordinates (dx dz : ℕ) :=
  RectMatrix dz dx × RectMatrix dz dx × RectMatrix dz dx × RectMatrix dz dx × (Fin dx → ℝ)

def SummarySpace.toCoordinates {dx dz : ℕ} (s : SummarySpace dx dz) :
    SummaryCoordinates dx dz := (s.M0, s.M1, s.N0, s.N1, s.mX)

instance {dx dz} : TopologicalSpace (SummarySpace dx dz) :=
  TopologicalSpace.induced SummarySpace.toCoordinates inferInstance

instance {dx dz} : MeasurableSpace (SummarySpace dx dz) :=
  borel (SummarySpace dx dz)

instance {dx dz} : BorelSpace (SummarySpace dx dz) := by
  constructor
  rfl

def obsArm {dx dz : ℕ} (t : Bool) : Set (Obs dx dz) := {o | o.T = t}

/-- Population observable moment summary.
    @realizes \(M_t(P)\)(armwise ZX moment) @realizes \(N_t(P)\)(armwise YZX moment)
    @realizes \(m_X(P)\)(unconditional X mean) @realizes \(S(P)\)(five-block tuple) -/
noncomputable def obsSummary : SummarySpace dx dz where
  M0 i j := conditionalMean (obsLaw P) (obsArm false) (fun o => o.Z i * o.X j)
  M1 i j := conditionalMean (obsLaw P) (obsArm true) (fun o => o.Z i * o.X j)
  N0 i j := conditionalMean (obsLaw P) (obsArm false) (fun o => o.Y * o.Z i * o.X j)
  N1 i j := conditionalMean (obsLaw P) (obsArm true) (fun o => o.Y * o.Z i * o.X j)
  mX j := (∫ o, o.X j ∂obsLaw P)

/-- Sum of four operator norms and the Euclidean mean norm. @realizes \(d_S\)(summary metric) -/
noncomputable def dS {dx dz : ℕ} (s q : SummarySpace dx dz) : ℝ :=
  ‖matrixCLM (s.M0 - q.M0)‖ + ‖matrixCLM (s.M1 - q.M1)‖ +
    ‖matrixCLM (s.N0 - q.N0)‖ + ‖matrixCLM (s.N1 - q.N1)‖ +
    Real.sqrt (∑ i, (s.mX i - q.mX i) ^ 2)

/-- The summary loss is symmetric. -/
-- @node: dS_symm
lemma dS_symm {dx dz : ℕ} (s q : SummarySpace dx dz) : dS s q = dS q s := by
  unfold dS
  have block (A B : RectMatrix dz dx) : ‖matrixCLM (A - B)‖ = ‖matrixCLM (B - A)‖ := by
    have heq : matrixCLM (A - B) = -(matrixCLM (B - A)) := by
      ext x i
      simp [matrixCLM, Matrix.toEuclideanLin_apply]
    rw [heq, norm_neg]
  rw [block s.M0 q.M0, block s.M1 q.M1, block s.N0 q.N0, block s.N1 q.N1]
  congr 1
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The summary loss obeys the triangle inequality. -/
-- @node: dS_triangle
lemma dS_triangle {dx dz : ℕ} (a b c : SummarySpace dx dz) :
    dS a c ≤ dS a b + dS b c := by
  unfold dS
  have block (A B C : RectMatrix dz dx) :
      ‖matrixCLM (A - C)‖ ≤ ‖matrixCLM (A - B)‖ + ‖matrixCLM (B - C)‖ := by
    have heq : matrixCLM (A - C) = matrixCLM (A - B) + matrixCLM (B - C) := by
      ext x i
      simp [matrixCLM, Matrix.toEuclideanLin_apply]
    rw [heq]
    exact norm_add_le _ _
  have h0 := block a.M0 b.M0 c.M0
  have h1 := block a.M1 b.M1 c.M1
  have h2 := block a.N0 b.N0 c.N0
  have h3 := block a.N1 b.N1 c.N1
  have hx : ‖(WithLp.toLp 2 (a.mX - c.mX) : Euc dx)‖ ≤
      ‖(WithLp.toLp 2 (a.mX - b.mX) : Euc dx)‖ +
        ‖(WithLp.toLp 2 (b.mX - c.mX) : Euc dx)‖ := by
    have heq : (WithLp.toLp 2 (a.mX - c.mX) : Euc dx) =
        WithLp.toLp 2 (a.mX - b.mX) + WithLp.toLp 2 (b.mX - c.mX) := by
      ext i
      simp
    rw [heq]
    exact norm_add_le _ _
  have hx' : Real.sqrt (∑ i, (a.mX i - c.mX i) ^ 2) ≤
      Real.sqrt (∑ i, (a.mX i - b.mX i) ^ 2) +
        Real.sqrt (∑ i, (b.mX i - c.mX i) ^ 2) := by
    simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, Pi.sub_apply, sq_abs] using hx
  linarith

lemma dS_continuous (dx dz : ℕ) :
    Continuous (Function.uncurry (@dS dx dz)) := by
  unfold Function.uncurry dS
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  have hM0coord : Continuous (fun s : SummarySpace dx dz => s.M0) := by
    exact continuous_fst.comp hcoord
  have hM1coord : Continuous (fun s : SummarySpace dx dz => s.M1) := by
    exact (continuous_fst.comp continuous_snd).comp hcoord
  have hN0coord : Continuous (fun s : SummarySpace dx dz => s.N0) := by
    exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp hcoord
  have hN1coord : Continuous (fun s : SummarySpace dx dz => s.N1) := by
    exact (continuous_fst.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hcoord
  have hmXcoord : Continuous (fun s : SummarySpace dx dz => s.mX) := by
    exact (continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hcoord
  have hM0 : Continuous (fun a : SummarySpace dx dz × SummarySpace dx dz =>
      matrixCLM (a.1.M0 - a.2.M0)) :=
    (matrixCLM_continuous (rows := dz) (cols := dx)).comp ((hM0coord.comp continuous_fst).sub
      (hM0coord.comp continuous_snd))
  have hM1 : Continuous (fun a : SummarySpace dx dz × SummarySpace dx dz =>
      matrixCLM (a.1.M1 - a.2.M1)) :=
    (matrixCLM_continuous (rows := dz) (cols := dx)).comp ((hM1coord.comp continuous_fst).sub
      (hM1coord.comp continuous_snd))
  have hN0 : Continuous (fun a : SummarySpace dx dz × SummarySpace dx dz =>
      matrixCLM (a.1.N0 - a.2.N0)) :=
    (matrixCLM_continuous (rows := dz) (cols := dx)).comp ((hN0coord.comp continuous_fst).sub
      (hN0coord.comp continuous_snd))
  have hN1 : Continuous (fun a : SummarySpace dx dz × SummarySpace dx dz =>
      matrixCLM (a.1.N1 - a.2.N1)) :=
    (matrixCLM_continuous (rows := dz) (cols := dx)).comp ((hN1coord.comp continuous_fst).sub
      (hN1coord.comp continuous_snd))
  have hmX : Continuous (fun a : SummarySpace dx dz × SummarySpace dx dz =>
      a.1.mX - a.2.mX) :=
    (hmXcoord.comp continuous_fst).sub (hmXcoord.comp continuous_snd)
  have hsqrt : Continuous (fun a : SummarySpace dx dz × SummarySpace dx dz =>
      Real.sqrt (∑ i, (a.1.mX i - a.2.mX i) ^ 2)) := by
    fun_prop (disch := assumption)
  exact (((hM0.norm.add hM1.norm).add hN0.norm).add hN1.norm).add hsqrt

/-- The complete observable-summary node, bundling the five population moments with the stated
continuous summary loss. -/
structure ObservableSummaryData (dx dz : ℕ) where
  summary : SummarySpace dx dz
  loss : SummarySpace dx dz → SummarySpace dx dz → ℝ
  loss_eq : loss = dS
  loss_continuous : Continuous (Function.uncurry loss)

-- @node: def:observable-summary
noncomputable def observableSummaryData : ObservableSummaryData dx dz :=
  ⟨obsSummary P, dS, rfl, dS_continuous dx dz⟩

noncomputable def observedProxyMoment {dx dz : ℕ} (s : SummarySpace dx dz) (t : Bool) :
    RectMatrix dz dx := if t then s.M1 else s.M0

noncomputable def observedOutcomeProxyMoment {dx dz : ℕ} (s : SummarySpace dx dz) (t : Bool) :
    RectMatrix dz dx := if t then s.N1 else s.N0

noncomputable def latentArmWeights {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    (t : Bool) : RectMatrix k k :=
  Matrix.diagonal fun u => P.real (latentCell u t) / P.real {w | w.T = t}

noncomputable def stackedProxyMoment {dx dz : ℕ} (s : SummarySpace dx dz) :
    RectMatrix (2 * dz) dx := fun i j =>
  if h : i.val < dz then s.M0 ⟨i.val, h⟩ j
  else s.M1 ⟨i.val - dz, by omega⟩ j

def armCount {n dx dz : ℕ} (t : Bool) (sample : Fin n → Obs dx dz) : ℕ :=
  (Finset.univ.filter fun i => (sample i).T = t).card

noncomputable def empiricalArmMatrix {n dx dz : ℕ} (weighted : Bool) (t : Bool)
    (sample : Fin n → Obs dx dz) : RectMatrix dz dx := fun a b =>
  (max 1 (armCount t sample) : ℝ)⁻¹ * ∑ i, if (sample i).T = t then
    (if weighted then (sample i).Y else 1) * (sample i).Z a * (sample i).X b else 0

/-- Total empirical summary, including the empty-arm zero branch.
    @realizes \(N_{t,n}\)(armCount) @realizes \(\widehat M_{t,n}\)(arm matrix)
    @realizes \(\widehat N_{t,n}\)(weighted arm matrix) @realizes \(\widehat m_{X,n}\)(sample mean)
    @realizes \(\widehat S_n\)(five empirical blocks) -/
-- @node: def:empirical-summary
noncomputable def empSummary {n dx dz : ℕ} (sample : Fin n → Obs dx dz) : SummarySpace dx dz where
  M0 := empiricalArmMatrix false false sample
  M1 := empiricalArmMatrix false true sample
  N0 := empiricalArmMatrix true false sample
  N1 := empiricalArmMatrix true true sample
  mX j := (n : ℝ)⁻¹ * ∑ i, (sample i).X j

/-- A supplied orthonormal signal basis and its spanning condition. @realizes \(V(P)\)(basis) -/
structure SignalBasis (dx k : ℕ) where
  V : RectMatrix dx k
  orthonormal : ∀ i j, (∑ a, V a i * V a j) = if i = j then 1 else 0

/-- Row space of the vertically stacked proxy moments. -/
noncomputable def signalRowspace {dx dz : ℕ} (s : SummarySpace dx dz) :
    Submodule ℝ (Euc dx) :=
  LinearMap.range (Matrix.toEuclideanLin s.M0.transpose) ⊔
    LinearMap.range (Matrix.toEuclideanLin s.M1.transpose)

/-- The supplied orthonormal columns span the stacked proxy row space. -/
def SignalBasis.SpansSignal {dx dz k : ℕ} (s : SummarySpace dx dz)
    (V : SignalBasis dx k) : Prop :=
  LinearMap.range (Matrix.toEuclideanLin V.V) = signalRowspace s

/-! The next three constructions jointly realize the compressed operator node. -/

/-- Compressed effect operator. @realizes \(\Delta Q(P)\)(Penrose compressed contrast) -/
noncomputable def compressedOperator {dx dz k : ℕ} (s : SummarySpace dx dz)
    (V : SignalBasis dx k) (_hV : V.SpansSignal s) : RectMatrix k k :=
  genuinePenroseInverse (s.M1 * V.V) * (s.N1 * V.V) -
    genuinePenroseInverse (s.M0 * V.V) * (s.N0 * V.V)

/-- Left spectral anchor. @realizes \(a(P)\)(mX transpose V) -/
noncomputable def leftAnchor {dx dz k : ℕ} (s : SummarySpace dx dz) (V : SignalBasis dx k) :
    Fin k → ℝ := fun j => ∑ i, s.mX i * V.V i j

/-- Right spectral anchor. @realizes \(c(P)\)(V transpose e1) -/
noncomputable def rightAnchor {dx k : ℕ} (V : SignalBasis dx k) : Fin k → ℝ :=
  fun j => ∑ i, V.V i j * firstBasis dx i

/-- All three constructions required by the compressed-operator definition, bundled together. -/
structure CompressedOperatorData (k : ℕ) where
  delta : RectMatrix k k
  left : Fin k → ℝ
  right : Fin k → ℝ

-- @node: def:compressed-operator
/-- The compressed effect operator and anchors attached to a model law and any orthonormal
basis spanning its stacked proxy row space. -/
noncomputable def compressedOperatorData {dx dz k : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (V : SignalBasis dx k) (hV : V.SpansSignal (obsSummary P)) : CompressedOperatorData k :=
  ⟨compressedOperator (obsSummary P) V hV,
    leftAnchor (obsSummary P) V, rightAnchor V⟩

/-- The labelled formula before validity is bundled. -/
noncomputable def quotientLawRaw (radius : ℝ) : AtomicLaw k radius :=
  ⟨latentMass P, latentEffect P⟩

-- @node: def:sample-experiment
/-- Observed iid experiment. @realizes \(\mathcal E_n\)(set of model product laws) -/
def sampleExperiment (n : ℕ) : Set (Measure (Fin n → Obs dx dz)) :=
  {Q | ∃ (P : Measure (FullData k dx dz)) (hP : IsProbabilityMeasure P),
    letI := hP
    Nonempty (UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) ∧
      Q = sampleLaw (n := n) P}

/-- Domain of a nominal confidence-set miscoverage level. -/
def MiscoverageDomain (alpha : ℝ) : Prop :=
  0 < alpha ∧ -- @realizes \(\alpha\)(strictly positive miscoverage)
  alpha < 1 / 2 -- @realizes \(\alpha\)(miscoverage below one half)

/-- Domain of a generic high-probability tail level. -/
def TailLevelDomain (eta : ℝ) : Prop :=
  0 < eta ∧ -- @realizes \(\eta\)(strictly positive tail level)
  eta < 1 / 2 -- @realizes \(\eta\)(tail level below one half)

/-- Domain of the simultaneous-concentration constant. -/
def ConcentrationConstantDomain (C0 : ℝ) : Prop :=
  1 ≤ C0 -- @realizes \(C_0\)(concentration constant at least one)

-- @env: S2
-- @realizes \(n\)(sample size) @realizes \(r_{n,\alpha}\)(summary radius)
-- @realizes \(E_P\)(summary deviation event)
variable {n : ℕ} {alpha eta C0 : ℝ}

/-- Simultaneous summary radius. -/
noncomputable def summaryRadius (n : ℕ) (alpha C0 L : ℝ) : ℝ :=
  C0 * L * Real.sqrt (Real.log (C0 / alpha) / n)

lemma summaryRadius_pos (n : ℕ) (alpha C0 L : ℝ) (hn : 0 < n)
    (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hC0 : 1 ≤ C0) (hL : 1 ≤ L) :
    0 < summaryRadius n alpha C0 L := by
  unfold summaryRadius
  have hdiv : 1 < C0 / alpha := by
    rw [one_lt_div halpha]
    linarith
  have hlog : 0 < Real.log (C0 / alpha) := Real.log_pos hdiv
  positivity
  -- @realizes \(r_{n,\alpha}\)(positive under core parameter domain)

/-- Summary concentration event. -/
def summaryEvent {n dx dz : ℕ} (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (C0 L alpha : ℝ) : Set (Fin n → Obs dx dz) :=
  {sample | dS (empSummary sample) (obsSummary P) ≤ summaryRadius n alpha C0 L}

-- @env: S3
variable {j : Fin (2 * k)}

-- @env: S4
-- @realizes \(m_\star\)(atom floor)
variable {mStar c C Cmod Clat : ℝ}

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
