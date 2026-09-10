import Causalean.Stat.Sample
import Causalean.Mathlib.CondDistrib
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Boundary thickness and estimability: common model

This file gives the paper's planar sharp-boundary law, its law-pinned side
functionals, the modeling assumptions, and the four model-class bundles.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- The bivariate assignment score. -/
abbrev Score := EuclideanSpace ℝ (Fin 2) -- @realizes X(carrier ℝ²)

/-- A latent potential-outcome unit `(Y(0),Y(1),X)`. -/
abbrev LatentUnit := ℝ × ℝ × Score
  -- @realizes Y(0)(carrier ℝ) @realizes Y(1)(carrier ℝ) @realizes X(latent score)

/-- One observed unit `(Y,X)`. -/
abbrev Observation := ℝ × Score -- @realizes O(pair (Y,X)) @realizes Y(carrier ℝ)

/-- An ordered sample of `n` observed units. -/
abbrev Sample (n : ℕ) := Fin n → Observation -- @realizes \mathcal D_n(carrier Oⁿ)

/-- A law and all law-dependent representatives used by the paper.  Equality
fields pin the score and observed laws to the latent law. -/
structure BoundaryLaw where
  latentLaw : Measure LatentUnit -- @realizes P(superpopulation law)
  observedOutcome : LatentUnit → ℝ -- @realizes Y(observed outcome map)
  treatment : LatentUnit → Fin 2 -- @realizes T(binary treatment carrier)
  observedLaw : Measure Observation -- @realizes O(induced observed law)
  scoreLaw : Measure Score -- @realizes P_{X}(score marginal law)
  region : Fin 2 → Set Score
    -- @realizes \mathcal A_0(control Borel region) @realizes \mathcal A_1(treated Borel region)
  region_measurable : ∀ t, MeasurableSet (region t)
  boundary_compact : IsCompact (frontier (region 0) ∩ frontier (region 1))
    -- @realizes \mathcal B(compact common boundary)
  observedLaw_eq : observedLaw = Measure.map (fun w => (observedOutcome w, w.2.2)) latentLaw
    -- @realizes O(pushforward of P by (Y,X))
  scoreLaw_eq : scoreLaw = Measure.map (fun w => w.2.2) latentLaw
    -- @realizes P_{X}(X-marginal of P)
  isProbability_latent : IsProbabilityMeasure latentLaw
  isProbability_observed : IsProbabilityMeasure observedLaw
  isProbability_score : IsProbabilityMeasure scoreLaw
  sideRegression : Fin 2 → Score → ℝ -- @realizes g_{t,P}(Borel representative carrier)
  sideRegression_measurable : ∀ t, Measurable (sideRegression t)
  sideTrace : Fin 2 → Score → ℝ -- @realizes \theta_{t,P}(boundary trace carrier)

/-- The known common assignment boundary. -/
def assignmentBoundary (P : BoundaryLaw) : Set Score :=
  frontier (P.region 0) ∩ frontier (P.region 1)
  -- @realizes \mathcal B(bd(A₀) ∩ bd(A₁))

/-- A law class with one fixed known complementary Borel assignment geometry. -/
def SharedAssignmentGeometry (laws : Set BoundaryLaw) (A0 A1 B : Set Score) : Prop :=
  MeasurableSet A0 ∧ MeasurableSet A1 ∧ A0 = A1ᶜ ∧
    B = frontier A0 ∩ frontier A1 ∧ IsCompact B ∧
    ∀ P ∈ laws, P.region 0 = A0 ∧ P.region 1 = A1 ∧ assignmentBoundary P = B

/-- The fixed complementary Borel geometry before any model class is formed. -/
def FixedAssignmentGeometry (A0 A1 B : Set Score) : Prop :=
  MeasurableSet A0 ∧ MeasurableSet A1 ∧ A0 = A1ᶜ ∧
    B = frontier A0 ∩ frontier A1 ∧ IsCompact B

/-- Restriction of a law set to one declared assignment geometry. -/
def lawsOnGeometry (laws : Set BoundaryLaw) (A0 A1 B : Set Score) : Set BoundaryLaw :=
  {P | P ∈ laws ∧ P.region 0 = A0 ∧ P.region 1 = A1 ∧ assignmentBoundary P = B}

/-- The one-sided restricted score measure. -/
noncomputable def restrictedScore (P : BoundaryLaw) (t : Fin 2) : Measure Score :=
  P.scoreLaw.restrict (P.region t)

/-- Closed support of the one-sided restricted score measure. -/
def sideSupport (P : BoundaryLaw) (t : Fin 2) : Set Score :=
  (restrictedScore P t).support
  -- @realizes \mathcal X_{t,P}(support of restricted score measure)

/-- Euclidean localization distance. -/
noncomputable def scoreDistance (x z : Score) : ℝ := dist x z
  -- @realizes d(Euclidean distance ‖x-z‖₂)

/-- The boundary trace contrast. -/
def traceContrast (P : BoundaryLaw) (x : Score) : ℝ :=
  P.sideTrace 1 x - P.sideTrace 0 x
  -- @realizes \tau_P(theta₁ minus theta₀)

/-- The observed joint law in `(X,Y)` order, used for disintegration. -/
noncomputable def scoreOutcomeLaw (P : BoundaryLaw) : Measure (Score × ℝ) :=
  P.observedLaw.map fun o => (o.2, o.1)

/-- One-sided mass of a boundary ball. -/
def localMass (P : BoundaryLaw) (t : Fin 2) (x : Score) (h : ℝ) : ℝ≥0∞ :=
  P.scoreLaw {z | z ∈ P.region t ∧ dist z x ≤ h}
  -- @realizes q_{t,P}(P{X∈A_t,d(X,x)≤h})

/-- Boundary locations whose minimum side mass is below `u`. -/
def thinSites (P : BoundaryLaw) (h : ℝ) (u : ℝ≥0∞) : Set Score :=
  {x | x ∈ assignmentBoundary P ∧ min (localMass P 0 x h) (localMass P 1 x h) ≤ u}

/-- The maximal separated cardinality of the thin-site set. -/
noncomputable def thinProfile (P : BoundaryLaw) (h : ℝ) (u : ℝ≥0∞) : ℕ∞ :=
  Metric.packingNumber (Real.toNNReal h) (thinSites P h u)
  -- @realizes \mathsf J_P(maximal h-separated thin-site cardinality)

-- @env: S1
variable (n : ℕ) -- @realizes n(sample size in ℕ)
variable (t : Fin 2) -- @realizes t(control/treatment side index)
variable (κbar κ L σ cm Cm h0 : ℝ)
  -- @realizes \overline\kappa(upper exponent endpoint)
  -- @realizes \kappa(exponent in (2,kappabar])
  -- @realizes L(positive Lipschitz and trace envelope)
  -- @realizes \sigma(positive noise scale)
  -- @realizes c_{m}(positive lower mass constant)
  -- @realizes C_{m}(thin-site threshold greater than c_m)
  -- @realizes h_0(localization radius in (0,1))

/-- Standing domains for the paper's fixed numerical parameters. -/
def AdmissibleBaseParameters (L σ cm κ h0 : ℝ) : Prop :=
  0 < L ∧ 0 < σ ∧ 0 < cm ∧ 2 < κ ∧ 0 < h0 ∧ h0 < 1
  -- @realizes L(L>0) @realizes \sigma(sigma>0) @realizes c_{m}(c_m>0)
  -- @realizes \kappa(kappa>2) @realizes h_0(0<h₀<1)

/-- Standing domain for an exponent upper endpoint. -/
def AdmissibleExponentRange (κbar κ : ℝ) : Prop :=
  2 < κbar ∧ 2 < κ ∧ κ ≤ κbar
  -- @realizes \overline\kappa(kappabar>2) @realizes \kappa(2<kappa≤kappabar)

-- @node: ass:iid-sampling
/-- The supplied sample law is the product of the observed law. -/
def IidSampling (P : BoundaryLaw) (sampleMeasure : Measure (Sample n)) : Prop :=
  sampleMeasure = Measure.pi (fun _ : Fin n => P.observedLaw)

-- @node: ass:sharp-assignment
/-- Treatment is the indicator of the treated assignment region. -/
def SharpAssignment (P : BoundaryLaw) : Prop :=
  ∀ᵐ w ∂P.latentLaw, (P.treatment w = 1 ↔ w.2.2 ∈ P.region 1)
  -- @realizes T(T=1{X∈A₁} P-a.s.)

-- @node: ass:consistency
/-- The observed response equals the selected potential outcome. -/
def Consistency (P : BoundaryLaw) : Prop :=
  ∀ᵐ w ∂P.latentLaw,
    P.observedOutcome w = if P.treatment w = 1 then w.2.1 else w.1
  -- @realizes Y(Y=T Y(1)+(1-T)Y(0) P-a.s.)

-- @node: ass:global-boundary-entropy
/-- The boundary has two-sided one-dimensional packing growth. -/
def GlobalBoundaryEntropy (P : BoundaryLaw) (h0 : ℝ) : Prop :=
  ∃ cB CB : ℝ, 0 < cB ∧ cB ≤ CB ∧
    ∀ h, 0 < h → h ≤ h0 →
      ENNReal.ofReal (cB / h) ≤ Metric.packingNumber (Real.toNNReal h) (assignmentBoundary P) ∧
      Metric.packingNumber (Real.toNNReal h) (assignmentBoundary P) ≤ ENNReal.ofReal (CB / h)
  -- @realizes \mathcal B(compact-curve h⁻¹ entropy bounds)

-- @node: ass:lipschitz-side-means
/-- Each side representative is Lipschitz on its near-boundary support. -/
def LipschitzSideMeans (P : BoundaryLaw) (L h0 : ℝ) : Prop :=
  ∀ t z, z ∈ sideSupport P t →
    (⨅ x ∈ assignmentBoundary P, ENNReal.ofReal (dist z x)) ≤ ENNReal.ofReal h0 →
    ∀ z', z' ∈ sideSupport P t →
      (⨅ x ∈ assignmentBoundary P, ENNReal.ofReal (dist z' x)) ≤ ENNReal.ofReal h0 →
      |P.sideRegression t z - P.sideRegression t z'| ≤ L * dist z z'
  -- @realizes g_{t,P}(L-Lipschitz on near-boundary support)

-- @node: ass:bounded-side-traces
/-- Boundary traces lie in the fixed envelope. -/
def BoundedSideTraces (P : BoundaryLaw) (L : ℝ) : Prop :=
  ∀ t x, x ∈ assignmentBoundary P →
    Tendsto (P.sideRegression t) (𝓝[sideSupport P t] x) (𝓝 (P.sideTrace t x)) ∧
    |P.sideTrace t x| ≤ L
  -- @realizes \theta_{t,P}(absolute trace bounded by L)

-- @node: ass:gaussian-errors
/-- One conditional kernel is centered, integrable and sub-Gaussian off one
restricted-score null set per side. -/
def CenteredSubGaussianKernel (P : BoundaryLaw) (σ : ℝ) : Prop :=
  0 < σ ∧ ∃ R : Kernel Score ℝ,
    IsMarkovKernel R ∧ (scoreOutcomeLaw P).IsCondKernel R ∧
    ∀ t : Fin 2, ∃ N : Set Score,
    restrictedScore P t N = 0 ∧
    ∀ z ∈ sideSupport P t \ N,
      Integrable (fun y : ℝ => y - P.sideRegression t z) (R z) ∧
      (∫ y, y - P.sideRegression t z ∂R z) = 0 ∧
      (∫ y, y ∂R z) = P.sideRegression t z ∧
      ∀ a : ℝ, (∫⁻ y, ENNReal.ofReal (Real.exp (a * (y - P.sideRegression t z))) ∂R z) ≤
        ENNReal.ofReal (Real.exp (σ ^ 2 * a ^ 2 / 2))
  -- @realizes g_{t,P}(kernel centered at side regression)
  -- @realizes \sigma(conditional sub-Gaussian proxy)

-- @node: ass:polynomial-lower-mass
/-- Uniform polynomial lower local mass on both assignment sides. -/
def PolynomialLowerMass (P : BoundaryLaw) (cm κ h0 : ℝ) : Prop :=
  ∀ x ∈ assignmentBoundary P, ∀ t : Fin 2, ∀ h, 0 < h → h ≤ h0 →
    ENNReal.ofReal (cm * h ^ κ) ≤ localMass P t x h
  -- @realizes q_{t,P}(q_t,P≥c_m h^kappa)

-- @node: ass:isolated-thin-profile-upper
/-- Upper envelope describing a single persistent thin region. -/
def IsolatedThinProfileUpper (P : BoundaryLaw) (Cm κ h0 : ℝ) : Prop :=
  ∃ Ciso > 0, ∀ h, 0 < h → h ≤ h0 → ∀ u : ℝ≥0∞,
    ENNReal.ofReal (Cm * h ^ κ) ≤ u → u ≤ 1 →
      thinProfile P h u ≤ ENNReal.ofReal (Ciso * (1 + h⁻¹ * (u.toReal / h ^ 2) ^ (1 / (κ - 2))))

-- @node: ass:isolated-thin-site
/-- At every local scale there is at least one polynomially thin site. -/
def IsolatedThinSite (P : BoundaryLaw) (Cm κ h0 : ℝ) : Prop :=
  ∀ h, 0 < h → h ≤ h0 → 1 ≤ thinProfile P h (ENNReal.ofReal (Cm * h ^ κ))

-- @node: ass:pervasive-thin-sites
/-- Polynomially thin sites occur at order `h⁻¹` many separated locations. -/
def PervasiveThinSites (P : BoundaryLaw) (Cm κ h0 : ℝ) : Prop :=
  ∃ cJ > 0, ∀ h, 0 < h → h ≤ h0 →
    ENNReal.ofReal (cJ / h) ≤ thinProfile P h (ENNReal.ofReal (Cm * h ^ κ))

-- @node: ass:declared-modulus-lower-mass
/-- A declared monotone modulus lower-bounds both side masses. -/
def DeclaredModulusLowerMass (P : BoundaryLaw) (m : ℝ → ℝ≥0∞) (h0 : ℝ) : Prop :=
  (∀ h h', 0 < h → h ≤ h' → h' ≤ h0 → m h ≤ m h') ∧
    ∀ x ∈ assignmentBoundary P, ∀ t : Fin 2, ∀ h,
    0 < h → h ≤ h0 → m h ≤ localMass P t x h
  -- @realizes m(nondecreasing only on 0<h≤h₀)

-- @node: ass:declared-profile-lower
/-- A declared profile is a uniform lower envelope for the law's thin profile. -/
def DeclaredProfileLower (P : BoundaryLaw) (Jminus : ℝ → ℝ≥0∞ → ℕ∞) (h0 : ℝ) : Prop :=
  ∀ h, 0 < h → h ≤ h0 → ∀ u : ℝ≥0∞, u ≤ 1 → Jminus h u ≤ thinProfile P h u
  -- @realizes \mathsf J_{-}(declared lower packing envelope)

-- @node: def:modulus-profile-class
/-- Laws satisfying the arbitrary-modulus and lower-profile conditions. -/
structure ModulusProfileClass (P : BoundaryLaw) (L σ h0 : ℝ)
    (m : ℝ → ℝ≥0∞) (Jminus : ℝ → ℝ≥0∞ → ℕ∞) : Prop where
  parameters : 0 < L ∧ 0 < σ ∧ 0 < h0 ∧ h0 < 1
  sharp : SharpAssignment P
  consistency : Consistency P
  entropy : GlobalBoundaryEntropy P h0
  lipschitz : LipschitzSideMeans P L h0
  bounded : BoundedSideTraces P L
  errors : CenteredSubGaussianKernel P σ
  lowerMass : DeclaredModulusLowerMass P m h0
  lowerProfile : DeclaredProfileLower P Jminus h0
  -- @realizes \mathcal P(m,\mathsf J_{-})(member-property law class)

-- @node: def:base-thickness-class
/-- The polynomial-thickness base class. -/
structure BaseThicknessClass (P : BoundaryLaw) (L σ cm κ h0 : ℝ) : Prop where
  parameters : AdmissibleBaseParameters L σ cm κ h0
  sharp : SharpAssignment P
  consistency : Consistency P
  entropy : GlobalBoundaryEntropy P h0
  lipschitz : LipschitzSideMeans P L h0
  bounded : BoundedSideTraces P L
  errors : CenteredSubGaussianKernel P σ
  lowerMass : PolynomialLowerMass P cm κ h0
  -- @realizes \mathcal P_{\kappa}^{\mathrm{base}}(polynomial-thickness law class)

-- @node: def:isolated-thinning-class
/-- The isolated-thinning subclass. -/
structure IsolatedThinningClass (P : BoundaryLaw) (L σ cm Cm κ h0 : ℝ) : Prop where
  threshold : cm < Cm
  base : BaseThicknessClass P L σ cm κ h0
  upperProfile : IsolatedThinProfileUpper P Cm κ h0
  thinSite : IsolatedThinSite P Cm κ h0
  -- @realizes \mathcal P_{\kappa}^{\mathrm{iso}}(isolated-thinning subclass)

-- @node: def:pervasive-thinning-class
/-- The pervasive-thinning subclass. -/
structure PervasiveThinningClass (P : BoundaryLaw) (L σ cm Cm κ h0 : ℝ) : Prop where
  threshold : cm < Cm
  base : BaseThicknessClass P L σ cm κ h0
  pervasive : PervasiveThinSites P Cm κ h0
  -- @realizes \mathcal P_{\kappa}^{\mathrm{perv}}(pervasive-thinning subclass)

/-- Set-level view of the polynomial base class. -/
def baseLaws (L σ cm κ h0 : ℝ) : Set BoundaryLaw :=
  {P | BaseThicknessClass P L σ cm κ h0}

/-- Set-level view of the isolated-thinning class. -/
def isolatedLaws (L σ cm Cm κ h0 : ℝ) : Set BoundaryLaw :=
  {P | IsolatedThinningClass P L σ cm Cm κ h0}

/-- Set-level view of the pervasive-thinning class. -/
def pervasiveLaws (L σ cm Cm κ h0 : ℝ) : Set BoundaryLaw :=
  {P | PervasiveThinningClass P L σ cm Cm κ h0}

/-- Set-level view of an arbitrary-modulus lower-profile class. -/
def modulusProfileLaws (L σ h0 : ℝ) (m : ℝ → ℝ≥0∞)
    (Jminus : ℝ → ℝ≥0∞ → ℕ∞) : Set BoundaryLaw :=
  {P | ModulusProfileClass P L σ h0 m Jminus}

/-- One declared exponent/lower-profile/upper-profile triple. -/
structure ProfileTriple (κbar : ℝ) where
  exponent : ℝ -- @realizes \kappa(real exponent carrier)
  exponent_mem : 2 < exponent ∧ exponent ≤ κbar
    -- @realizes \kappa(2<kappa≤kappabar) @realizes \overline\kappa(common upper endpoint)
  lower : ℝ → ℝ≥0∞ → ℕ∞
  upper : ℝ → ℝ≥0∞ → ℕ∞
  -- @realizes \kappa(triple exponent)
  -- @realizes \mathsf J_{-}(triple lower profile)
  -- @realizes \mathsf J_{+}(triple upper profile)

/-- Membership in a profile-bracketed component class. -/
def ProfileBracket {κbar : ℝ} (P : BoundaryLaw) (a : ProfileTriple κbar)
    (L σ cm h0 : ℝ) : Prop :=
  BaseThicknessClass P L σ cm a.exponent h0 ∧
    ∀ h, 0 < h → h ≤ h0 → ∀ u : ℝ≥0∞, u ≤ 1 →
      a.lower h u ≤ thinProfile P h u ∧ thinProfile P h u ≤ a.upper h u

/-- A declared triangular range bundled with the required nonempty union. -/
structure TriangularProfileIndex (κbar L σ cm h0 : ℝ) where
  profiles : Set (ProfileTriple κbar)
  union_nonempty : (Set.iUnion fun a : profiles =>
    {P : BoundaryLaw | ProfileBracket P a.1 L σ cm h0}).Nonempty

-- @node: def:triangular-profile-union
/-- The nonempty union over a declared triangular profile range. -/
def triangularProfileUnion {κbar L σ cm h0 : ℝ}
    (Λ : TriangularProfileIndex κbar L σ cm h0) : Set BoundaryLaw :=
  {P | ∃ a ∈ Λ.profiles, ProfileBracket P a L σ cm h0}
  -- @realizes \Lambda_n(declared profiles bundled with nonempty union)
  -- @realizes \mathcal P_n(\Lambda_n)(union of bracketed base classes)

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
