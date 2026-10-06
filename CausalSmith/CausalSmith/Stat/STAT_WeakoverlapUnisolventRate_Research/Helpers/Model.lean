module
public import Causalean.Stat.Nonparametric.Approximation.Holder.Defs
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Stat.Nonparametric.Approximation.Holder.CubeExtension
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Weak-overlap response model

The causal completion and the observed data law use explicit product spaces. This
is a bypass-justified use of product measures: `POSystem` is regime-indexed,
whereas the present result concerns a random-design regression experiment.
`BackdoorEstimationSystem` assumes strict overlap. The local Hölder conditions
use intrinsic coordinate jets on the closed cube. Ambient representatives arise
only through the separate extension theorem.
-/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

-- @env: S1
variable (d : ℕ) -- @realizes d(natural covariate dimension; positive in theorem hypotheses)
variable (β : ℝ) -- @realizes beta(real smoothness order; range via ModelParameterDomain)
variable (B : ℝ) -- @realizes B(real outcome bound; range via ModelParameterDomain)
variable (L : ℝ) -- @realizes L(real Hölder radius; range via ModelParameterDomain)
variable (C : ℝ) -- @realizes C(real global-tail constant; range via ModelParameterDomain)
variable (c_f : ℝ) -- @realizes c_f(real density lower bound; range via ModelParameterDomain)
variable (γ : ℝ) -- @realizes gamma(overlap exponent in compact adaptation range)
variable (γ_min : ℝ)
  -- @realizes gamma_min(lower range endpoint; range via AdaptationParameterDomain)
variable (γ_max : ℝ) -- @realizes gamma_max(upper endpoint; ≥gamma_min in theorem hypotheses)
variable (n : ℕ) -- @realizes n(natural sample size)

/-- Stated parameter spaces for a fixed model class. For [the stated inputs and conditions](hyp:d,β,B,L,C,c_f), [the `ModelParameterDomain` object being defined](goal). -/
def ModelParameterDomain (d : ℕ) (β B L C c_f : ℝ) : Prop :=
  1 ≤ d ∧
  1 < β ∧ -- @realizes beta(beta > 1)
  0 < B ∧ -- @realizes B(B > 0)
  0 < L ∧ -- @realizes L(L > 0)
  1 ≤ C ∧ -- @realizes C(C ≥ 1)
  0 < c_f ∧ c_f ≤ 1 -- @realizes c_f(0 < c_f ≤ 1)

/-- Stated compact range of overlap exponents. For [the stated inputs and conditions](hyp:γ_min,γ_max), [the `AdaptationParameterDomain` object being defined](goal). -/
def AdaptationParameterDomain (γ_min γ_max : ℝ) : Prop :=
  1 < γ_min ∧ γ_min < γ_max -- @realizes gamma_min(gamma_min > 1)

/-- Covariate cube. For [the stated inputs and conditions](hyp:d), [the `cube` object being defined](goal). -/
def cube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) -- @realizes mathcalX(Borel cube [0,1]^d)

/-- Fixed compact adaptation range. For [the stated inputs and conditions](hyp:γ_min,γ_max,_hdom), [the `adaptationRange` object being defined](goal). -/
noncomputable def adaptationRange (γ_min γ_max : ℝ)
    (_hdom : AdaptationParameterDomain γ_min γ_max) : Set ℝ :=
  Set.Icc γ_min γ_max -- @realizes Gamma(interval [gamma_min,gamma_max])

/-- Local polynomial degree. For [the stated inputs and conditions](hyp:β), [the `polynomialDegree` object being defined](goal). -/
noncomputable def polynomialDegree (β : ℝ) : ℕ := ⌈β⌉₊ - 1 -- @realizes m(ceil beta minus one)

/-- Effective covariate dimension. For [the stated inputs and conditions](hyp:d,γ), [the `effectiveDimension` object being defined](goal). -/
noncomputable def effectiveDimension (d : ℕ) (γ : ℝ) : ℝ :=
  (d : ℝ) * γ / (γ - 1) -- @realizes Dgamma(d gamma/(gamma-1))

/-- Oracle mesh width. For [the stated inputs and conditions](hyp:d,n,β,γ), [the `oracleMesh` object being defined](goal). -/
noncomputable def oracleMesh (d n : ℕ) (β γ : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / (2 * β + effectiveDimension d γ))
  -- @realizes hgamman(n^(-1/(2 beta+Dgamma)))

/-- Oracle risk scale. For [the stated inputs and conditions](hyp:d,n,β,γ), [the `oracleRate` object being defined](goal). -/
noncomputable def oracleRate (d n : ℕ) (β γ : ℝ) : ℝ :=
  (oracleMesh d n β γ) ^ β -- @realizes rgamman(hgamman^beta)

/-- The oracle mesh is interpreted on the model's parameter domain. For [the stated inputs and conditions](hyp:d,n,β,γ), [the `OracleMeshDomain` object being defined](goal). -/
def OracleMeshDomain (d n : ℕ) (β γ : ℝ) : Prop :=
  1 ≤ d ∧ 1 ≤ n ∧ 1 < β ∧ 1 < γ

/-- The formula for the oracle mesh has the stated range on its parameter domain. [For the stated inputs and conditions](hyp:d,n,β,γ,hdom), [the asserted conclusion holds](goal). -/
lemma oracleMesh_mem_Ioc (d n : ℕ) (β γ : ℝ)
    (hdom : OracleMeshDomain d n β γ) :
    oracleMesh d n β γ ∈ Set.Ioc (0 : ℝ) 1 := by
  rcases hdom with ⟨hd, hn, hβ, hγ⟩
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hn_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hdim : 0 < effectiveDimension d γ := by
    unfold effectiveDimension
    positivity
  have hden : 0 < 2 * β + effectiveDimension d γ := by positivity
  have hexp : -(1 : ℝ) / (2 * β + effectiveDimension d γ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · norm_num
    · positivity
  constructor
  · unfold oracleMesh
    positivity
  · unfold oracleMesh
    exact Real.rpow_le_one_of_one_le_of_nonpos hn_real hexp
  -- @realizes hgamman(0 < hgamman ≤ 1 on the model domain)

/-- One observation `(X,A,Y)`. For [the stated inputs and conditions](hyp:d), [the `Obs` object being defined](goal). -/
-- @env: S2
abbrev Obs (d : ℕ) := (Fin d → ℝ) × Bool × ℝ
  -- @realizes X(covariate vector carrier Fin d→ℝ)
  -- @realizes A(binary treatment carrier Bool)
  -- @realizes Y(real observed outcome carrier)
  -- @realizes Z(observed triple)

/-- Completion `(X,A,Y(0),Y(1),Y)`. For [the stated inputs and conditions](hyp:d), [the `Completion` object being defined](goal). -/
abbrev Completion (d : ℕ) := (Fin d → ℝ) × Bool × ℝ × ℝ × ℝ
  -- @realizes Y0(real control potential outcome) -- @realizes Y1(real treated potential outcome)

/-- Observable projection of the causal completion. For [the stated inputs and conditions](hyp:ω), [the `observed` object being defined](goal). -/
def observed {d : ℕ} (ω : Completion d) : Obs d :=
  (ω.1, ω.2.1, ω.2.2.2.2)
  -- @realizes X(first coordinate)
  -- @realizes A(binary second coordinate)
  -- @realizes Y(observed last coordinate)

/-- Covariate marginal of an observed law. For [the stated inputs and conditions](hyp:P), [the `covariateLaw` object being defined](goal). -/
noncomputable def covariateLaw {d : ℕ} (P : Measure (Obs d)) : Measure (Fin d → ℝ) :=
  P.map Prod.fst

/-- Covariate density, using the Radon–Nikodym derivative. For [the stated inputs and conditions](hyp:P,x), [the `covariateDensity` object being defined](goal). -/
noncomputable def covariateDensity {d : ℕ} (P : Measure (Obs d))
    (x : Fin d → ℝ) : ℝ :=
  ((covariateLaw P).rnDeriv (volume.restrict (cube d)) x).toReal -- @realizes f(dP_X/dx)

/-- A propensity version obtained from the conditional treatment kernel. For [the stated inputs and conditions](hyp:P,x), [the `propensity` object being defined](goal). -/
noncomputable def propensity {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (x : Fin d → ℝ) : ℝ :=
  (condDistrib (fun z : Obs d => z.2.1) (fun z => z.1) P x {true}).toReal
  -- @realizes e(conditional treatment probability)

/-- Density of the treated covariate distribution, normalized by the
probability of treatment when that probability is positive. For [the stated inputs and conditions](hyp:P,hA,x), [the `treatedCovariateDensity` object being defined](goal). -/
-- keep: realizes the frozen S2 design-diagnostic symbol g1 with its nonnegative range.
noncomputable def treatedCovariateDensity {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P]
    (hA : 0 < P.real {z : Obs d | z.2.1 = true})
    (x : Fin d → ℝ) : NNReal :=
  ⟨propensity P x * covariateDensity P x /
      P.real {z : Obs d | z.2.1 = true}, by
    exact div_nonneg
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (le_of_lt hA)⟩
  -- @realizes g1(nonnegative e_P(x) f(x) / P(A=1), with P(A=1)>0)

/-- Conditional treated response distribution. For [the stated inputs and conditions](hyp:P,x), [the `treatedKernel` object being defined](goal). -/
noncomputable def treatedKernel {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (x : Fin d → ℝ) : Measure ℝ :=
  condDistrib (fun z : Obs d => z.2.2) (fun z => (z.1, z.2.1)) P (x, true)

/-- Treated conditional regression. For [the stated inputs and conditions](hyp:P,x), [the `treatedRegression` object being defined](goal). -/
noncomputable def treatedRegression {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (x : Fin d → ℝ) : ℝ :=
  ∫ y, y ∂treatedKernel P x

/-- Bounds on within-set coordinate jets on an arbitrary covariate domain. For [the stated inputs and conditions](hyp:S,g,β,L), [the `HolderDerivBoundOn` object being defined](goal). -/
def HolderDerivBoundOn {d : ℕ} (S : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → ℝ) (β L : ℝ) : Prop :=
  Causalean.Mathlib.Analysis.Calculus.CubeExtension.DerivBoundOn
    S (polynomialDegree β) L g
  -- @realizes g(bounded coordinate derivatives)

/-- Top-order within-set coordinate-jet modulus on a covariate domain. For [the stated inputs and conditions](hyp:S,g,β,L), [the `HolderTopModulusOn` object being defined](goal). -/
def HolderTopModulusOn {d : ℕ} (S : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → ℝ) (β L : ℝ) : Prop :=
  Causalean.Mathlib.Analysis.Calculus.CubeExtension.TopHolderOn
    S (polynomialDegree β) (β - (polynomialDegree β : ℝ)) L g

-- @node: ass:holder-derivative-bound
/-- Maximum over coordinate partial derivatives through degree `ceil β - 1`. For [the stated inputs and conditions](hyp:g,β,L), [the `HolderDerivBound` object being defined](goal). -/
def HolderDerivBound {d : ℕ} (g : (Fin d → ℝ) → ℝ) (β L : ℝ) : Prop :=
  HolderDerivBoundOn (cube d) g β L

-- @node: ass:holder-modulus
/-- Maximum over top-order coordinate partial Hölder moduli. For [the stated inputs and conditions](hyp:g,β,L), [the `HolderTopModulus` object being defined](goal). -/
def HolderTopModulus {d : ℕ} (g : (Fin d → ℝ) → ℝ) (β L : ℝ) : Prop :=
  HolderTopModulusOn (cube d) g β L

/-- Intrinsic Hölder class on a specified cube, including Dorn's original cube. For [the stated inputs and conditions](hyp:S,β,L,g), [the `HolderBallOn` object being defined](goal). -/
abbrev HolderBallOn {d : ℕ} (S : Set (Fin d → ℝ))
    (β L : ℝ) (g : (Fin d → ℝ) → ℝ) : Prop :=
  Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
    S (polynomialDegree β) (β - (polynomialDegree β : ℝ)) L g

-- @node: def:holder
/-- The response itself belongs to the intrinsic Hölder ball on the closed
covariate cube; no outside extension is selected as a model member. -/
structure HolderBall {d : ℕ} (β L : ℝ) (g : (Fin d → ℝ) → ℝ) : Prop where
  regularity : ContDiffOn ℝ (⌈β⌉₊ - 1) g (cube d) -- @realizes HbetaL(C^m member)
  derivBound : HolderDerivBound g β L -- @realizes HbetaL(derivative-bound member)
  modulus : HolderTopModulus g β L -- @realizes HbetaL(top-derivative modulus member)

/-- The paper's intrinsic ball is exactly the within-cube ball of the
cube-extension library. [For the stated inputs and conditions](hyp:d,β,L,g,h), [the asserted conclusion holds](goal). -/
lemma HolderBall.toIntrinsic {d : ℕ} {β L : ℝ}
    {g : (Fin d → ℝ) → ℝ} (h : HolderBall β L g) :
    Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
      (cube d) (polynomialDegree β) (β - (polynomialDegree β : ℝ)) L g :=
  ⟨h.regularity, h.derivBound, h.modulus⟩

-- @node: ass:iid
/-- The sample law is the iid product of the observed law. For [the stated inputs and conditions](hyp:Q,P), [the `IIDSampleLaw` object being defined](goal). -/
def IIDSampleLaw {d n : ℕ} (Q : Measure (Fin n → Obs d))
    (P : Measure (Obs d)) : Prop :=
  Q = Measure.pi (fun _ : Fin n => P) -- @realizes Dn(iid sample product law)

-- @node: ass:density
/-- Covariate density bounded below relative to volume on the cube. For [the stated inputs and conditions](hyp:P,c_f), [the `CovariateDensityLowerBound` object being defined](goal). -/
def CovariateDensityLowerBound {d : ℕ} (P : Measure (Obs d))
    (c_f : ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict (cube d), c_f ≤ covariateDensity P x
  -- @realizes f(Radon-Nikodym density with lower bound)

-- @node: ass:consistency
/-- Observed outcome equals the selected potential outcome. For [the stated inputs and conditions](hyp:Pc), [the `OutcomeConsistency` object being defined](goal). -/
def OutcomeConsistency {d : ℕ} (Pc : Measure (Completion d)) : Prop :=
  ∀ᵐ ω ∂Pc, ω.2.2.2.2 = if ω.2.1 then ω.2.2.2.1 else ω.2.2.1
  -- @realizes Y0(control potential outcome) -- @realizes Y1(treated potential outcome)

-- @node: ass:exchangeability
/-- Potential outcomes and treatment are conditionally independent given `X`. For [the stated inputs and conditions](hyp:Pc), [the `CondExchangeable` object being defined](goal). -/
def CondExchangeable {d : ℕ} (Pc : Measure (Completion d))
    [IsFiniteMeasure Pc] : Prop :=
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (fun ω : Completion d => ω.1) inferInstance)
    (Measurable.comap_le (by fun_prop : Measurable (fun ω : Completion d => ω.1)))
    (fun ω : Completion d => (ω.2.2.1, ω.2.2.2.1)) (fun ω => ω.2.1) Pc

-- @node: ass:global-tail
/-- Polynomial lower-propensity tail under the covariate law. For [the stated inputs and conditions](hyp:P,e,C,γ), [the `GlobalPropensityTail` object being defined](goal). -/
def GlobalPropensityTail {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (e : (Fin d → ℝ) → ℝ) (C γ : ℝ) : Prop :=
  (∀ᵐ x ∂covariateLaw P, e x = propensity P x) ∧
    -- @realizes e(conditional treatment probability version)
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (covariateLaw P).real {x | e x ≤ t} ≤ C * t ^ (γ - 1)
    -- @realizes e(global tail of propensity)

-- @node: ass:bounded-potential-outcomes
/-- Bounded treated mean and conditionally sub-Gaussian treated residual. For [the stated inputs and conditions](hyp:P,B), [the `BoundedMeanSubGaussianResidual` object being defined](goal). -/
def BoundedMeanSubGaussianResidual {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (B : ℝ) : Prop :=
  ∀ᵐ x ∂covariateLaw P,
    |treatedRegression P x| ≤ B ∧
    ∀ t : ℝ,
      Integrable (fun y : ℝ => Real.exp (t * (y - treatedRegression P x)))
        (treatedKernel P x) ∧
      mgf (fun y : ℝ => y - treatedRegression P x)
        (treatedKernel P x) t ≤ Real.exp (B ^ 2 * t ^ 2 / 2)

-- @node: ass:holder-response
/-- The potential-outcome response has the designated Hölder representative. For [the stated inputs and conditions](hyp:Pc,μ₁,β,L), [the `HolderResponse` object being defined](goal). -/
def HolderResponse {d : ℕ} (Pc : Measure (Completion d))
    (μ₁ : (Fin d → ℝ) → ℝ) (β L : ℝ) : Prop :=
  HolderBall β L μ₁ ∧
  (fun ω : Completion d => μ₁ ω.1) =ᵐ[Pc]
    Pc[(fun ω : Completion d => ω.2.2.2.1) | MeasurableSpace.comap (fun ω => ω.1) inferInstance]
  -- @realizes mu1(continuous Hölder representative of E[Y1|X])

-- @node: def:model
/-- Global-tail causal model with sub-Gaussian treated residuals. -/
structure GlobalTailModel {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ) : Prop where
  cubeSupport : covariateLaw (Pc.map observed) (cube d) = 1
    -- @realizes X(covariate law supported on the cube)
  covariateAC : covariateLaw (Pc.map observed) ≪ volume.restrict (cube d)
    -- @realizes f(covariate law absolutely continuous with respect to cube volume)
  density : CovariateDensityLowerBound (Pc.map observed) c_f
  consistency : OutcomeConsistency Pc
  exchangeability : CondExchangeable Pc
  tail : GlobalPropensityTail (Pc.map observed) e C γ
  outcome : BoundedMeanSubGaussianResidual (Pc.map observed) B
  smooth : HolderResponse Pc μ₁ β L

/-- Observed laws admitting a causal completion in the model. For [the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ), [the `ModelClass` object being defined](goal). -/
def ModelClass (d : ℕ) (β B L C c_f γ : ℝ) : Set (Measure (Obs d)) :=
  {P | ModelParameterDomain d β B L C c_f ∧ 1 < γ ∧
    ∃ (Pc : Measure (Completion d)) (_ : IsProbabilityMeasure Pc)
    (μ₁ e : (Fin d → ℝ) → ℝ),
    P = Pc.map observed ∧ GlobalTailModel β B L C c_f γ Pc μ₁ e}
  -- @realizes P(observed probability law with causal completion)
  -- @realizes Pgamma(class of observed laws)

/-- A chosen Hölder representative for a law in the model class. For [the stated inputs and conditions](hyp:P,hP), [the `responseOf` object being defined](goal). -/
noncomputable def responseOf {d : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) (hP : P ∈ ModelClass d β B L C c_f γ) :
    (Fin d → ℝ) → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hP.2.2))

/-- Euclidean closed ball, distinct from the sup-norm covariate cube. For [the stated inputs and conditions](hyp:x₀,h), [the `ball2` object being defined](goal). -/
def ball2 {d : ℕ} (x₀ : Fin d → ℝ) (h : ℝ) : Set (Fin d → ℝ) :=
  {x | (∑ i, (x i - x₀ i) ^ 2) ≤ h ^ 2}

/-- A source-law tuple carries the observed law and the selected treated mean,
control mean, and pointwise propensity representative. For [the stated inputs and conditions](hyp:d), [the `DornSourceLaw` object being defined](goal). -/
abbrev DornSourceLaw (d : ℕ) :=
  Measure (Obs d) × ((Fin d → ℝ) → ℝ) ×
    ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)

/-- Dorn's original covariate cube. For [the stated inputs and conditions](hyp:d), [the `dornCube` object being defined](goal). -/
def dornCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

/-- A selected propensity version for a probability law on a specified cube. For [the stated inputs and conditions](hyp:S,P,e), [the `DornSelectedPropensity` object being defined](goal). -/
def DornSelectedPropensity {d : ℕ} (S : Set (Fin d → ℝ))
    (P : Measure (Obs d)) (e : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ hP : IsProbabilityMeasure P,
    letI : IsProbabilityMeasure P := hP
    Measurable e ∧
    (∀ x ∈ S, e x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ᵐ x ∂covariateLaw P, e x = propensity P x ∧ 0 < e x ∧ e x < 1)

-- @node: def:dorn-a3
/-- Dorn's A3 is a property of a nonempty family and its selected pointwise
propensity versions. Its constants are common to every family member. For [the stated inputs and conditions](hyp:S,𝔓), [the `DornA3` object being defined](goal). -/
noncomputable def DornA3 {d : ℕ} (S : Set (Fin d → ℝ))
    (𝔓 : Set (DornSourceLaw d)) : Prop :=
  𝔓.Nonempty ∧
  (∀ z ∈ 𝔓, covariateLaw z.1 S = 1) ∧
  (∀ z ∈ 𝔓, DornSelectedPropensity S z.1 z.2.2.2) ∧
  ∃ ρ ν h₀ : ℝ, 0 < ρ ∧ 0 < ν ∧ 0 < h₀ ∧
    ∀ z ∈ 𝔓, ∀ x₀ ∈ S, ∀ h ∈ Set.Ioc (0 : ℝ) h₀,
      ν < (covariateLaw z.1).real
        ({x | z.2.2.2 x ≥
            ρ * sSup (z.2.2.2 '' (ball2 x₀ h ∩ S))} ∩ ball2 x₀ h) /
          (covariateLaw z.1).real (ball2 x₀ h)
  -- @realizes A3Dorn(nonempty family, selected versions, common constants)

/-- Singleton abbreviation for the displayed law and selected propensity on
the paper's unit cube. For [the stated inputs and conditions](hyp:P,e), [the `DornA3OnCube` object being defined](goal). -/
noncomputable def DornA3OnCube {d : ℕ} (P : Measure (Obs d))
    (e : (Fin d → ℝ) → ℝ) : Prop :=
  DornA3 (cube d) ({(P, (fun _ => 0), (fun _ => 0), e)} : Set (DornSourceLaw d))

/-- The numerical local anti-concentration clause of Dorn's A3 for one displayed
propensity on the paper's cube. This clause deliberately does not impose the
separate selected-propensity requirement that `e < 1` almost surely. For [the stated inputs and conditions](hyp:P,e), [the `DornA3AntiConcentrationOnCube` object being defined](goal). -/
noncomputable def DornA3AntiConcentrationOnCube {d : ℕ} (P : Measure (Obs d))
    (e : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ ρ ν h₀ : ℝ, 0 < ρ ∧ 0 < ν ∧ 0 < h₀ ∧
    ∀ x₀ ∈ cube d, ∀ h ∈ Set.Ioc (0 : ℝ) h₀,
      ν < (covariateLaw P).real
        ({x | e x ≥ ρ * sSup (e '' (ball2 x₀ h ∩ cube d))} ∩ ball2 x₀ h) /
          (covariateLaw P).real (ball2 x₀ h)
end CausalSmith.Stat.WeakOverlap
