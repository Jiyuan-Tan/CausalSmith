module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Relation

/-! Atomic count shift models and observable factorial moments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @env: S1
variable {p M n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
-- @realizes p(finite coordinate count) @realizes [p](Fin p)
-- @realizes M(intervention count) @realizes \mathcal E(Fin (M+1), control 0)
-- @realizes n(replicates per environment)

/-- The zero diagonal and acyclic causal support of the mechanism. -/
-- @node: ass:acyclic-mechanism
def AcyclicMechanism (A : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  (∀ i, A i i = 0) ∧ ∀ i, ¬ Relation.TransGen (fun j k => A k j ≠ 0) i i

/-- Each intervention changes one latent intercept. -/
-- @node: ass:atomic-mean-shift
def AtomicMeanShift (η : Fin (M + 1) → Fin p → ℝ) (α : Fin M → ℝ)
    (t : Fin M → Fin p) : Prop :=
  ∀ m, (fun i => η m.succ i - η 0 i) = α m • Pi.single (t m) 1
  -- @realizes e_j(Pi.single canonical basis)

-- @node: ass:nonvanishing-strength
def NonvanishingStrength (α : Fin M → ℝ) : Prop := ∀ m, α m ≠ 0

/-- Positive definite Gaussian disturbance in every environment. -/
-- @node: ass:gaussian-disturbance
def GaussianDisturbance (Ωc : Fin (M + 1) → Matrix (Fin p) (Fin p) ℝ)
    (ξ : Fin (M + 1) → Ω → Fin p → ℝ) : Prop :=
  ∀ m, (Ωc m).PosDef ∧
    HasLaw (fun ω => WithLp.toLp 2 (ξ m ω))
      (multivariateGaussian 0 (Ωc m)) μ

/-- Conditional independent Poisson count law at a fixed offset and latent state. -/
noncomputable def poissonCountLaw (s z : Fin p → ℝ) : Measure (Fin p → ℕ) :=
  Measure.pi (fun j => poissonMeasure (Real.toNNReal (s j * Real.exp (z j))))

/-- The conditioning and joint observed maps are almost everywhere measurable,
and the joint offset, state, count law is the conditional Poisson mixture. -/
-- @node: ass:poisson-measurement
def PoissonMeasurement {E R : Type*}
    (Z S : E → R → Ω → Fin p → ℝ) (X : E → R → Ω → Fin p → ℕ) : Prop :=
  ∀ m r,
    (∀ᵐ ω ∂μ, ∀ j, 0 < S m r ω j) ∧ -- @realizes S_{rj}^{(m)}(a.s. positive)
    AEMeasurable (fun ω => (S m r ω, Z m r ω)) μ ∧
    AEMeasurable (fun ω => ((S m r ω, Z m r ω), X m r ω)) μ ∧
    μ.map (fun ω => ((S m r ω, Z m r ω), X m r ω)) =
      Measure.bind (μ.map (fun ω => (S m r ω, Z m r ω)))
        (fun sz => (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x)))

/-- The observable pair is measurable up to null sets under the conditional
Poisson measurement model. -/
theorem PoissonMeasurement.obs_aemeasurable {E R : Type*}
    {Z S : E → R → Ω → Fin p → ℝ} {X : E → R → Ω → Fin p → ℕ}
    (hP : PoissonMeasurement μ Z S X) (m : E) (r : R) :
    AEMeasurable (fun ω => (S m r ω, X m r ω)) μ := by
  have hfull := (hP m r).2.2.1
  exact hfull.fst.fst.prodMk hfull.snd

-- @node: ass:iid-within-environment
def IIDWithinEnvironment
    (S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ)
    (X : Fin (p + 1) → Fin n → Ω → Fin p → ℕ) : Prop :=
  ∀ m, iIndepFun (fun r ω => (S m r ω, X m r ω)) μ ∧
    ∀ r r', IdentDistrib (fun ω => (S m r ω, X m r ω))
      (fun ω => (S m r' ω, X m r' ω)) μ μ

-- @node: ass:offset-exogeneity
def OffsetExogeneity {E R : Type*}
    (S Z : E → R → Ω → Fin p → ℝ) : Prop :=
  ∀ m r, IndepFun (S m r) (Z m r) μ

/-- The adjusted first factorial count. @realizes U_{rj}^{(m)}(X/S) -/
noncomputable def firstFactorial (x : Fin p → ℕ) (s : Fin p → ℝ) (j : Fin p) : ℝ :=
  (x j : ℝ) / s j

/-- The adjusted second factorial count. @realizes W_{rj}^{(m)}(X(X-1)/S²) -/
noncomputable def secondFactorial (x : Fin p → ℕ) (s : Fin p → ℝ) (j : Fin p) : ℝ :=
  (x j : ℝ) * ((x j : ℝ) - 1) / (s j) ^ 2

/-- Cross factorial count, including the diagonal. @realizes R_{rjk}^{(m)}(cross factorial) -/
noncomputable def crossFactorial (x : Fin p → ℕ) (s : Fin p → ℝ) (j k : Fin p) : ℝ :=
  if j = k then secondFactorial x s j
  else (x j : ℝ) * (x k : ℝ) / (s j * s k)

-- @node: ass:factorial-variance-bound
def FactorialVarianceBound
    (Z S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ) (v : ℝ) : Prop :=
  (∀ m r j,
    Integrable (fun ω => Real.exp (Z m r ω j)) μ ∧
    MemLp (fun ω => Real.exp (Z m r ω j)) 2 μ ∧
    Integrable (fun ω => Real.exp (2 * Z m r ω j)) μ ∧
    MemLp (fun ω => Real.exp (2 * Z m r ω j)) 2 μ ∧
    Integrable (fun ω => Real.exp (3 * Z m r ω j)) μ ∧
    Integrable (fun ω => (S m r ω j)⁻¹) μ ∧
    Integrable (fun ω => (S m r ω j)⁻¹ ^ 2) μ) ∧
  ∀ m r j,
    max (variance (fun ω => Real.exp (Z m r ω j)) μ +
      (∫ ω, Real.exp (Z m r ω j) ∂μ) *
        ∫ ω, (S m r ω j)⁻¹ ∂μ)
      (variance (fun ω => Real.exp (2 * Z m r ω j)) μ +
        4 * (∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
          (∫ ω, (S m r ω j)⁻¹ ∂μ) +
        2 * (∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
          ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ) ≤ v

-- @node: ass:first-moment-nondegeneracy
def FirstMomentNondegeneracy
    (S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ)
    (X : Fin (p + 1) → Fin n → Ω → Fin p → ℕ) (ℓ : ℝ) : Prop :=
  ∀ m r j, ℓ ≤ ∫ ω, firstFactorial (X m r ω) (S m r ω) j ∂μ

/-- Total effect matrix. @realizes B((I_p-A)⁻¹)
@realizes I_p(matrix identity 1) -/
noncomputable def totalEffect (A : Matrix (Fin p) (Fin p) ℝ) := (1 - A)⁻¹

/-- State determined by the structural equation. @realizes Z^{(m)}((I-A)⁻¹(η+ξ)) -/
noncomputable def latentState (A : Matrix (Fin p) (Fin p) ℝ)
    (η : Fin (M + 1) → Fin p → ℝ)
    (ξ : Fin (M + 1) → Ω → Fin p → ℝ)
    (m : Fin (M + 1)) (ω : Ω) : Fin p → ℝ :=
  totalEffect A *ᵥ (fun i => η m i + ξ m ω i)

/-- Invariant atomic Poisson lognormal structural model.
@realizes \mathcal M_p(atomic count-shift model class) -/
-- @node: def:atomic-count-model
structure AtomicCountModel (p M : ℕ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  p_pos : 0 < p -- @realizes p(positive coordinate count)
  M_pos : 0 < M -- @realizes M(positive intervention count)
  A : Matrix (Fin p) (Fin p) ℝ -- @realizes A(matrix ℝ^{p×p})
  η : Fin (M + 1) → Fin p → ℝ -- @realizes \eta_m(intercepts)
  Ωc : Fin (M + 1) → Matrix (Fin p) (Fin p) ℝ -- @realizes \Omega_m(covariance carrier)
  α : Fin M → ℝ -- @realizes \alpha_m(strength)
  t : Fin M → Fin p -- @realizes t(m)(target map)
  ξ : Fin (M + 1) → Ω → Fin p → ℝ -- @realizes \xi^{(m)}(disturbance carrier)
  S : Fin (M + 1) → Ω → Fin p → ℝ -- @realizes S_{rj}^{(m)}(a.s. positive offset)
  X : Fin (M + 1) → Ω → Fin p → ℕ -- @realizes X_{r}^{(m)}(count carrier)
  acyclic : AcyclicMechanism A
  atomic : AtomicMeanShift η α t
  nonvanishing : NonvanishingStrength α
  gaussian : GaussianDisturbance μ Ωc ξ
  poisson : PoissonMeasurement μ (fun m (_ : Unit) => latentState A η ξ m)
    (fun m _ => S m) (fun m _ => X m)

-- @env: S2
variable {p' M' : ℕ} {Ω' : Type*} [MeasurableSpace Ω']

/-- Observable offset and count law. @realizes P_m(observable law) -/
noncomputable def obsLaw (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin (M + 1)) : Measure ((Fin p → ℝ) × (Fin p → ℕ)) :=
  μ.map (fun ω => (𝔐.S m ω, 𝔐.X m ω))

/-- Latent mean recovered from adjusted factorial moments. @realizes \mu_m(log moments) -/
noncomputable def obsMean (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin (M + 1)) (j : Fin p) : ℝ :=
  2 * Real.log (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) -
    (1 / 2 : ℝ) * Real.log
      (∫ ω, secondFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ)

/-- Latent covariance recovered from adjusted cross factorial moments.
@realizes V_m(log cross moments) -/
noncomputable def obsCov (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin (M + 1)) (j k : Fin p) : ℝ :=
  Real.log (∫ ω, crossFactorial (𝔐.X m ω) (𝔐.S m ω) j k ∂μ) -
    Real.log (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) -
    Real.log (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) k ∂μ)

/-- Observable latent mean shift. @realizes d_m(μ_m-μ_0) @realizes D(shift columns) -/
noncomputable def obsShift (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin M) (j : Fin p) : ℝ := obsMean μ 𝔐 m.succ j - obsMean μ 𝔐 0 j

/-- Smallest direct strength in the balanced full-cover design.
@realizes a(minimum absolute direct strength) -/
noncomputable def minStrength (𝔐 : AtomicCountModel p p Ω μ) : ℝ :=
  sInf {x : ℝ | ∃ m : Fin p, x = |𝔐.α m|}

/-- Balanced bounded moment class.
@realizes \mathcal Q_{p,n}(\ell,v)(balanced experiment class) -/
-- @node: def:bounded-moment-class
structure BoundedMomentClass (p n : ℕ) (ℓ v : ℝ) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  p_pos : 0 < p -- @realizes p(positive coordinate count)
  n_pos : 0 < n -- @realizes n(positive replicate count)
  ell_pos : 0 < ℓ -- @realizes \ell(positive moment floor)
  ell_le : ℓ ≤ Real.exp (1 / 2) -- @realizes \ell(at most exp(1/2))
  v_pos : 0 < v -- @realizes v(positive variance envelope)
  Z : Fin (p + 1) → Fin n → Ω → Fin p → ℝ
  S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ -- @realizes S_{rj}^{(m)}(a.s. positive offset)
  X : Fin (p + 1) → Fin n → Ω → Fin p → ℕ
  poisson : PoissonMeasurement μ Z S X
  iid : IIDWithinEnvironment μ S X
  exog : OffsetExogeneity μ S Z
  varBound : FactorialVarianceBound μ Z S v
  firstMoment : FirstMomentNondegeneracy μ S X ℓ

/-- Observable mean functional for the balanced experiment, at a fixed replicate. -/
noncomputable def balancedObsMean (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
    (r : Fin n) (m : Fin (p + 1)) (j : Fin p) : ℝ :=
  2 * Real.log (∫ ω, firstFactorial (𝒬.X m r ω) (𝒬.S m r ω) j ∂μ) -
    (1 / 2 : ℝ) * Real.log
      (∫ ω, secondFactorial (𝒬.X m r ω) (𝒬.S m r ω) j ∂μ)

/-- Balanced observable mean shift. -/
noncomputable def balancedObsShift (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
    (r : Fin n) (m j : Fin p) : ℝ :=
  balancedObsMean μ 𝒬 r m.succ j - balancedObsMean μ 𝒬 r 0 j

/-- Full observed balanced count-offset sample. -/
abbrev ObservedSample (p n : ℕ) :=
  (Fin (p + 1) → Fin n → Fin p → ℝ) ×
    (Fin (p + 1) → Fin n → Fin p → ℕ)

/-- Law of the full observed balanced sample. -/
noncomputable def obsSampleLaw (𝒬 : BoundedMomentClass p n ℓ v Ω μ) :
    Measure (ObservedSample p n) :=
  μ.map (fun ω =>
    (fun m r => 𝒬.S m r ω, fun m r => 𝒬.X m r ω))

/-- Uniform mixture of the nonbaseline alternatives. -/
noncomputable def uniformAltMixture {α : Type*} [MeasurableSpace α]
    {p : ℕ} [NeZero p] (P : Fin p → Measure α) : Measure α :=
  ∑ j ∈ (Finset.univ.filter (fun j : Fin p => j ≠ 0)),
    (((p - 1 : ℕ) : ℝ≥0∞)⁻¹) • P j

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
