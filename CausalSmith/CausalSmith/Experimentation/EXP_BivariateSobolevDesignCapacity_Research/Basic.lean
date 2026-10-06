module
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Bivariate Sobolev design capacity: carriers and constructions

The continuous covariate world uses Mathlib kernels; the finite-design substrate does not
carry covariate-dependent assignment. The minimax functional reuses Causalean's extended
nonnegative API. All paper-owned proof obligations are left to the proof-filling stage.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal FourierTransform BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

set_option maxSynthPendingDepth 5

-- @env: S1
variable {n d p : ℕ} {s : ℝ}
-- @realizes n(sample size; range ≥2 in theorem signatures)
-- @realizes d(dimension; range ≥2 in theorem signatures)
-- @realizes s(smoothness; range 0<s≤1 in theorem signatures)

/-- [ Ambient coordinates; the sampling measure is supported on the unit cube. -/
abbrev Cube (d : ℕ) := Fin d → ℝ -- @realizes x(real d-coordinates; support via cubeMeasure)
/-- Unit indices. -/
abbrev UnitIdx (n : ℕ) := Fin n -- @realizes i(indices 1,…,n)
/-- Coordinate indices. -/
abbrev CoordIdx (d : ℕ) := Fin d -- @realizes j(indices 1,…,d) @realizes ell(indices 1,…,d)
/-- Product uniform measure, including the zero-dimensional convention. -/
def cubeMeasure (d : ℕ) : Measure (Cube d) :=
  Measure.pi (fun _ => volume.restrict (Icc (0 : ℝ) 1))
  -- @realizes x(unit-cube sampling support)
/-- Finite-valued Borel centered square-integrable representatives. -/
abbrev CenteredL2Fn (d : ℕ) := {m : Cube d → ℝ // -- @realizes m(finite real carrier)
  Measurable m ∧ -- @realizes m(Borel representative)
  MemLp m 2 (cubeMeasure d) ∧ -- @realizes m(square-integrable under cubeMeasure)
  ∫ x, m x ∂cubeMeasure d = 0} -- @realizes m(centered under cubeMeasure)
/-- Canonical main effect, integrating the unused coordinates. -/
def g1 (m : Cube d → ℝ) (j : Fin d) (u : ℝ) : ℝ :=
  ∫ y, m (Function.update y j u) ∂cubeMeasure d -- @realizes g1(canonical marginal integral)
/-- Canonical pair effect, subtracting the two main effects. -/
def g2 (m : Cube d → ℝ) (j l : Fin d) (u v : ℝ) : ℝ :=
  (∫ y, m (Function.update (Function.update y j u) l v) ∂cubeMeasure d) -
    g1 m j u - g1 m l v -- @realizes g2(canonical pair integral minus main effects)
/-- The closed unit cube in Euclidean coordinates. -/
def euclideanCube (p : ℕ) : Set (EuclideanSpace ℝ (Fin p)) :=
  {u | ∀ h, u h ∈ Icc (0 : ℝ) 1} -- @realizes p(component dimensions 1 or 2 at consumers)
/-- The unitary angular-frequency Fourier integral, initially on integrable extensions. -/
def Fourier (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (ω : EuclideanSpace ℝ (Fin p)) : ℂ :=
  (2 * Real.pi) ^ (-(p : ℝ) / 2) •
    ∫ u, Complex.exp (-Complex.I * ((∑ h, ω h * u h : ℝ) : ℂ)) * G u
  -- @realizes Fourier((2π)^(-p/2) integral exp(-i omega·u) G(u))
  -- @realizes omega(angular Euclidean frequency)
/-- Squared restriction norm, as an extension infimum of weighted Fourier energy.
The integrable extensions give the same infimum by cutoff approximation; the squared
functional is used directly, avoiding an accidental fourth power in the pooled budget. -/
def sobolevNormSq (p : ℕ) (s : ℝ) (g : Cube p → ℝ) : ℝ≥0∞ :=
  ⨅ (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (_ : Integrable G volume ∧ MemLp G 2 volume ∧
      G =ᵐ[volume.restrict (euclideanCube p)] fun u => (g (fun h => u h) : ℂ)),
    ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)
  -- @realizes N(squared restriction norm; extension-infimum Fourier energy)

-- @node: ass:order-two
/-- Exact canonical order-two ANOVA with zero intercept. -/
def OrderTwo (m : CenteredL2Fn d) : Prop :=
  m.val =ᵐ[cubeMeasure d] fun x =>
    (∑ j, g1 m.val j (x j)) + ∑ j, ∑ l,
      if j < l then g2 m.val j l (x j) (x l) else 0

-- @node: ass:pooled-budget
/-- The pooled squared component restriction norms have total budget one. -/
def PooledBudget (s : ℝ) (m : CenteredL2Fn d) : Prop :=
  (∑ j, sobolevNormSq 1 s (fun u => g1 m.val j (u 0))) +
    (∑ j, ∑ l, if j < l then
      sobolevNormSq 2 s (fun u => g2 m.val j l (u 0) (u 1)) else 0) ≤ 1

-- @node: def:sobolev-class
/-- Centered bivariate outcomes with the exact ANOVA decomposition and pooled budget. -/
structure SobolevClass (d : ℕ) (s : ℝ) (m : CenteredL2Fn d) : Prop where
  orderTwo : OrderTwo m -- @realizes H(exact order-two canonical decomposition)
  pooledBudget : PooledBudget s m -- @realizes H(order-two class with pooled restriction budget)

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω]
/-- A Bool represents a sign; true is +1 and false is −1. -/
abbrev Signs (n : ℕ) := Fin n → Bool -- @realizes Zspace(original unit sign vectors)
/-- The finite sign space is standard Borel. -/
instance signsStandardBorel (n : ℕ) : StandardBorelSpace (Signs n) := inferInstance
/-- The real sign associated with a coin. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1
/-- Covariate arrays. -/
abbrev Covariates (n d : ℕ) := Fin n → Cube d -- @realizes X(original n-by-d covariates)
/-- The covariate array is standard Borel. -/
instance covariatesStandardBorel (n d : ℕ) : StandardBorelSpace (Covariates n d) :=
  inferInstance
/-- Independent uniform original covariates. -/
def covLaw (n d : ℕ) : Measure (Covariates n d) :=
  Measure.pi (fun _ => cubeMeasure d)
/-- Pre-assignment schedules, with control first and treatment second. -/
abbrev Sched (n : ℕ) := Fin n → ℝ × ℝ -- @realizes Y(real potential outcome schedules)
/-- The schedule space is standard Borel. -/
instance schedStandardBorel (n : ℕ) : StandardBorelSpace (Sched n) := inferInstance
/-- Joint law drawing a schedule before drawing covariate-only assignment. -/
def experimentLaw (μX : Measure (Covariates n d))
    (κ : Kernel (Covariates n d) (Sched n))
    (π : Kernel (Covariates n d) (Signs n)) :
    Measure ((Covariates n d × Sched n) × Signs n) :=
  (μX ⊗ₘ κ) ⊗ₘ (π.comap Prod.fst measurable_fst)
  -- @realizes Z(assignment drawn after X,Y from the X-only kernel)

-- @node: ass:uniform-draw
/-- Independent uniform covariates on an arbitrary sampling space. -/
def UniformDraw (μ : Measure Ω) (X : Ω → Covariates n d) : Prop :=
  Measurable X ∧ μ.map X = covLaw n d

-- @node: ass:fair
/-- Unitwise conditional zero sign means under the original cube-supported sampling law.
Null-set representatives and values outside the sampled cube are unrestricted. -/
def FairKernel (π : Kernel (Covariates n d) (Signs n)) : Prop :=
  ∀ᵐ x ∂covLaw n d, ∀ i, ∫ z, sgn (z i) ∂π x = 0

/-- Pointwise fairness, used internally for concrete constructions and the cited carrier. -/
def PointwiseFairKernel (π : Kernel (Covariates n d) (Signs n)) : Prop :=
  ∀ x i, ∫ z, sgn (z i) ∂π x = 0


-- @node: ass:assignment-independence
/-- Assignment is conditionally independent of every pre-assignment outcome mechanism. -/
def OutcomeIndependentKernel (π : Kernel (Covariates n d) (Signs n)) : Prop :=
  ∀ (hπ : IsMarkovKernel π) (μX : Measure (Covariates n d))
    (hμ : IsProbabilityMeasure μX) (κ : Kernel (Covariates n d) (Sched n))
    (hκ : IsMarkovKernel κ),
    letI := hπ; letI := hμ; letI := hκ
    letI : IsProbabilityMeasure (experimentLaw μX κ π) :=
      inferInstanceAs (IsProbabilityMeasure
        ((μX ⊗ₘ κ) ⊗ₘ (π.comap Prod.fst measurable_fst)))
    CondIndepFun (MeasurableSpace.comap (fun ω : (Covariates n d × Sched n) × Signs n =>
      ω.1.1) inferInstance) (measurable_fst.fst.comap_le)
      (fun ω => ω.2) (fun ω => ω.1.2) (experimentLaw μX κ π)

/-- Borel probability assignment kernels, with no outcomes in the input. -/
abbrev Design (n d : ℕ) := {π : Kernel (Covariates n d) (Signs n) // IsMarkovKernel π}
  -- @realizes pi(covariate-only Borel probability kernel)

-- @node: def:design-class
/-- Fair outcome-independent original-sample designs. -/
structure DesignClass (n d : ℕ) (π : Design n d) : Prop where
  fair : FairKernel π.val -- @realizes D(fairness a.e. under the original cube covariate law)
  outcomeIndep : OutcomeIndependentKernel π.val -- @realizes D(admissible fair independent kernels)

/-- Independent fair signs. -/
def fairSigns (n : ℕ) : Measure (Signs n) := (PMF.uniformOfFintype (Signs n)).toMeasure
/-- The independent-sign law is a probability measure.](goal) This uses [the stated conclusion](goal). -/
-- @node: fairSigns_probability
lemma fairSigns_probability (n : ℕ) : IsProbabilityMeasure (fairSigns n) := by
  unfold fairSigns
  infer_instance
/-- [ The independent-sign branch, constant in the covariates. -/
def fairSignKernel (n d : ℕ) : Design n d :=
  letI := fairSigns_probability n
  ⟨Kernel.const (Covariates n d) (fairSigns n), inferInstance⟩
/-- Uniform signs have zero marginal means by the sign-reversal involution.](goal) This uses [the stated conclusion](goal). -/
-- @node: fairSigns_mean_zero
lemma fairSigns_mean_zero (n : ℕ) (i : Fin n) :
    ∫ z, sgn (z i) ∂fairSigns n = 0 := by
  letI := fairSigns_probability n
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, fairSigns, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, smul_eq_mul]
  let e : Signs n ≃ Signs n :=
    { toFun := fun z j => !(z j)
      invFun := fun z j => !(z j)
      left_inv := by intro z; funext j; simp
      right_inv := by intro z; funext j; simp }
  have hsum := e.sum_comp (fun z => ((Fintype.card (Signs n) : ℝ≥0∞)⁻¹).toReal * sgn (z i))
  have hneg (z : Signs n) : sgn (e z i) = -sgn (z i) := by
    change sgn (!(z i)) = -sgn (z i)
    cases z i <;> norm_num [sgn]
  simp only [hneg, mul_neg, Finset.sum_neg_distrib] at hsum
  linarith

/-- Every almost-everywhere fair design has a pointwise fair null-equivalent representative.
This changes a representative for proof purposes, not membership in the public design class. Under [the stated conditions](hyp:hfair), [the asserted mathematical result follows](goal). -/
-- @node: pointwiseFairRepresentative
lemma pointwiseFairRepresentative (π : Design n d) (hfair : FairKernel π.val) :
    ∃ ρ : Design n d, PointwiseFairKernel ρ.val ∧
      (fun x => ρ.val x) =ᵐ[covLaw n d] (fun x => π.val x) := by
  classical
  letI : IsMarkovKernel π.val := π.property
  letI : IsMarkovKernel (fairSignKernel n d).val := (fairSignKernel n d).property
  let good : Set (Covariates n d) := {x | ∀ i, ∫ z, sgn (z i) ∂π.val x = 0}
  have hgood : MeasurableSet good := by
    change MeasurableSet {x | ∀ i, ∫ z, sgn (z i) ∂π.val x = 0}
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun x : Covariates n d => ∫ z, sgn (z i) ∂π.val x) := by
      have hz : Measurable (fun z : Signs n => sgn (z i)) := by fun_prop
      exact (hz.stronglyMeasurable.integral_kernel (κ := π.val)).measurable
    exact measurableSet_eq_fun hm measurable_const
  let ρ : Design n d := ⟨Kernel.piecewise hgood π.val (fairSignKernel n d).val,
    inferInstance⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro x i
    change (∫ z, sgn (z i) ∂Kernel.piecewise hgood π.val (fairSignKernel n d).val x) = 0
    rw [Kernel.piecewise_apply]
    by_cases hx : x ∈ good
    · rw [if_pos hx]
      exact hx i
    · rw [if_neg hx]
      exact fairSigns_mean_zero n i
  · filter_upwards [hfair] with x hx
    change Kernel.piecewise hgood π.val (fairSignKernel n d).val x = π.val x
    rw [Kernel.piecewise_apply, if_pos (show x ∈ good from hx)]

/-- Extended expected squared prognostic imbalance. -/
def loss (π : Design n d) (m : Cube d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / (n : ℝ)) * ∫⁻ x, ∫⁻ z,
    ENNReal.ofReal ((∑ i, sgn (z i) * m (x i)) ^ 2) ∂π.val x ∂covLaw n d
  -- @realizes loss(4/n times joint expected squared imbalance)

-- @node: def:criterion
/-- Full-design capacity, keeping the fixed-function supremum outside sampling. -/
def capacity (n d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (π : {π : Design n d // DesignClass n d π})
      (m : {m : CenteredL2Fn d // SobolevClass d s m}) => loss π.val m.val.val)
  -- @realizes R(infimum over all admissible designs of fixed-function worst risk)
/-- Worst risk of a specified design. -/
def worstLoss (π : Design n d) (s : ℝ) : ℝ≥0∞ :=
  ⨆ m : {m : CenteredL2Fn d // SobolevClass d s m}, loss π m.val.val

-- @env: S5
variable {L : ℕ}
/-- Number of coordinate pairs. -/
def pairCount (d : ℕ) : ℕ := d.choose 2 -- @realizes B(d choose 2)
/-- Pair-cosine indices and positive integer frequencies. -/
abbrev PairIdx (d L : ℕ) :=
  {α : (Fin d × Fin d) × (Fin L × Fin L) // α.1.1 < α.1.2}
  -- @realizes alpha(j<ell and two positive frequencies ≤L)
/-- Number of cosine coordinates. -/
def priorDimension (d L : ℕ) : ℕ := pairCount d * L ^ 2 -- @realizes M(B L²)
/-- Explicit positive cutoff-extension normalization. -/
def C0 : ℝ := Real.sqrt (48 + 32 * Real.pi ^ 2) -- @realizes C0(fixed √(48+32π²))
/-- Tensor-pair cosine features. -/
def pairFeature (α : PairIdx d L) (x : Cube d) : ℝ :=
  2 * Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * x α.val.1.1) *
    Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * x α.val.1.2)
  -- @realizes V(pair-cosine features with frequencies 1,…,L)
/-- The normalized random-sign cosine polynomial. -/
def mXi (s : ℝ) (L : ℕ) (ξ : PairIdx d L → Bool) : Cube d → ℝ :=
  fun x => (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ *
    ∑ α, sgn (ξ α) * pairFeature α x
  -- @realizes m_xi(normalized sign-weighted cosine polynomial)
/-- The prior cutoff. -/
def priorCutoff (n d : ℕ) : ℕ :=
  max 1 ⌈Real.sqrt (4096 * (n : ℝ) / pairCount d)⌉₊ -- @realizes L(positive cutoff ceil √(4096n/B))

-- @node: def:cosine-prior
/-- Uniform independent coefficient signs; its function image is the legal-prior candidate. -/
def cosinePrior (n d : ℕ) (_s : ℝ) : PMF (PairIdx d (priorCutoff n d) → Bool) :=
  PMF.uniformOfFintype _ -- @realizes xi(uniform coefficient signs independent of X)
  -- @realizes nu_star(function law represented by finite sign prior and mXi pushforward)
/-- The prior average risk, without a measurable-space choice on the function space. -/
def priorRisk (π : Design n d) (s : ℝ) : ℝ≥0∞ :=
  ∑ ξ, (cosinePrior n d s ξ) * loss π (mXi s (priorCutoff n d) ξ)
/-- Lower comparison scale. -/
def bScale (n d : ℕ) (s : ℝ) : ℝ :=
  min 1 (((pairCount d : ℝ) / n) ^ s) -- @realizes b_s(min 1 (B/n)^s)
/-- Sharper lower constant, independent of n and d. -/
def cLower (s : ℝ) : ℝ :=
  2 / ((48 + 32 * Real.pi ^ 2) * (16384 : ℝ) ^ s)
  -- @realizes c_s(explicit universal lower constant)
/-- Uniform upper constant. -/
def CUpper : ℝ := 3072 -- @realizes C_s(universal upper constant 3072)

-- @env: S3
variable (hd : 0 < d)
/-- The fixed average treatment effect. -/
def tau0 : ℝ := 0.2 -- @realizes tau0(fixed 0.2)
/-- The fixed treatment-effect amplitude. -/
def delta : ℝ := 0.1 -- @realizes delta(fixed 0.1)
/-- The sinusoidal covariate treatment effect. -/
def tauFn (x : Cube d) : ℝ :=
  tau0 + delta * Real.sqrt 2 * Real.sin (2 * Real.pi * x ⟨0, hd⟩)
  -- @realizes tau(tau0+delta √2 sin(2πx1))
/-- Independent unit-variance Gaussian noise, drawn before assignment. -/
def noiseLaw (n : ℕ) : Measure (Sched n) :=
  Measure.pi (fun _ => (gaussianReal 0 1).prod (gaussianReal 0 1))
  -- @realizes epsilon(N(0,I_2n) independent of X)
/-- Potential outcomes with prognosis m and the fixed heterogeneous treatment effect. -/
def completionSchedule (m : Cube d → ℝ) (x : Covariates n d) (e : Sched n) : Sched n :=
  fun i => (m (x i) - tauFn hd (x i) / 2 + (e i).1,
    m (x i) + tauFn hd (x i) / 2 + (e i).2)
  -- @realizes Y(m(X)±tau(X)/2+Gaussian noise)
/-- Measurability of the Gaussian completion's measure-valued map. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: measurable_completion
lemma measurable_completion (m : CenteredL2Fn d) :
    Measurable (fun x : Covariates n d =>
      (noiseLaw n).map (completionSchedule hd m.val x)) := by
  have hm : Measurable m.val := m.property.1
  letI : IsProbabilityMeasure (noiseLaw n) := by
    unfold noiseLaw
    infer_instance
  have hjoint : Measurable (fun xe : Covariates n d × Sched n =>
      completionSchedule hd m.val xe.1 xe.2) := by
    unfold completionSchedule tauFn
    fun_prop
  have h := (Measure.measurable_map _ hjoint).comp
    (Measurable.map_prodMk_left (ν := noiseLaw n) (α := Covariates n d))
  simpa only [Function.comp_def, Measure.map_map hjoint measurable_prodMk_left] using h

/-- The pre-assignment Gaussian potential-outcome kernel. -/
def gaussianCompletion (m : CenteredL2Fn d) : Kernel (Covariates n d) (Sched n) :=
  ⟨fun x => (noiseLaw n).map (completionSchedule hd m.val x), measurable_completion hd m⟩
/-- Treatment indicator corresponding to the original unit sign. -/
def treatment (z : Signs n) (i : Fin n) : ℝ := (sgn (z i) + 1) / 2
  -- @realizes A((Z_i+1)/2)
/-- Actual unit-weight Horvitz--Thompson ATE estimator. -/
def htEstimator (y : Sched n) (z : Signs n) : ℝ :=
  (2 / (n : ℝ)) * ∑ i, sgn (z i) * (if z i then (y i).2 else (y i).1)
  -- @realizes theta_hat(actual 2/n unit-weight HT estimator)
/-- Realized full-schedule finite-population ATE. -/
def finiteATE (y : Sched n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ((y i).2 - (y i).1) -- @realizes theta_n(full-schedule average effect)
/-- Potential-outcome midpoint vector. -/
def prognosis (y : Sched n) (i : Fin n) : ℝ :=
  ((y i).2 + (y i).1) / 2 -- @realizes q(schedule midpoint vector)
/-- The assignment covariance matrix, including its mean subtraction. -/
def assignCov (π : Design n d) (x : Covariates n d) (i j : Fin n) : ℝ :=
  (∫ z, sgn (z i) * sgn (z j) ∂π.val x) -
    (∫ z, sgn (z i) ∂π.val x) * (∫ z, sgn (z j) ∂π.val x)
  -- @realizes Cpi(conditional assignment covariance)
/-- Gaussian benchmark. -/
def Vstar : ℝ := delta ^ 2 + 4 -- @realizes Vstar(delta²+4=4.01)
/-- Superpopulation target under the Gaussian completion. -/
def gaussianTheta (m : CenteredL2Fn d) : ℝ :=
  ∫ ω, finiteATE ω.2 ∂(covLaw n d ⊗ₘ gaussianCompletion hd m)
  -- @realizes theta(expectation of finite population ATE)


-- @node: def:causal-completion
/-- The frozen causal completion uses independent standard Gaussian pre-assignment noise
and the sinusoidal treatment effect specified by S3. It draws X, then the full schedule Y,
then assignment from the covariate-only kernel. The remaining components explicitly anchor
A=(Z+1)/2, the actual HT estimator, the full-schedule target, and its sampling expectation. -/
def gaussianCausalCompletion (m : CenteredL2Fn d) (π : Design n d) :
    Measure ((Covariates n d × Sched n) × Signs n) ×
      (Signs n → Fin n → ℝ) × (Sched n → Signs n → ℝ) × (Sched n → ℝ) × ℝ :=
  (experimentLaw (covLaw n d) (gaussianCompletion hd m) π.val,
    treatment, htEstimator, finiteATE, gaussianTheta (n := n) hd m)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
