import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import Causalean.Stat.Minimax.MinimaxValue
import Causalean.Mathlib.Probability.StdNormalCDF
import Causalean.Experimentation.DesignBased.Optimality.Neyman
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option linter.style.openClassical false

/-!
# Gaussian face games and mechanism values

This file defines the full-location and compact quotient simple-regret games
using the product of scalar Gaussian measures, then states their shared analytic
properties for Stage 3.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

-- @env: S5
variable (A : Finset (Fin K)) (v r : Fin K → ℝ)

/-- Coordinates indexed only by the declared active face. -/
abbrev ActiveIndex (A : Finset (Fin K)) := {k : Fin K // k ∈ A}

def extendActive (A : Finset (Fin K)) (h : ActiveIndex A → ℝ) : Fin K → ℝ :=
  fun k => if hk : k ∈ A then h ⟨k, hk⟩ else 0

def restrictActive (A : Finset (Fin K)) (x : Fin K → ℝ) : ActiveIndex A → ℝ :=
  fun k => x k.1

/-- The least active arm, with a harmless fallback for an empty set. -/
def referenceArm [NeZero K] (A : Finset (Fin K)) : Fin K :=
  if h : A.Nonempty then A.min' h else 0

/-- Reference contrast coordinate `h_k-h_a0`. -/
def contrastCoordinate [NeZero K] (A : Finset (Fin K))
    (h : Fin K → ℝ) (k : Fin K) : ℝ := h k - h (referenceArm A)
-- @realizes D_A(rows e_k' - e_a0')

/-- Two representatives define the same translation-quotient point. -/
def TranslationEquivalent (A : Finset (Fin K)) (h h' : Fin K → ℝ) : Prop :=
  ∃ c : ℝ, ∀ k ∈ A, h' k = h k + c
-- @realizes H_A(R^A modulo span{1_A})
-- @realizes \mathbf 1_A(common-shift direction)

/-- Euclidean reference-contrast quotient norm. -/
def quotientNorm [NeZero K] (A : Finset (Fin K)) (h : Fin K → ℝ) : ℝ :=
  Real.sqrt (∑ k ∈ A, (contrastCoordinate A h k) ^ 2)
-- @realizes \lVert[h]\rVert_A(norm of D_A h)

/-- Diagonal Gaussian covariance entry `v_k/r_k`. -/
def gaussianCovariance (v r : Fin K → ℝ) (i j : Fin K) : ℝ :=
  if i = j then v i / r i else 0
-- @realizes \Sigma(v_A,r_A)(diag(v_k/r_k))

/-- Independent-coordinate Gaussian location law. -/
def diagonalGaussian (h v r : Fin K → ℝ) : Measure (Fin K → ℝ) :=
  Measure.pi fun k => ProbabilityTheory.gaussianReal (h k) (Real.toNNReal (v k / r k))

/-- The Gaussian observation actually available to a selector on face `A`.
Inactive coordinates are absent from the observation type. -/
def activeDiagonalGaussian (A : Finset (Fin K)) (h v r : Fin K → ℝ) :
    Measure (ActiveIndex A → ℝ) :=
  Measure.pi fun k => ProbabilityTheory.gaussianReal (h k.1)
    (Real.toNNReal (v k.1 / r k.1))

/-- Reference-contrast covariance. -/
def quotientCovariance [NeZero K] (A : Finset (Fin K)) (v r : Fin K → ℝ)
    (i j : Fin K) : ℝ :=
  gaussianCovariance v r i j - gaussianCovariance v r i (referenceArm A) -
    gaussianCovariance v r (referenceArm A) j +
      gaussianCovariance v r (referenceArm A) (referenceArm A)
-- @realizes \Omega_A(D_A Sigma D_A')

/-- Coordinates of the reference-contrast quotient. -/
abbrev QuotientIndex [NeZero K] (A : Finset (Fin K)) :=
  {k : Fin K // k ∈ A ∧ k ≠ referenceArm A}

/-- The reference value used by the quotient map.  On every nonempty face the
fallback branch is impossible. -/
def activeReferenceValue [NeZero K] (A : Finset (Fin K))
    (x : ActiveIndex A → ℝ) : ℝ :=
  if h : referenceArm A ∈ A then x ⟨referenceArm A, h⟩ else 0

/-- The observable reference-contrast vector `D_A x`, formed only from active
coordinates. -/
def quotientObservation [NeZero K] (A : Finset (Fin K)) (x : ActiveIndex A → ℝ) :
    EuclideanSpace ℝ (QuotientIndex A) :=
  WithLp.toLp 2 fun k => x ⟨k.1, k.2.1⟩ - activeReferenceValue A x

/-- The genuine multivariate Gaussian law with mean `D_A h` and covariance
`Omega_A = D_A Sigma D_A'`. -/
def quotientGaussianLaw [NeZero K] (A : Finset (Fin K)) (h v r : Fin K → ℝ) :
    Measure (EuclideanSpace ℝ (QuotientIndex A)) :=
  ProbabilityTheory.multivariateGaussian (quotientObservation A (restrictActive A h))
    (fun i j => quotientCovariance A v r i.1 j.1)

/-- A measurable randomized selector supported on `A`. -/
def GaussianSelector (A : Finset (Fin K))
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) : Prop :=
  (∀ a, Measurable fun x => delta x a) ∧
    (∀ x a, 0 ≤ delta x a) ∧
    (∀ x, ∑ a, delta x a = 1) ∧ ∀ x a, a ∉ A → delta x a = 0

/-- A selector ignores the common-location nuisance. -/
def LocationInvariantSelector (A : Finset (Fin K))
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) : Prop :=
  ∀ x c a, delta (fun k => x k + c) a = delta x a

/-- A location-invariant selector factors measurably through `D_A`. -/
def MeasurablyFactorsThroughQuotient [NeZero K] (A : Finset (Fin K))
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) : Prop :=
  ∃ quotientDelta : EuclideanSpace ℝ (QuotientIndex A) → Fin K → ℝ,
    (∀ a, Measurable fun g => quotientDelta g a) ∧
    ∀ x a, delta x a = quotientDelta (quotientObservation A x) a

/-- Simple regret of action `a`, with zero fallback on an empty face. -/
def simpleRegret (A : Finset (Fin K)) (h : Fin K → ℝ) (a : Fin K) : ℝ :=
  (if hA : A.Nonempty then A.sup' hA h else 0) - h a

/-- Risk of a represented randomized selector in the diagonal Gaussian shift. -/
def gaussianSelectorRisk (A : Finset (Fin K)) (v r h : Fin K → ℝ)
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ :=
  ∫ x, ∑ a, delta x a * simpleRegret A h a ∂(activeDiagonalGaussian A h v r)

/-- Extended-real worst-case risk.  Unlike an `ℝ` supremum, this records an
unbounded selector risk as `⊤`. -/
def gaussianSelectorWorstRisk (A : Finset (Fin K)) (v r : Fin K → ℝ)
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ≥0∞ :=
  ⨆ h : Fin K → ℝ, ⨆ _ : (∀ k, k ∉ A → h k = 0), ∫⁻ x, ENNReal.ofReal
    (∑ a, delta x a * simpleRegret A h a) ∂(activeDiagonalGaussian A h v r)

/-- Positive-rate extended-real minimax value. -/
def gaussianInteriorValue (A : Finset (Fin K)) (v r : Fin K → ℝ) : ℝ≥0∞ :=
  sInf {g : ℝ≥0∞ | ∃ delta : (ActiveIndex A → ℝ) → Fin K → ℝ,
    GaussianSelector A delta ∧ g = gaussianSelectorWorstRisk A v r delta}

/-- Lower-semicontinuous extended-real Gaussian value.  Positive rates use the
ordinary experiment; a boundary rate is approached from the positive orthant. -/
def gaussianGlobalValue (A : Finset (Fin K)) (v r : Fin K → ℝ) : ℝ≥0∞ :=
  if ∀ k ∈ A, 0 < r k then gaussianInteriorValue A v r else
    Filter.liminf (fun N : ℕ => gaussianInteriorValue A v
      (fun k => r k + ((N + 1 : ℕ) : ℝ)⁻¹)) Filter.atTop
-- @realizes G_A(v_A,r_A)(extended-real l.s.c. Gaussian minimax value)

/-- Real projection used only on domains where finiteness has been established. -/
def gaussianGlobalValueReal (A : Finset (Fin K)) (v r : Fin K → ℝ) : ℝ :=
  (gaussianGlobalValue A v r).toReal

/-- Extended-real worst risk restricted to a quotient ball. -/
def gaussianSelectorCompactWorstRisk [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M : ℝ)
    (delta : (ActiveIndex A → ℝ) → Fin K → ℝ) : ℝ≥0∞ :=
  ⨆ h : Fin K → ℝ, ⨆ _ : (∀ k, k ∉ A → h k = 0),
    ⨆ _ : quotientNorm A h ≤ M,
    ∫⁻ x, ENNReal.ofReal (∑ a, delta x a * simpleRegret A h a)
      ∂(activeDiagonalGaussian A h v r)

/-- Compact all-selector Gaussian minimax value at radius `M`. -/
def gaussianCompactValue [NeZero K] (A : Finset (Fin K)) (v r : Fin K → ℝ)
    (M : ℝ) : ℝ≥0∞ :=
  sInf {g : ℝ≥0∞ | ∃ delta : (ActiveIndex A → ℝ) → Fin K → ℝ,
    GaussianSelector A delta ∧ g = gaussianSelectorCompactWorstRisk A v r M delta}

/-- Compact invariant-selector value, stated separately for the Hunt--Stein equality. -/
def gaussianInvariantCompactValue [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M : ℝ) : ℝ≥0∞ :=
  sInf {g : ℝ≥0∞ | ∃ delta : (ActiveIndex A → ℝ) → Fin K → ℝ,
    GaussianSelector A delta ∧ LocationInvariantSelector A delta ∧
      g = gaussianSelectorCompactWorstRisk A v r M delta}

def gaussianCompactValueReal [NeZero K] (A : Finset (Fin K))
    (v r : Fin K → ℝ) (M : ℝ) : ℝ := (gaussianCompactValue A v r M).toReal

-- @node: def:gaussian-face-game
/-- Full and compact-quotient Gaussian face-game values. -/
def gaussianFaceGame [NeZero K] (A : Finset (Fin K)) (v r : Fin K → ℝ) (M : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (gaussianGlobalValue A v r, gaussianCompactValue A v r M)
-- @realizes G_{A,M}(v_A,r_A)(compact quotient minimax value)

/-- Own-cluster domain of the Gaussian face game. -/
def GaussianFaceDomain (A : Finset (Fin K)) (v r : Fin K → ℝ) (M : ℝ) : Prop :=
  2 ≤ A.card ∧ (∀ k ∈ A, 0 < v k) ∧ (∀ k ∈ A, 0 ≤ r k) ∧ 0 < M
-- @realizes v_A(active coordinates positive)
-- @realizes r_A(active coordinates nonnegative)
-- @realizes M(positive finite quotient radius)

/-- Finite-simplex membership. -/
def InSimplex (p : Fin K → ℝ) : Prop := (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1

/-- A simplex vector supported on the chosen face, with positive active entries. -/
def InActiveSimplex (A : Finset (Fin K)) (p : Fin K → ℝ) : Prop :=
  InSimplex p ∧ (∀ k, k ∉ A → p k = 0) ∧ ∀ k ∈ A, 0 < p k

/-- Matrix-vector product on the finite policy menu. -/
def matVec (B : Fin K → Fin K → ℝ) (p : Fin K → ℝ) : Fin K → ℝ :=
  fun k => ∑ l, B k l * p l

-- @node: def:face-mechanism-values
/-- Optimized Bernoulli-hit and exact-count face values. -/
def faceMechanismValues [NeZero K] (B : Fin K → Fin K → ℝ)
    (A : Finset (Fin K)) (v : Fin K → ℝ) : ℝ × ℝ :=
  (sInf {g : ℝ | ∃ p, InSimplex p ∧ (∀ k ∈ A, 0 < matVec B p k) ∧
      g = gaussianGlobalValueReal A v (matVec B p)},
    sInf {g : ℝ | ∃ alpha, InActiveSimplex A alpha ∧
      g = gaussianGlobalValueReal A v alpha})
-- @realizes R_{B,A}^\star(min_{p∈Delta_K} G_A(v,(Bp)_A))
-- @realizes R_{CR,A}^\star(min_{a∈Delta_A} G_A(v,a))

/-- Active hit mass and normalized active information vector. -/
def activeHitMass (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ)
    (p : Fin K → ℝ) : ℝ := ∑ k ∈ A, matVec B p k
-- @realizes s_A(p)(sum_{k∈A}(Bp)_k)

/-- Own-cluster range condition for the active exact-hit mass. -/
def ActiveHitMassInterior (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ)
    (p : Fin K → ℝ) : Prop := activeHitMass A B p ∈ Ioo (0 : ℝ) 1
-- @realizes s_A(p)(range (0,1))

def normalizedActiveHits (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ)
    (p : Fin K → ℝ) : Fin K → ℝ :=
  fun k => if k ∈ A then matVec B p k / activeHitMass A B p else 0
-- @realizes a_A(p)((Bp)_A/s_A(p))

def maximumActiveColumnMass [NeZero K] (A : Finset (Fin K)) (B : Fin K → Fin K → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun l => ∑ k ∈ A, B k l
-- @realizes s_{A,\max}(max_l sum_{k∈A} B_kl)

/-- Own-cluster range condition for the largest active column mass. -/
def MaximumActiveColumnMassInterior [NeZero K] (A : Finset (Fin K))
    (B : Fin K → Fin K → ℝ) : Prop :=
  maximumActiveColumnMass A B ∈ Ioo (0 : ℝ) 1
-- @realizes s_{A,\max}(range (0,1))

/-- Two-policy contrast-variance objective. -/
def twoPolicyObjective (B : Fin 2 → Fin 2 → ℝ) (v : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  v 0 / (B 0 1 + (B 0 0 - B 0 1) * t) +
    v 1 / (B 1 1 - (B 1 1 - B 1 0) * t)
-- @realizes F_v(t)(v1/q1(t)+v2/q2(t))
-- @realizes t(first nominal-label share in [0,1])

/-- Admissibility of the two-policy share coordinate. -/
def AdmissibleTwoPolicyShare (t : ℝ) : Prop := t ∈ Icc (0 : ℝ) 1
-- @realizes t(range [0,1])

-- @node: def:two-policy-allocation
/-- The two-policy objective and its leftmost minimizer on `[0,1]`. -/
def twoPolicyAllocation (B : Fin 2 → Fin 2 → ℝ) (v : Fin 2 → ℝ) :
    (ℝ → ℝ) × ℝ × ℝ :=
  let F := twoPolicyObjective B v
  let tStar := sInf {t : ℝ | t ∈ Icc 0 1 ∧ ∀ s ∈ Icc (0 : ℝ) 1, F t ≤ F s}
  let alphaStar := Real.sqrt (v 0) / (Real.sqrt (v 0) + Real.sqrt (v 1))
  (F, tStar, alphaStar)
-- @realizes t^\star(argmin_{t∈[0,1]} F_v(t))

/-- Standard normal density. -/
def standardNormalDensity (x : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-1 / 2 : ℝ) * Real.exp (-(x ^ 2) / 2)
-- @realizes \varphi((2*pi)^(-1/2) exp(-x²/2))

/-- Standard normal distribution function. -/
def standardNormalDistribution (x : ℝ) : ℝ := Causalean.Mathlib.stdNormalCDF x
-- @realizes \Phi(standard normal CDF)

-- @node: lem:gaussian-quotient-reduction
/-- The all-selector value equals the location-invariant quotient value, every
invariant selector factors through reference contrasts, and compact quotient
values increase to the full value. -/
lemma gaussian_quotient_reduction {K : ℕ} [NeZero K]
    (A : Finset (Fin K)) (v r : Fin K → ℝ) (hA : 2 ≤ A.card)
    (hv : ∀ k ∈ A, 0 < v k) (hr : ∀ k ∈ A, 0 < r k) :
    gaussianGlobalValue A v r =
      sInf {g : ℝ≥0∞ | ∃ delta, GaussianSelector A delta ∧
        LocationInvariantSelector A delta ∧
        g = gaussianSelectorWorstRisk A v r delta} ∧
    (∀ delta, GaussianSelector A delta → LocationInvariantSelector A delta →
      MeasurablyFactorsThroughQuotient A delta) ∧
    (∀ h, Measure.map (quotientObservation A) (activeDiagonalGaussian A h v r) =
      quotientGaussianLaw A h v r) ∧
    (∀ M, gaussianCompactValue A v r M = gaussianInvariantCompactValue A v r M) ∧
    (∀ M, gaussianCompactValue A v r M ≤ gaussianGlobalValue A v r) ∧
    (∀ M M', M ≤ M' → gaussianCompactValue A v r M ≤ gaussianCompactValue A v r M') ∧
    Tendsto (fun N : ℕ => gaussianCompactValue A v r N) atTop
      (nhds (gaussianGlobalValue A v r)) := by sorry

-- @node: lem:gaussian-information-order
/-- Homogeneity, information monotonicity, two-sided perturbation modulus,
positive finiteness, and the lower-semicontinuous infinite boundary value. -/
lemma gaussian_information_order {K : ℕ} [NeZero K]
    (A : Finset (Fin K)) (v r r' : Fin K → ℝ) (s xi : ℝ)
    (hA : 2 ≤ A.card) (hv : ∀ k ∈ A, 0 < v k)
    (hr : ∀ k ∈ A, 0 < r k) (hs : 0 < s)
    (horder : ∀ k ∈ A, r k ≤ r' k) (hxi : 0 < xi ∧ xi < 1) :
    gaussianGlobalValueReal A v (fun k => s * r k) =
        s ^ (-1 / 2 : ℝ) * gaussianGlobalValueReal A v r ∧
    gaussianGlobalValueReal A v r' ≤ gaussianGlobalValueReal A v r ∧
    ((∀ k ∈ A, (1 - xi) * r k ≤ r' k ∧ r' k ≤ (1 + xi) * r k) →
      (1 + xi) ^ (-1 / 2 : ℝ) * gaussianGlobalValueReal A v r ≤
          gaussianGlobalValueReal A v r' ∧
        gaussianGlobalValueReal A v r' ≤
          (1 - xi) ^ (-1 / 2 : ℝ) * gaussianGlobalValueReal A v r) ∧
    0 < gaussianGlobalValueReal A v r ∧
    (∃ bound : ℝ, gaussianGlobalValueReal A v r ≤ bound) ∧
    (∀ r0 : Fin K → ℝ, (∀ k ∈ A, 0 ≤ r0 k) →
      (∃ i ∈ A, r0 i = 0) → gaussianGlobalValue A v r0 = ⊤) := by sorry

-- @node: lem:hierarchical-gaussian-screening
/-- Independent Gaussian screening followed by compact retained-subset selectors
gives the displayed exponentially-small noncompact risk envelope, uniformly on
compact positive diagonal-variance cells. -/
lemma hierarchical_gaussian_screening {K : ℕ} [NeZero K]
    (A : Finset (Fin K)) (v r : Fin K → ℝ) (lambda T eta : ℝ)
    (Msub : Finset (Fin K) → ℝ)
    (deltaSub : ∀ S : Finset (Fin K), (ActiveIndex S → ℝ) → Fin K → ℝ)
    (hA : 2 ≤ A.card) (hv : ∀ k ∈ A, 0 < v k)
    (hr : ∀ k ∈ A, 0 < r k) (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hT : 0 < T) (heta : 0 ≤ eta)
    (hM : ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
      2 * Real.sqrt (1 - lambda) * T * Real.sqrt (S.card - 1) ≤ Msub S)
    (hselectors : ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
      GaussianSelector S (deltaSub S) ∧
      LocationInvariantSelector S (deltaSub S) ∧
      (⨆ h ∈ {h | quotientNorm S h ≤ Msub S},
        gaussianSelectorRisk S v r h (deltaSub S)) ≤
          gaussianCompactValueReal S v r (Msub S) + eta) :
    let H := Finset.univ.sup' Finset.univ_nonempty fun S : Finset (Fin K) =>
      if S.Nonempty ∧ S ⊆ A then gaussianCompactValueReal S v r (Msub S) else 0
    ∃ delta : (ActiveIndex A → ℝ) → Fin K → ℝ, GaussianSelector A delta ∧
      H ≤ gaussianGlobalValueReal A v r ∧
      gaussianGlobalValueReal A v r ≤
        (⨆ h : Fin K → ℝ, gaussianSelectorRisk A v r h delta) ∧
      (⨆ h : Fin K → ℝ, gaussianSelectorRisk A v r h delta) ≤
        (1 - lambda) ^ (-1 / 2 : ℝ) *
          (H + eta) +
        2 * (A.card : ℝ) ^ 2 *
          Real.sqrt (2 / lambda) * (A.sup' (Finset.card_pos.mp (by omega)) fun i =>
            Real.sqrt (v i / r i)) / Real.sqrt (2 * Real.pi) *
          Real.exp (-T ^ 2 / (4 / lambda *
            (A.sup' (Finset.card_pos.mp (by omega)) fun i => Real.sqrt (v i / r i)) ^ 2)) ∧
      (∀ c x a, delta (fun k => x k + c) a = delta x a) ∧
      ∀ S : Finset (Fin K), S.Nonempty → S ⊆ A →
        gaussianGlobalValueReal S v r ≤ gaussianGlobalValueReal A v r := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
