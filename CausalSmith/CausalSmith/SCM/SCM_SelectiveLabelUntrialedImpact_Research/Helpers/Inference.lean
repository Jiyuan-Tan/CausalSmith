import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.BinomialCountLaw
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Duality
import Causalean.Stat.CLT.GaussianLimit
import Causalean.Stat.Inference.HadamardDeriv
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Sampling, projection, and directional-limit constructions

Multinomial counts from the reused i.i.d. sample bundle, exact projection
plug-in endpoints, the projection-composed derivative, and atomic-tie
subsampling schedules.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set

variable {O T OBlind : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]

-- @env: S4
-- @realizes O_i(i.i.d. categorical observations)
-- @realizes p(population observable law)
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
  [MeasurableSingletonClass O] {μ : Measure Ω} {P : Measure O}
  (S : Causalean.Stat.IIDSample Ω O μ P)

/-- The multinomial cell-count vector. -/
noncomputable def multinomialCounts (S : Causalean.Stat.IIDSample Ω O μ P)
    (n : ℕ) (ω : Ω) (o : O) : ℕ :=
  iidCellCount S o n ω -- @realizes N(N_o = sum of cell indicators)

/-- The empirical categorical proportion. -/
noncomputable def empiricalLaw (S : Causalean.Stat.IIDSample Ω O μ P)
    (n : ℕ) (ω : Ω) (o : O) : ℝ :=
  multinomialCounts S n ω o / (n : ℝ) -- @realizes p_hat(N/n)

/-- The multinomial covariance matrix `diag(p)-p pᵀ`. -/
def multinomialCovariance (p : O → ℝ) : Matrix O O ℝ := fun i j =>
  (if i = j then p i else 0) - p i * p j
  -- @realizes Sigma_p(diag(p) - p pᵀ)

/-- A centered Gaussian law with the multinomial covariance form. -/
def IsMultinomialGaussian (p : O → ℝ) (Q : Measure (O → ℝ)) : Prop :=
  ProbabilityTheory.IsGaussian Q ∧
    (∫ x, x ∂Q) = 0 ∧
    ∀ i j, (∫ x, x i * x j ∂Q) = multinomialCovariance p i j
  -- @realizes G_p(centered Gaussian with covariance Sigma_p)

/-- Existence of the centered Gaussian law with multinomial covariance. -/
lemma exists_multinomialGaussian (p : O → ℝ)
    (hp : ∀ o, 0 ≤ p o) (hsum : ∑ o, p o = 1) :
    ∃ Q : Measure (O → ℝ), IsMultinomialGaussian p Q := by
  sorry

/-- The centered Gaussian multinomial limit law. -/
noncomputable def multinomialGaussianLaw (p : O → ℝ) : Measure (O → ℝ) :=
  if h : (∀ o, 0 ≤ p o) ∧ ∑ o, p o = 1 then
    Classical.choose (exists_multinomialGaussian p h.1 h.2)
  else 0
  -- @realizes G_p(concrete centered Gaussian law)

/-- Metric projection onto a set, with zero used only when no minimizer exists. -/
noncomputable def metricProjection (s : Set (O → ℝ)) (x : O → ℝ) : O → ℝ :=
  if h : ∃ y ∈ s, ∀ z ∈ s, ‖x - y‖ ≤ ‖x - z‖ then Classical.choose h else 0
  -- @realizes Pi_O(Euclidean argmin over O_poly)

/-- Project an empirical law onto the observable polytope and evaluate `(L,U)`. -/
-- @node: def:projection-endpoint-estimator
noncomputable def projectionEndpointEstimator (G : SLCCIncidence O T OBlind)
    (pHat : O → ℝ) : ℝ × ℝ :=
  sharpEndpointPrograms G (metricProjection (observablePolytope G) pHat)
  -- @realizes p_tilde(Pi_O p_hat)
  -- @realizes theta_hat(theta(Pi_O p_hat))

/-- The closed radial tangent cone of the observable polytope at `p`. -/
noncomputable def polyhedralTangentCone (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) : Set (O → ℝ) :=
  closure {z | ∃ a : ℝ, 0 ≤ a ∧ ∃ v ∈ observablePolytope G, z = a • (v - p)}
  -- @realizes T_O_p(closed radial cone at p)

/-- The metric projection of a direction onto the tangent cone. -/
noncomputable def tangentProjection (G : SLCCIncidence O T OBlind)
    (p g : O → ℝ) : O → ℝ := metricProjection (polyhedralTangentCone G p) g

/-- The slope coordinate of an unnormalised dual pair. -/
def slopeValue (z : O → ℝ) (aLam : ℝ × (O → ℝ)) : ℝ :=
  ∑ o, aLam.2 o * z o

/-- Projection-composed lower and upper endpoint directional map. -/
-- @node: def:projection-composed-derivative
noncomputable def projectionComposedDerivative (G : SLCCIncidence O T OBlind)
    (p g : O → ℝ) : ℝ × ℝ :=
  let z := tangentProjection G p g
  (sSup (slopeValue z '' lowerOptimalFace G p),
    sInf (slopeValue z '' upperOptimalFace G p))
  -- @realizes Gamma_p_prime(max/min active dual slopes after tangent projection)

/-- The explicit cube-root subsample schedule. -/
noncomputable def subsampleSize (n : ℕ) : ℕ :=
  max 1 ⌊Real.rpow n (1 / 3 : ℝ)⌋₊ -- @realizes m_n(max(1,floor(n^(1/3))))

/-- The explicit vanishing upper-quantile slack. -/
noncomputable def quantileSlack (n : ℕ) (alpha : ℝ) : ℝ :=
  min (alpha / 2) (Real.rpow n (-(1 / 12 : ℝ)))
  -- @realizes eta_n(min(alpha/2,n^(-1/12)))

/-- A finite-fan package used by the atomic-tie theorem.  Its arguments are
the fan and closure generated in that theorem's explicit hypotheses. -/
structure AtomicTieData (O : Type*) where
  fan : Finset (Set (O → ℝ))
  restrictions : Finset (O → ℝ)
  matrixRows : Finset (List (O → ℝ))
  fixedLawConstant : ℝ
  m : ℕ → ℕ
  eta : ℕ → ℝ
  conditionalLowerQuantile : ℕ → ℝ
  witnessLaw : O → ℝ

/-- Package the refined fan, finite row-family, fixed-law Berry--Esseen
constant, schedules, conditional lower quantile, and witness law. -/
-- @node: def:atomic-tie-subsampling-handle
noncomputable def atomicTieHandle
    (fan : Finset (Set (O → ℝ))) (restrictions : Finset (O → ℝ))
    (matrixRows : Finset (List (O → ℝ))) (constant alpha : ℝ)
    (criticalValue : ℕ → ℝ) (pDagger : O → ℝ) : AtomicTieData O :=
  { fan := fan
    restrictions := restrictions
    matrixRows := matrixRows
    fixedLawConstant := max 0 constant
    m := subsampleSize
    eta := fun n => quantileSlack n alpha
    conditionalLowerQuantile := criticalValue -- @realizes c_sub(lower conditional subsampling quantile)
    witnessLaw := pDagger }

/-- The exact categorical-proportion weak convergence statement.  This is the
locally discharged specialization of the Causalean multivariate CLT.

Citation: Guilherme Duarte, Noam Finkelstein, Dean Knox, Jonathan Mummolo, and
Ilya Shpitser (2024), Appendix E; arXiv:2109.13471,
DOI 10.1080/01621459.2023.2216909. -/
-- @node: lem:finite-multinomial-clt
lemma finite_multinomial_clt
    (G : SLCCIncidence O T OBlind) (p : O → ℝ)
    (hIID : IidFiniteSampling μ P S G p) :
    WeakConvergence μ
      (fun n ω o => Real.sqrt n * (empiricalLaw S n ω o - p o))
      (multinomialGaussianLaw p) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
