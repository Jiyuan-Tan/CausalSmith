import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Basic
import Causalean.Stat.Inference.HadamardDeriv
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Cited logical gates

Explicit assumption-shaped interfaces for the two cited results that this
paper does not prove.  They are propositions, not axioms or sorry-backed
theorems.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators ENNReal
open MeasureTheory Set Filter Topology

/-- Hadamard directional differentiability restricted to a tangential set. -/
def HasHadamardDirDerivTangentially
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : E → F) (phi' : E → F) (theta : E) (tangent : Set E) : Prop :=
  ∀ h ∈ tangent, ∀ hn : ℕ → E, ∀ tn : ℕ → ℝ,
    Tendsto hn atTop (𝓝 h) → (∀ n, hn n ∈ tangent) →
    Tendsto tn atTop (𝓝 0) → (∀ n, 0 < tn n) →
    Tendsto (fun n => (tn n)⁻¹ • (phi (theta + tn n • hn n) - phi theta))
      atTop (𝓝 (phi' h))

/-- Fang and Santos (2019), Theorem 2.1 (`th:delta`): a tight weak limit
supported on the tangential set is carried through a Hadamard directionally
differentiable map.

Authors: Zheng Fang and Andres Santos. Year: 2019. Locator: Theorem 2.1.
Handle: arXiv:1404.3763; DOI 10.1093/restud/rdy049. -/
-- @node: lem:hadamard-directional-delta-method
def HadamardDirectionalDeltaMethod : Sort 0 :=
  ∀ (E F Ω : Type*) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
    (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
    (_ : MeasurableSpace E) (_ : TopologicalSpace E)
    (_ : MeasurableSpace F) (_ : TopologicalSpace F)
    (_ : MeasurableSpace Ω) (mu : Measure Ω) (Q : Measure E)
    (phi : E → F) (phi' : E → F) (theta : E) (tangent : Set E)
    (thetaHat : ℕ → Ω → E) (rate : ℕ → ℝ),
    IsProbabilityMeasure mu → IsProbabilityMeasure Q →
    HasHadamardDirDerivTangentially phi phi' theta tangent →
    Continuous phi' → Measurable phi' →
    IsTightMeasureSet {Q} → Q tangent = 1 → Tendsto rate atTop atTop →
    WeakConvergence mu (fun n ω => rate n • (thetaHat n ω - theta)) Q →
    WeakConvergence mu
      (fun n ω => rate n • (phi (thetaHat n ω) - phi theta)) (Q.map phi')

/-- The Euclidean norm on finite real coordinates. -/
noncomputable def finiteEuclideanNorm {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ j, (x j) ^ 2)

/-- Raič (2019), Theorem 1.1, formula (1.2): the explicit multivariate
Berry--Esseen bound for measurable convex sets under identity total
covariance.  No singular-covariance conclusion is included.

Author: Martin Raič. Year: 2019. Locator: Theorem 1.1, p. 2825, formula
(1.2). Handle: arXiv:1802.06475v4; DOI 10.3150/18-BEJ1072. -/
-- @node: lem:raic-multivariate-berry-esseen-convex-sets
def RaicMultivariateBerryEsseenConvexSets : Sort 0 :=
  ∀ (d : ℕ) (I Ω : Type*) (_ : Countable I) (_ : MeasurableSpace Ω)
    (mu : Measure Ω) (X : I → Ω → (Fin d → ℝ))
    (gamma : Measure (Fin d → ℝ)),
    IsProbabilityMeasure mu → IsProbabilityMeasure gamma →
    ProbabilityTheory.iIndepFun X mu →
    (∀ i j, Measurable fun ω => X i ω j) →
    (∀ i j, ∫ ω, X i ω j ∂mu = 0) →
    (∀ a b : Fin d → ℝ,
      ∑' i, ∫ ω, (∑ j, a j * X i ω j) * (∑ j, b j * X i ω j) ∂mu =
        ∑ j, a j * b j) →
    ProbabilityTheory.IsGaussian gamma →
    (∀ j, ∫ x, x j ∂gamma = 0) →
    (∀ a b : Fin d → ℝ,
      ∫ x, (∑ j, a j * x j) * (∑ j, b j * x j) ∂gamma = ∑ j, a j * b j) →
    ∀ A : Set (Fin d → ℝ), MeasurableSet A → Convex ℝ A →
      |ENNReal.toReal (mu {ω | (fun j => ∑' i, X i ω j) ∈ A}) -
          ENNReal.toReal (gamma A)| ≤
        (42 * Real.sqrt (Real.sqrt d) + 16) *
          ∑' i, ∫ ω, (finiteEuclideanNorm (X i ω)) ^ 3 ∂mu

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
