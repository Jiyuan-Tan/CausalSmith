import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Basic
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Transport
import Causalean.Stat.Inference.HadamardDeriv
import Causalean.Stat.Limit.Convergence
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Cited logical gates

These named propositions are explicit external inputs. This paper neither proves
them nor hides them behind axioms.
-/

open scoped BigOperators ENNReal
open MeasureTheory Filter Topology ProbabilityTheory
open Causalean.Stat

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

/-- Weak convergence expressed by convergence of integrals against bounded
continuous real-valued test functions. -/
def WeakConverges {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace E] (Xn : ℕ → Ω → E) (Q : Measure E) (μ : Measure Ω) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => ∫ ω, f (Xn n ω) ∂μ) atTop (𝓝 (∫ x, f x ∂Q))

/-- The tight probability law condition is the stated property of the slate-benefit partial-transport model. -/
def TightProbabilityLaw {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (Q : Measure E) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set E, IsCompact C ∧ Q Cᶜ ≤ ε

/-- The supported in condition is the stated property of the slate-benefit partial-transport model. -/
def SupportedIn {E : Type*} [MeasurableSpace E] (Q : Measure E)
    (tangent : Set E) : Prop :=
  Q tangentᶜ = 0

/-- The empirical atom vector is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def empiricalAtomVector {Ω 𝒪 : Type*} [Fintype 𝒪] [DecidableEq 𝒪]
    [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    (O : ℕ → Ω → 𝒪) (Pobs : Measure 𝒪) (n : ℕ) (ω : Ω) : 𝒪 → ℝ :=
  fun o => Real.sqrt n *
    ((n : ℝ)⁻¹ * (∑ r ∈ Finset.range n, if O r ω = o then 1 else 0) -
      Pobs.real {o})

/-- **van der Vaart (1998), Chapter 2, Example 2.18 and the Cramér--Wold
device**, DOI `10.1017/CBO9780511802256`.

For independent sampling from a fixed finite support, the centered empirical
probability vector scaled by the square root of sample size converges weakly to
a centered Gaussian law with multinomial covariance. -/
-- @node: lem:finite-multinomial-central-limit
def FiniteMultinomialCLT : Sort 0 :=
  ∀ {Ω 𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳]
    [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (Pobs : Measure (ObservedDatum 𝒳 K))
    (O : ℕ → Ω → ObservedDatum 𝒳 K),
    IsProbabilityMeasure μ → IsProbabilityMeasure Pobs →
    (∀ n, IidSampling n μ Pobs O) →
      ∃ Q : Measure (ObservedDatum 𝒳 K → ℝ),
        IsGaussian Q ∧
        (∫ z, z ∂Q = 0) ∧
        (∀ a b,
          ∫ z, z a * z b ∂Q =
            if a = b then Pobs.real {a} * (1 - Pobs.real {a})
            else -(Pobs.real {a} * Pobs.real {b})) ∧
        WeakConverges (empiricalAtomVector O Pobs) Q μ
  -- @realizes \mathbb Z_{P_{\mathrm{obs}}}(centered multinomial Gaussian vector)

/-- **Lu, Ding, and Dasgupta (2018), Proposition 2, equation (6), page 546**,
`Treatment effects on ordinal outcomes: Causal estimands and sharp bounds`.

For equal-mass finite ordered marginals, the sharp lower and upper strict-benefit
probabilities over all couplings equal the cumulative cut formulas. -/
-- @node: lem:ordinal-fixed-marginal-strict-benefit
def OrdinalFixedMarginalStrictBenefit : Sort 0 :=
  ∀ {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] {K : ℕ}
    (c : Capacities 𝒳 K) (x : 𝒳),
    ∀ hValid : ValidCapacities c,
    0 < c.mass x → c.q0 x = c.mass x → c.q1 x = c.mass x →
      sInf {v : ℝ | ∃ γ ∈ tiePolytope c hValid x, v = benefitMass γ / c.mass x} =
          max 0 (Finset.univ.sup' Finset.univ_nonempty
            (fun t : Option (Fin K) => match t with
              | none => 0
              | some k => (c.lowerLe x k - c.upperLe x k) / c.mass x)) ∧
      sSup {v : ℝ | ∃ γ ∈ tiePolytope c hValid x, v = benefitMass γ / c.mass x} =
          Finset.univ.inf' Finset.univ_nonempty
            (fun t : Option (Fin K) => match t with
              | none => 1
              | some k => (c.lowerLt x k + c.upperGt x k) / c.mass x)

/-- Tangential sequential Hadamard directional differentiability, including the
domain constraint on every perturbation. -/
def HasTangentialHadamardDirDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (domain tangent : Set E) (φ φ' : E → F) (θ : E) : Prop :=
  θ ∈ domain ∧ ContinuousOn φ' tangent ∧
  ∀ h ∈ tangent, ∀ hn : ℕ → E, ∀ tn : ℕ → ℝ,
    Tendsto hn atTop (𝓝 h) → Tendsto tn atTop (𝓝 0) →
    (∀ n, 0 < tn n) → (∀ n, θ + tn n • hn n ∈ domain) →
    Tendsto (fun n => (tn n)⁻¹ • (φ (θ + tn n • hn n) - φ θ)) atTop (𝓝 (φ' h))

/-- **Fang and Santos (2019), Section 2.3, Assumptions 1--2, Theorem 2.1,
equation (10), and Remark 2.1**, DOI `10.1093/restud/rdy049`.

The Banach-space directional delta method: tangential Hadamard directional
differentiability and weak convergence of the scaled estimator imply the
directional expansion and its continuous-mapping weak limit. -/
-- @node: lem:hadamard-directional-delta-method
def HadamardDirectionalDeltaMethod : Sort 0 :=
  ∀ {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F]
    (μ : Measure Ω) (domain tangent : Set E) (φ φ' extension : E → F)
    (θ0 : E) (θhat : ℕ → Ω → E) (rn : ℕ → ℝ)
    (Q : Measure E),
    IsProbabilityMeasure μ → IsProbabilityMeasure Q →
    HasTangentialHadamardDirDerivAt domain tangent φ φ' θ0 →
    Continuous extension → (∀ h ∈ tangent, extension h = φ' h) →
    (∀ n, Measurable (θhat n)) →
    (∀ n ω, θhat n ω ∈ domain) → Tendsto rn atTop atTop →
    WeakConverges (fun n ω => rn n • (θhat n ω - θ0)) Q μ →
    TightProbabilityLaw Q → SupportedIn Q tangent →
    IsLittleOp
      (fun n ω => ‖rn n • (φ (θhat n ω) - φ θ0) -
        extension (rn n • (θhat n ω - θ0))‖)
      (fun _ => 1) μ ∧
    WeakConverges
      (fun n ω => rn n • (φ (θhat n ω) - φ θ0))
      (Q.map extension) μ

end CausalSmith.PartialID.SlateBenefitPartialTransport
