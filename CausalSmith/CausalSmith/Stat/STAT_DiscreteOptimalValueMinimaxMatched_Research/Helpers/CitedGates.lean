import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseConstruction

set_option linter.style.longLine false

/-! Explicit cited logical gates. These are propositions, not proved declarations. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory

/-- Cai and Low (2011), Lemma 1 and Section 3.1, arXiv:1105.3039.
Symmetric probability measures on `[-1,1]` match moments through every positive even
degree and attain twice the best absolute-value approximation error; that error is
bounded above and below by universal multiples of the reciprocal degree. -/
-- @node: lem:cai-low-absolute-moment-priors
def CaiLowAbsoluteMomentPriors : Sort 0 :=
  (∀ (K : ℕ) (hK : Even K), 0 < K → ∃ nu0 nu1 : Measure ℝ,
    IsProbabilityMeasure nu0 ∧ IsProbabilityMeasure nu1 ∧
    nu0 (Set.Icc (-1) 1)ᶜ = 0 ∧ nu1 (Set.Icc (-1) 1)ᶜ = 0 ∧
    Measure.map (fun t : ℝ => -t) nu0 = nu0 ∧
    Measure.map (fun t : ℝ => -t) nu1 = nu1 ∧
    (∀ l ≤ K, ∫ t, t ^ l ∂nu1 = ∫ t, t ^ l ∂nu0) ∧
    (∫ t, |t| ∂nu1) - ∫ t, |t| ∂nu0 =
      2 * bestEvenApproxError K) ∧
  ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ (K : ℕ) (hK : Even K), 0 < K →
    c / K ≤ bestEvenApproxError K ∧
      bestEvenApproxError K ≤ C / K
  -- @realizes \(\nu_{0,K}\)(first symmetric prior) @realizes \(\nu_{1,K}\)(second symmetric prior)

/-- Jiao, Han, and Weissman (2018), Theorem 3, equation (24), DOI
10.1109/TIT.2018.2846245. The two-sample Poissonized L1 minimax risk has the stated
large-alphabet lower rate in the displayed sample-size regime. -/
-- @node: lem:jhw-poisson-l1-lower
def JhwPoissonL1Lower : Sort 0 :=
  ∀ c0 C0 : ℝ, 0 < c0 → 0 < C0 → ∃ c1 : ℝ, 0 < c1 ∧ ∀ d n : ℕ, 2 ≤ d →
    c0 * d / Real.log (Real.exp 1 * d) ≤ n →
    Real.log (Real.exp 1 * n) ≤ C0 * Real.log (Real.exp 1 * d) →
    c1 * min 1 (d / (n * Real.log (Real.exp 1 * n))) ≤
      poissonL1FiniteRiskMinimaxRisk n d

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
