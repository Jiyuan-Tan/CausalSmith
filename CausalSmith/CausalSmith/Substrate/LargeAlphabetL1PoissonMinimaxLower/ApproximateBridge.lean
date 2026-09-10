import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Basic

/-!
# Approximate probability vectors and the exact-simplex bridge

The moment construction naturally produces nonnegative vectors whose total
mass is close to one, rather than exactly one.  This module defines that raw
experiment and states the reusable normalization/conditioning comparison
which transfers a lower bound back to exact probability vectors at a reduced
Poisson intensity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- A nonnegative vector whose total mass differs from one by at most
`epsilon`. -/
abbrev ApproximateProbabilityVector (d : ℕ) (epsilon : ℝ) :=
  {w : Fin d → ℝ≥0 // |((∑ i, w i : ℝ≥0) : ℝ) - 1| ≤ epsilon}

/-- Normalize a raw nonnegative vector, using a designated atom only when its
total mass is zero. -/
noncomputable def normalizedApproximateVector {d : ℕ} (i0 : Fin d)
    (w : Fin d → ℝ≥0) : ProbabilityVector d := by
  classical
  let s : ℝ≥0 := ∑ i, w i
  by_cases hs : s = 0
  · exact ⟨fun i => if i = i0 then 1 else 0, by simp⟩
  · exact ⟨fun i => w i / s, by
      change (∑ i, w i / s) = 1
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, show ∑ i, w i = s by rfl, mul_inv_cancel₀ hs]⟩

/-- The raw `L₁` target between an approximate vector and an exact
probability vector. -/
noncomputable def approximateVectorL1 {d : ℕ} {epsilon : ℝ}
    (w : ApproximateProbabilityVector d epsilon) (q : ProbabilityVector d) : ℝ :=
  ∑ i, |(w.1 i : ℝ) - (q.1 i : ℝ)|

/-- At intensity `t`, the raw fixed-`q` experiment observes independent
Poisson counts with means `t wᵢ` and `t qᵢ`. -/
noncomputable def approximateFixedQSampleLawAt (t : ℝ≥0) {d : ℕ}
    {epsilon : ℝ} (w : ApproximateProbabilityVector d epsilon)
    (q : ProbabilityVector d) : Measure (TwoSampleCounts d) :=
  (Measure.pi fun i : Fin d => poissonMeasure (t * w.1 i)).prod
    (Measure.pi fun i : Fin d => poissonMeasure (t * q.1 i))

/-- Squared risk in the raw approximate-vector experiment. -/
noncomputable def approximateFixedQL1RiskAt (t : ℝ≥0) {d : ℕ}
    {epsilon : ℝ} (w : ApproximateProbabilityVector d epsilon)
    (q : ProbabilityVector d) (est : MeasurableEstimator d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((est.1 z - approximateVectorL1 w q) ^ 2)
    ∂approximateFixedQSampleLawAt t w q

/-- The real minimax risk over approximate vectors with fixed exact `q`. -/
noncomputable def approximateFixedQMinimaxRiskAt (t : ℝ≥0) (d : ℕ)
    (epsilon : ℝ) (q : ProbabilityVector d) : ℝ :=
  (⨅ est : MeasurableEstimator d,
    ⨆ w : ApproximateProbabilityVector d epsilon,
      approximateFixedQL1RiskAt t w q est).toReal

/-- The exact-simplex fixed-`q` minimax risk at intensity `t`. -/
noncomputable def exactFixedQMinimaxRiskAt (t : ℝ≥0) (d : ℕ)
    (q : ProbabilityVector d) : ℝ :=
  (⨅ est : MeasurableEstimator d,
    ⨆ p : ProbabilityVector d,
      poissonizedTwoSampleL1RiskAt t p q est).toReal

/-- Normalizing a nonzero approximate vector changes its `L₁` target by at
most its total-mass error. -/
theorem approximateVectorL1_normalize_error {d : ℕ} {epsilon : ℝ}
    (i0 : Fin d) (w : ApproximateProbabilityVector d epsilon)
    (q : ProbabilityVector d) :
    |probabilityVectorL1 (normalizedApproximateVector i0 w.1) q -
      approximateVectorL1 w q| ≤
      epsilon := by
  sorry

/-- Approximate-vector minimax risk transfers to exact probability vectors at
one quarter of the available mass-adjusted intensity, up to the Poisson lower
tail and normalization errors.

This is the paper-faithful conditioning bridge: condition on the total count,
apply the estimator to the normalized vector, and use the preceding target
comparison.  The second fixed-`q` count sample is ancillary and is resampled
at the required intensity. -/
theorem approximateFixedQMinimaxRisk_bridge (t : ℝ≥0) (d : ℕ)
    (epsilon : ℝ) (q : ProbabilityVector d)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    (1 / 4 : ℝ) * approximateFixedQMinimaxRiskAt t d epsilon q -
        (1 / 2 : ℝ) * Real.exp (-(t : ℝ) * (1 - epsilon) / 8) -
        (1 / 2 : ℝ) * epsilon ^ 2 ≤
      exactFixedQMinimaxRiskAt (t * ⟨(1 - epsilon) / 4, by positivity⟩) d q := by
  sorry

/-- Restricting the full two-unknown parameter space to a fixed second
distribution can only decrease minimax risk. -/
theorem exactFixedQMinimaxRiskAt_le_twoUnknown (t : ℝ≥0) (d : ℕ)
    (q : ProbabilityVector d) :
    exactFixedQMinimaxRiskAt t d q ≤
      poissonizedTwoUnknownL1MinimaxRiskAt t d := by
  sorry

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
