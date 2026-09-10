import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.ApproximateBridge
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.BoundaryPrior
import Causalean.Stat.Minimax.LeCam

/-!
# Paper-faithful approximate-vector fuzzy hypotheses

This module packages the construction before the exact-simplex bridge.  One
distribution is fixed, while independent moment-matched coordinate priors are
used for the other distribution and then conditioned on having total mass
close to one.  The package records exactly the target separation and
prior-predictive total-variation control consumed by Le Cam's method.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- Average the approximate fixed-`q` Poisson experiment over a prior on raw
vectors. -/
noncomputable def approximateMixtureObservationLaw (t : ℝ≥0) (d : ℕ)
    (epsilon : ℝ) (q : ProbabilityVector d)
    (π : Measure (ApproximateProbabilityVector d epsilon)) :
    Measure (TwoSampleCounts d) :=
  π.bind fun w => approximateFixedQSampleLawAt t w q

/-- Two conditioned approximate-vector priors form a fuzzy witness when their
targets concentrate in separated clouds and their observation mixtures are
close. -/
structure ApproximateFuzzyWitness (t : ℝ≥0) (d : ℕ) (epsilon : ℝ)
    (q : ProbabilityVector d) where
  /-- Lower-target prior. -/
  prior0 : Measure (ApproximateProbabilityVector d epsilon)
  /-- Upper-target prior. -/
  prior1 : Measure (ApproximateProbabilityVector d epsilon)
  /-- The lower prior is a probability measure. -/
  prior0_probability : IsProbabilityMeasure prior0
  /-- The upper prior is a probability measure. -/
  prior1_probability : IsProbabilityMeasure prior1
  /-- Center of the lower target cloud. -/
  center0 : ℝ
  /-- Center of the upper target cloud. -/
  center1 : ℝ
  /-- Radius of both target clouds. -/
  radius : ℝ
  /-- The target radius is positive. -/
  radius_pos : 0 < radius
  /-- The two target clouds are separated. -/
  target_separated : center0 + 2 * radius ≤ center1 - 2 * radius
  /-- The lower target is concentrated. -/
  target0_concentrated : (15 : ℝ≥0∞) / 16 ≤ prior0
    {w | |approximateVectorL1 w q - center0| ≤ radius}
  /-- The upper target is concentrated. -/
  target1_concentrated : (15 : ℝ≥0∞) / 16 ≤ prior1
    {w | |approximateVectorL1 w q - center1| ≤ radius}
  /-- The lower prior-predictive law is a probability measure. -/
  mixture0_probability :
    IsProbabilityMeasure (approximateMixtureObservationLaw t d epsilon q prior0)
  /-- The upper prior-predictive law is a probability measure. -/
  mixture1_probability :
    IsProbabilityMeasure (approximateMixtureObservationLaw t d epsilon q prior1)
  /-- The two prior-predictive laws are close in total variation. -/
  mixture_tv : Causalean.Stat.tvDist
    (approximateMixtureObservationLaw t d epsilon q prior0)
    (approximateMixtureObservationLaw t d epsilon q prior1) ≤ 1 / 4

/-- An approximate fuzzy witness forces the fixed-`q` approximate minimax risk
to be at least `radius²/8`. -/
theorem approximateFuzzyWitness_minimax_lower {t : ℝ≥0} {d : ℕ}
    {epsilon : ℝ} {q : ProbabilityVector d}
    (W : ApproximateFuzzyWitness t d epsilon q) :
    W.radius ^ 2 / 8 ≤ approximateFixedQMinimaxRiskAt t d epsilon q := by
  sorry

/-- In the growing-alphabet regime, the one-sided and interior scalar priors,
independent coordinate products, Hoeffding concentration, and conditioning on
the approximate-simplex event produce a fixed-`q` fuzzy witness at the
large-alphabet rate. -/
theorem exists_approximateMomentMatchedFuzzyWitness (n d : ℕ)
    (hd : 8 ≤ d)
    (hn : (d : ℝ) /
      (100 * Real.log (Real.exp 1 * (d : ℝ))) ≤ (n : ℝ))
    (hlog : Real.log (Real.exp 1 * (n : ℝ)) ≤
      4 * Real.log (Real.exp 1 * (d : ℝ))) :
    ∃ (epsilon : ℝ) (q : ProbabilityVector d)
      (W : ApproximateFuzzyWitness (2 * (n : ℝ≥0)) d epsilon q),
      0 < epsilon ∧ epsilon < 1 / 2 ∧ epsilon ≤ W.radius / 10 ∧
      (1 / 1000 : ℝ) * Real.sqrt (largeAlphabetL1Rate n d) ≤ W.radius := by
  sorry

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
