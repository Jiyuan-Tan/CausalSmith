import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TNuisanceDeletionBernoulli
import Causalean.Stat.CLT.GaussianLimit
import Causalean.Stat.CLT.AsymptoticLinearityVec
import Causalean.Stat.Concentration.Matrix.IidSums
import Mathlib.Probability.CondVar

/-! # Efficient Bernoulli exact-hit estimation -/

open MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:efficient-exact-hit-bernoulli
/-- The calibrated influence coordinates are canonical, have diagonal variance
`tau_k²/q_k`, and yield the full-vector CLT and covariance consistency. -/
theorem efficient_exact_hit_bernoulli {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p : Fin K → ℝ) (m : Fin K → ℕ)
    (h_iid : IidSchedules P0 sampleLaw)
    (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P0 labelLaw assignmentLaw)
    (hmenu : WellFormedMenu n K m) (hp : (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1) :
    let q := (hitMatrix n m p).2
    let mu := assignmentMean P0
    let phi := bernoulliInfluence m q mu
    let Sigma : Fin K → Fin K → ℝ :=
      fun i j => if i = j then sliceVariance P0 (m i) / q i else 0
    let hatSigma := fun C (O : Fin C → Record K n) =>
      empiricalCovariance (fun k => feasibleBernoulliInfluence O m k) O
    (∀ k, InL2Zero (bernoulliObservedLaw P0 p m) (phi k) ∧
      InL2Closure (bernoulliObservedLaw P0 p m)
        {score | ∃ path, BernoulliRegularPath P0 p m path score} (phi k) ∧
      (∀ path score, BernoulliRegularPath P0 p m path score →
        HasDerivAt (fun t => exactSliceWelfare (path t) m k)
          (∫ o, phi k o * score o ∂(bernoulliObservedLaw P0 p m)) 0) ∧
      (∫ o, (phi k o) ^ 2 ∂(bernoulliObservedLaw P0 p m)) =
        sliceVariance P0 (m k) / q k) ∧
    IsDiagonalCovariance Sigma (fun k => sliceVariance P0 (m k) / q k) ∧
    BernoulliCalibratedCLT P0 p m Sigma ∧
    BernoulliCovarianceConsistent P0 p m hatSigma Sigma ∧
    ∀ A : Finset (Fin K), ∀ i ∈ A, ∀ j ∈ A,
      Sigma i j = if i = j then sliceVariance P0 (m i) / q i else 0 := by sorry
-- @realizes \Sigma_B^{(K)}(diag(tau_k²/q_k))
-- @realizes \Sigma_{B,A}(active principal restriction)

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
