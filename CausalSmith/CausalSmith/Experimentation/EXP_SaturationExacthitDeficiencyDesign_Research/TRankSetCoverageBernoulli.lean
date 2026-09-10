import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.WeakCompactness
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitBernoulli
import Causalean.Stat.Concentration.Matrix.IidSums
import Causalean.Stat.Limit.ConvergenceVec
import Mathlib.Topology.Sequences

/-! # Uniform Bernoulli rank-set coverage -/

open scoped BigOperators ENNReal
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:rank-set-coverage-bernoulli
/-- Calibrated max-t inversion covers every tie-aware rank set uniformly over
nondegenerate bounded schedule laws, with the explicit empty-cell fallback bound. -/
theorem rank_set_coverage_bernoulli {C n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p : Fin K → ℝ) (m : Fin K → ℕ) (tauLower gamma : ℝ)
    (h_iid : IidSchedules P sampleLaw) (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P labelLaw assignmentLaw)
    (h_tauLower : 0 < tauLower ∧ tauLower ≤ 1 / 2)
    (hmenu : WellFormedMenu n K m) (hp : (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1)
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    let q := (hitMatrix n m p).2
    let phi := bernoulliInfluence m q (assignmentMean P)
    let hatSigma := fun N (O : Fin N → Record K n) => empiricalCovariance
      (fun k => feasibleBernoulliInfluence O m k) O
    BernoulliCovarianceConsistent P p m hatSigma
      (fun i j => if i = j then sliceVariance P (m i) / q i else 0) ∧
    Filter.liminf (fun N => sInf {prob : ℝ | ∃ Q,
      NondegenerateAllSlices Q m tauLower ∧
      prob = ((Measure.pi fun _ : Fin N => bernoulliObservedLaw Q p m)
        {O | rankCoverageEvent Q m gamma
          (hatSigma N) O}).toReal}) atTop ≥ 1 - gamma ∧
    (Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)
      {O | hasEmptyTargetCell O m = true} ≤
        ENNReal.ofReal (∑ k, sliceCard n (m k) *
          Real.exp (-(C : ℝ) * q k / sliceCard n (m k))) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
