import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.ScheduleLawBridge
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.WeakCompactness
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitCR
import Causalean.Stat.Limit.ConvergenceVec
import Mathlib.Topology.Sequences

/-! # Uniform fixed-count rank-set coverage -/

open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:rank-set-coverage-cr
/-- Fixed-count calibrated max-t inversion uniformly covers all tie-aware rank sets
when every reported share and slice variance is nondegenerate. -/
theorem rank_set_coverage_cr {C n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ) (m : Fin K → ℕ)
    (tauLower gamma : ℝ)
    (h_iid : IidSchedules P sampleLaw) (h_labels : CrLabelVector (counts C) labelLaw)
    (h_indep : CrLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_slices : CrExactSlices m P labelLaw assignmentLaw) (h_shares : CrAllShares counts alpha)
    (h_nondegenerate : NondegenerateAllSlices P m tauLower)
    (hmenu : WellFormedMenu n K m) (hcounts : ∀ N, ∑ k, counts N k = N)
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    let hatSigma := fun N (O : Fin N → Record K n) =>
      empiricalCovariance (C := N) (fun k o => if o.1 = k then
        (N : ℝ) / counts N k * (recordWelfare n o - cellMean O o.2.1) else 0) O
    CrCovarianceConsistent P counts m hatSigma
      (fun i j => if i = j then sliceVariance P (m i) / alpha i else 0) ∧
    Filter.liminf (fun N => sInf {prob : ℝ | ∃ Q,
      NondegenerateAllSlices Q m tauLower ∧
      prob = (crObservedLaw (C := N) Q (counts N) m
        {O | rankCoverageEvent (C := N) Q m gamma
          (hatSigma N) O}).toReal}) atTop ≥
      1 - gamma := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
