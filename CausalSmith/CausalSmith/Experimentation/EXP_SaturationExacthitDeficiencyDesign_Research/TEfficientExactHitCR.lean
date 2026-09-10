import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.ScheduleLawBridge
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TNuisanceDeletionCR
import Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT
import Causalean.Stat.Concentration.Matrix.IidSums
import Mathlib.Probability.CondVar

/-! # Full-vector fixed-count exact-hit limit -/

open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:efficient-exact-hit-cr
/-- With every limiting stratum share positive, the full calibrated vector has
diagonal covariance `tau_k²/alpha_k`, a Gaussian limit, and consistent covariance. -/
theorem efficient_exact_hit_cr {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ) (m : Fin K → ℕ)
    (h_iid : IidSchedules P0 sampleLaw)
    (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : CrLabelVector (counts C) labelLaw)
    (h_indep : CrLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_shares : CrAllShares counts alpha)
    (h_slices : CrExactSlices m P0 labelLaw assignmentLaw)
    (hmenu : WellFormedMenu n K m)
    (hcounts : ∀ N, ∑ k, counts N k = N) :
    let Sigma := fun i j : Fin K =>
      if i = j then sliceVariance P0 (m i) / alpha i else 0
    let hatSigma := fun N (O : Fin N → Record K n) =>
      empiricalCovariance (C := N) (fun k o => if o.1 = k then
        (N : ℝ) / counts N k * (recordWelfare n o - cellMean O o.2.1) else 0) O
    CrCalibratedCLT P0 counts m Sigma ∧
    CrCovarianceConsistent P0 counts m hatSigma Sigma ∧
    ∃ remainder : ∀ N, (Fin N → Record K n) → Fin K → ℝ,
      (∀ eps > 0, Tendsto (fun (N : ℕ) => crObservedLaw P0 (counts N) m
        {O | ∃ k, eps < |remainder N O k|}) atTop (nhds 0)) ∧
      ∀ (N : ℕ) (O : Fin N → Record K n) k, Real.sqrt N *
        ((calibratedEstimator (C := N) O m Finset.univ).1 k - exactSliceWelfare P0 m k) =
        (Real.sqrt N)⁻¹ * ∑ c, crInfluence (counts N) m (assignmentMean P0) c k (O c) +
          remainder N O k := by sorry
-- @realizes \Sigma_{CR}^{(K)}(diag(tau_k²/alpha_k))

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
