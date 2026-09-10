import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.ScheduleLawBridge
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TNuisanceDeletionCR

/-! # Active-face fixed-count exact-hit limit -/

open scoped BigOperators
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: prop:efficient-exact-hit-cr-face
/-- Positive shares are required only on the declared active face; no limit is
asserted for unallocated inactive coordinates. -/
theorem efficient_exact_hit_cr_face {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (tauLower : ℝ) (Sigma : Fin K → Fin K → ℝ)
    (h_iid : IidSchedules P0 sampleLaw)
    (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : CrLabelVector (counts C) labelLaw)
    (h_indep : CrLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_shares : CrActiveShares counts alpha A)
    (h_slices : CrExactSlices m P0 labelLaw assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower)
    (hmenu : WellFormedMenu n K m) (hcounts : ∀ N, ∑ k, counts N k = N)
    (hA : 2 ≤ A.card)
    (hargmax : ∀ k, k ∈ A ↔
      ∀ j, exactSliceWelfare P0 m j ≤ exactSliceWelfare P0 m k) :
    (∀ i ∈ A, ∀ j ∈ A, Sigma i j = if i = j then sliceVariance P0 (m i) / alpha i else 0) ∧
    (∀ t : Fin K → ℝ, (∀ k, k ∉ A → t k = 0) →
      Tendsto (fun C => ∫ O : Fin C → Record K n,
        Real.cos (∑ k, t k * (Real.sqrt C *
          ((calibratedEstimator O m A).1 k - exactSliceWelfare P0 m k)))
          ∂(crObservedLaw P0 (counts C) m)) atTop
        (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)))) ∧
      Tendsto (fun C => ∫ O : Fin C → Record K n,
        Real.sin (∑ k, t k * (Real.sqrt C *
          ((calibratedEstimator O m A).1 k - exactSliceWelfare P0 m k)))
          ∂(crObservedLaw P0 (counts C) m)) atTop (nhds 0)) ∧
    CrActiveCovarianceConsistent P0 counts m A
      (fun N O => empiricalCovariance (C := N) (fun k o => if o.1 = k then
        (N : ℝ) / counts N k * (recordWelfare n o - cellMean O o.2.1) else 0) O)
      Sigma := by sorry
-- @realizes \Sigma_{CR,A}(active diag(tau_k²/alpha_k))

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
