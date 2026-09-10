import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitBernoulli
import Causalean.Experimentation.DesignBased.HT.Variance

/-! # Strict refinement of the nominal-label HOS estimator -/

open scoped BigOperators
open MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

-- @node: thm:han-strict-refinement
/-- The published nominal-label HT expression equals its exact-hit form and its
asymptotic variance weakly exceeds the nominal calibrated and pooled calibrated bounds. -/
theorem han_strict_refinement {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (O : Fin C → Record K n) (p : Fin K → ℝ) (m : Fin K → ℕ) (k : Fin K)
    (h_iid : IidSchedules P0 sampleLaw)
    (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P0 labelLaw assignmentLaw)
    (hmenu : WellFormedMenu n K m) (hp : (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1)
    (hpk : 0 < p k) :
    let eta := nominalHitRate n p m k
    let q := (hitMatrix n m p).2 k
    let U := exactSliceWelfare P0 m k
    let Qnom := nominalTargetHitLaw P0 p m k
    ((hosEstimator P0 O p m).1 k =
      ((C : ℝ) * eta)⁻¹ * ∑ c,
        if (O c).1 = k ∧ (O c).2.1 ∈ exactSlice n (m k)
        then recordWelfare n (O c) else 0) ∧
    (∀ o, (hosEstimator P0 O p m).2.1 k o =
      eta⁻¹ * (if o.1 = k ∧ o.2.1 ∈ exactSlice n (m k)
        then recordWelfare n o else 0) - U) ∧
    (∫ o, ((hosEstimator P0 O p m).2.1 k o) ^ 2
      ∂(bernoulliObservedLaw P0 p m)) =
      (sliceVariance P0 (m k) + betweenAssignmentVariance P0 m k) / eta +
        U ^ 2 * (eta⁻¹ - 1) ∧
    RecordAsymptoticallyLinear
      (fun N => Measure.pi fun _ : Fin N => bernoulliObservedLaw P0 p m)
      (fun N records => (hosEstimator P0 records p m).1 k) U
      ((hosEstimator P0 O p m).2.1 k) ∧
    RegularNominalInfluence P0 p m k ((hosEstimator P0 O p m).2.2 k) ∧
    (∫ o, ((hosEstimator P0 O p m).2.2 k o) ^ 2 ∂Qnom) =
      sliceVariance P0 (m k) / eta ∧
    (∃ nominalEstimator : ∀ N, (Fin N → Record K n) → ℝ,
      (∀ N records, nominalEstimator N records =
        nominalCalibratedEstimator records m k) ∧
      RecordAsymptoticallyLinear
        (fun N => Measure.pi fun _ : Fin N => bernoulliObservedLaw P0 p m)
        nominalEstimator U ((hosEstimator P0 O p m).2.2 k) ∧
      RegularNominalInfluence P0 p m k ((hosEstimator P0 O p m).2.2 k) ∧
      (∫ o, ((hosEstimator P0 O p m).2.2 k o) ^ 2 ∂Qnom) =
        sliceVariance P0 (m k) / eta) ∧
    (∀ influence, InL2Zero Qnom influence →
      (∀ path score, NominalRegularPath P0 p m k path score →
        HasDerivAt (fun t => exactSliceWelfare (path t) m k)
          (∫ o, influence o * score o ∂Qnom) 0) →
      (∫ o, ((hosEstimator P0 O p m).2.2 k o) ^ 2
        ∂Qnom) ≤ ∫ o, (influence o) ^ 2 ∂Qnom) ∧
    (q > eta ∧ 0 < sliceVariance P0 (m k) →
      sliceVariance P0 (m k) / q < sliceVariance P0 (m k) / eta) ∧
    (0 < betweenAssignmentVariance P0 m k →
      sliceVariance P0 (m k) / eta <
        (sliceVariance P0 (m k) + betweenAssignmentVariance P0 m k) / eta +
          U ^ 2 * (eta⁻¹ - 1)) := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
