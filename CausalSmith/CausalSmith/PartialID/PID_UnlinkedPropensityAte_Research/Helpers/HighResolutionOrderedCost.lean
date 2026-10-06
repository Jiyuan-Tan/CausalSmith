module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionOrderedRelease
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TUniversalPointIdentification

/-! Cost bound for the ordered paired-companding release. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,H,f,hDensity,hOverlap,hfcont,hfpos,k,hk), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionOrderedRelease_worstCaseAmbiguity_le_compandingCost
    {ε mf Mf : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (f : ScoreSpace ε → ℝ) (hDensity : BoundedScoreDensity H f mf Mf)
    (hOverlap : Overlap ε) (hfcont : Continuous f)
    (hfpos : ∀ e, 0 < f e) (k : ℕ) (hk : 0 < k) :
    worstCaseAmbiguity H
        (highResolutionOrderedRelease hOverlap f hfcont hfpos k hk) ≤
      pairedPartitionCost 2 k (highResolutionBeta f)
        (pairedCompandingCell ε (1 - ε) 2 k (highResolutionBeta f))
        (pairedCompandingMidpoint ε (1 - ε) 2 k (highResolutionBeta f)) := by
  let g := highResolutionOrderedRelease hOverlap f hfcont hfpos k hk
  let B := pairedCompandingCell ε (1 - ε) 2 k (highResolutionBeta f)
  let z := pairedCompandingMidpoint ε (1 - ε) 2 k (highResolutionBeta f)
  have hg : Measurable g :=
    highResolutionOrderedRelease_measurable hOverlap f hfcont hfpos k hk
  have hB : IsIntervalPartition ε (1 - ε) k B :=
    highResolutionCompandingCell_partition hOverlap f hfcont hfpos k hk
  have hz : ∀ r s, z r s ∈ Icc ε (1 - ε) :=
    pairedCompandingMidpoint_mem_Icc ε (1 - ε)
      (by linarith [hOverlap.2]) 2 k hk (highResolutionBeta f)
  have hcellNonneg (r : LabelSpace k) (s : Fin 2) (w : ℝ)
      (hw : w ∈ Icc ε (1 - ε)) :
      0 ≤ ∫ x in realScoreCell g r,
        highResolutionBeta f s x w * |x - w| := by
    rw [highResolutionOrderedRelease_realScoreCell
      hOverlap f hfcont hfpos k hk r]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (hB.1 r)] with x hx
    have hβ := highResolutionBeta_pos hOverlap f hfpos s x w
      (by
        rw [← hB.2.2]
        exact Set.mem_iUnion_of_mem r hx) hw
    exact mul_nonneg hβ.le (abs_nonneg _)
  have hinfLe (r : LabelSpace k) (s : Fin 2) :
      sInf {v : ℝ | ∃ w ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f s x w * |x - w|} ≤
        ∫ x in realScoreCell g r,
          highResolutionBeta f s x (z r s) * |x - z r s| := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro v ⟨w, hw, rfl⟩
      exact hcellNonneg r s w hw
    · exact ⟨z r s, hz r s, rfl⟩
  rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
  calc
    (∑ r : LabelSpace k,
        (cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r)) ≤
        ∑ r : LabelSpace k,
          ((∫ x in realScoreCell g r,
              highResolutionBeta f 1 x (z r 1) * |x - z r 1|) +
            ∫ x in realScoreCell g r,
              highResolutionBeta f 0 x (z r 0) * |x - z r 0|) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [sum_cellAbsoluteDeviation_eq_highResolutionInfs
        H f hDensity g hg r hOverlap hfpos]
      exact add_le_add (hinfLe r 1) (hinfLe r 0)
    _ = pairedPartitionCost 2 k (highResolutionBeta f) B z := by
      unfold pairedPartitionCost
      simp only [Fin.sum_univ_two]
      dsimp only [g]
      simp_rw [highResolutionOrderedRelease_realScoreCell
        hOverlap f hfcont hfpos k hk]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,hOverlap,f,hfcont,hfpos,k,hk), this result [establishes the stated mathematical conclusion](goal). -/
lemma optimalKAmbiguity_le_highResolutionOrderedRelease
    {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e)
    (k : ℕ) (hk : 0 < k) :
    optimalKAmbiguity ε k H ≤
      worstCaseAmbiguity H
        (highResolutionOrderedRelease hOverlap f hfcont hfpos k hk) := by
  let g := highResolutionOrderedRelease hOverlap f hfcont hfpos k hk
  have hg : Measurable g :=
    highResolutionOrderedRelease_measurable hOverlap f hfcont hfpos k hk
  unfold optimalKAmbiguity
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro d ⟨q, hq, rfl⟩
    rw [(worstCaseAmbiguity_eq H q hOverlap hq).1]
    exact Finset.sum_nonneg fun r hr => add_nonneg
      (cellAbsoluteDeviation_nonneg H q hOverlap true r)
      (cellAbsoluteDeviation_nonneg H q hOverlap false r)
  · exact ⟨g, hg, rfl⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte
