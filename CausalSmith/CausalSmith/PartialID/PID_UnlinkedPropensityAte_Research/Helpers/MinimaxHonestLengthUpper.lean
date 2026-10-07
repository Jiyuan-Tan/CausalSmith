module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.InferenceMidpointProcedure
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompatibilityFullLawConstruction

/-! Outer-infimum upper bound from the explicit midpoint interval. -/

public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

private lemma intervalProcedure_expectedLength_mem_Icc
    {K n : ℕ} (C : IntervalProcedure n K)
    (Q : Measure (Observation K)) [IsProbabilityMeasure Q] :
    (∫ x, C.length x ∂Measure.pi (fun _ : Fin n => Q)) ∈ Icc (0 : ℝ) 2 := by
  let μ := Measure.pi (fun _ : Fin n => Q)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hlenInt : Integrable C.length μ := by
    apply Integrable.of_bound
      (C.measurable_hi.sub C.measurable_lo).aestronglyMeasurable 2
    filter_upwards [] with x
    have hlo := C.lower_bound x
    have hord := C.ordered x
    have hhi := C.upper_bound x
    change |C.hi x - C.lo x| ≤ 2
    rw [abs_of_nonneg (sub_nonneg.mpr hord)]
    linarith
  constructor
  · apply integral_nonneg
    exact fun x => sub_nonneg.mpr (C.ordered x)
  · change (∫ x, C.length x ∂μ) ≤ 2
    calc
      (∫ x, C.length x ∂μ) ≤ ∫ _x, (2 : ℝ) ∂μ := by
        apply integral_mono hlenInt (integrable_const _)
        intro x
        have hlo := C.lower_bound x
        have hhi := C.upper_bound x
        unfold IntervalProcedure.length
        linarith
      _ = 2 := by simp

private lemma innerExpectedLengthSup_nonneg
    {ε : ℝ} {K n : ℕ} (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace K) (C : IntervalProcedure n K) :
    0 ≤ sSup {u : ℝ | ∃ P ∈ CausalLaws H g,
      u = ∫ x, C.length x ∂Measure.pi (fun _ : Fin n => releasedLaw P)} := by
  let U : Set ℝ := {u : ℝ | ∃ P ∈ CausalLaws H g,
    u = ∫ x, C.length x ∂Measure.pi (fun _ : Fin n => releasedLaw P)}
  by_cases hU : U.Nonempty
  · obtain ⟨u, hu⟩ := hU
    rcases hu with ⟨P, hP, rfl⟩
    letI : IsProbabilityMeasure P := hP.1
    have hrecord : Measurable (releasedRecord (ε := ε) (J := K)) := by
      unfold releasedRecord label arm observed
      fun_prop
    letI : IsProbabilityMeasure (releasedLaw P) := by
      unfold releasedLaw
      exact Measure.isProbabilityMeasure_map hrecord.aemeasurable
    have hnonneg := (intervalProcedure_expectedLength_mem_Icc C (releasedLaw P)).1
    apply hnonneg.trans
    apply le_csSup
    · refine ⟨2, ?_⟩
      rintro v ⟨Q, hQ, rfl⟩
      letI : IsProbabilityMeasure Q := hQ.1
      have hrecordQ : Measurable (releasedRecord (ε := ε) (J := K)) := by
        unfold releasedRecord label arm observed
        fun_prop
      letI : IsProbabilityMeasure (releasedLaw Q) := by
        unfold releasedLaw
        exact Measure.isProbabilityMeasure_map hrecordQ.aemeasurable
      exact (intervalProcedure_expectedLength_mem_Icc C (releasedLaw Q)).2
    · exact ⟨P, hP, rfl⟩
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    change 0 ≤ sSup U
    rw [hUempty]
    simp

private lemma equalWidth_causalLaws_nonempty {ε : ℝ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (K : ℕ) (hK : 0 < K) :
    (CausalLaws H (equalWidthRelease ε K hK)).Nonempty := by
  let g := equalWidthRelease ε K hK
  let Prel := halfOutcomeReleasedLaw H g
  have hg : Measurable g := equalWidthRelease_measurable ε K hK
  have hMass : CompatibleCellMasses H g Prel :=
    halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
  letI : IsProbabilityMeasure Prel := hMass.2.1
  let P := reconstructedFullLaw H g Prel hg
  have hP := reconstructedFullLaw_compatibleCausalLaw H g Prel hg hMass hOverlap
  have hRandom : RandomizedCausalLaw H g P :=
    ⟨hP.probability, hP.measurableRelease, hP.scoreMarginal,
      hP.randomizedAssignment, hP.consistency, hP.deterministicRelease⟩
  exact ⟨P, hP.probability, hRandom⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,H,n,K,hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma minimaxHonestLength_midpoint_upper {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K) :
    minimaxHonestLength n K H α ≤
      midpointLengthConstant ε α *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) := by
  let CI := midpointInterval hOverlap hα n K hn hK
  let R := midpointLengthConstant ε α *
    ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹)
  let V : Set ℝ := {v : ℝ | ∃ gC ∈ honestProcedures n K H α,
    v = sSup {u : ℝ | ∃ P ∈ CausalLaws H gC.1,
      u = ∫ x, gC.2.length x
        ∂Measure.pi (fun _ : Fin n => releasedLaw P)}}
  have hVbelow : BddBelow V := by
    refine ⟨0, ?_⟩
    rintro v ⟨gC, hgC, rfl⟩
    exact innerExpectedLengthSup_nonneg H gC.1 gC.2
  have hhonest : (equalWidthRelease ε K hK, CI) ∈
      honestProcedures n K H α :=
    equalWidth_midpointInterval_honest hOverlap hα H n K hn hK
  let U : Set ℝ := {u : ℝ | ∃ P ∈ CausalLaws H (equalWidthRelease ε K hK),
    u = ∫ x, CI.length x ∂Measure.pi (fun _ : Fin n => releasedLaw P)}
  have hUne : U.Nonempty := by
    obtain ⟨P, hP⟩ := equalWidth_causalLaws_nonempty hOverlap H K hK
    refine ⟨∫ x, CI.length x ∂Measure.pi (fun _ : Fin n => releasedLaw P),
      P, hP, rfl⟩
  have hUsup : sSup U ≤ R := by
    apply csSup_le hUne
    rintro u ⟨P, hP, rfl⟩
    letI : IsProbabilityMeasure P := hP.1
    have hrecord : Measurable (releasedRecord (ε := ε) (J := K)) := by
      unfold releasedRecord label arm observed
      fun_prop
    letI : IsProbabilityMeasure (releasedLaw P) := by
      unfold releasedLaw
      exact Measure.isProbabilityMeasure_map hrecord.aemeasurable
    exact midpointInterval_expectedLength_le hOverlap hα n K hn hK (releasedLaw P)
  unfold minimaxHonestLength
  change sInf V ≤ R
  calc
    sInf V ≤ sSup U := by
      apply csInf_le hVbelow
      exact ⟨(equalWidthRelease ε K hK, CI), hhonest, rfl⟩
    _ ≤ R := hUsup

end
end CausalSmith.PartialID.UnlinkedPropensityAte
