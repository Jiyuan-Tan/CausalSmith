module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelRateLower
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthTesting
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TUniversalPointIdentification

/-! Finite-label identification lower bounds for honest released-trial intervals. -/

public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,n,H,g,C,hOverlap,hg,α,hHonest), this result [establishes the stated mathematical conclusion](goal). -/
lemma honestProcedure_fairEndpoint_expectedLength_lower {ε : ℝ} {K n : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (C : IntervalProcedure n K)
    (hOverlap : Overlap ε) (hg : Measurable g) (α : ℝ)
    (hHonest : (g, C) ∈ honestProcedures n K H α) :
    ∃ P ∈ CausalLaws H g,
      (1 - 2 * α) * worstCaseAmbiguity H g ≤
        ∫ x, C.length x
          ∂(Measure.pi (fun _ : Fin n => releasedLaw P)) := by
  rcases (worstCaseAmbiguity_eq H g hOverlap hg).2.2.2 with
    ⟨Pminus, Pplus, hminusProb, hplusProb, hminusComp, hplusComp,
      _hminus, _hplus, hgap⟩
  have hminusLaw : Pminus ∈ CausalLaws H g := by
    refine ⟨hminusProb, ?_⟩
    exact
      { probability := hminusComp.probability
        measurableRelease := hminusComp.measurableRelease
        scoreMarginal := hminusComp.scoreMarginal
        randomizedAssignment := hminusComp.randomizedAssignment
        consistency := hminusComp.consistency
        deterministicRelease := hminusComp.deterministicRelease }
  have hplusLaw : Pplus ∈ CausalLaws H g := by
    refine ⟨hplusProb, ?_⟩
    exact
      { probability := hplusComp.probability
        measurableRelease := hplusComp.measurableRelease
        scoreMarginal := hplusComp.scoreMarginal
        randomizedAssignment := hplusComp.randomizedAssignment
        consistency := hplusComp.consistency
        deterministicRelease := hplusComp.deterministicRelease }
  let Prel := halfOutcomeReleasedLaw H g
  let Q := Measure.pi (fun _ : Fin n => Prel)
  let _ : IsProbabilityMeasure Pminus := hminusProb
  let _ : IsProbabilityMeasure (releasedLaw Pminus) :=
    @Measure.isProbabilityMeasure_map _ _ _ _ Pminus hminusProb _
      (by
        exact (by
          unfold releasedRecord label arm observed
          fun_prop : Measurable (releasedRecord (ε := ε) (J := K))).aemeasurable)
  let _ : IsProbabilityMeasure Prel := by
    dsimp [Prel]
    rw [← hminusComp.releasedLaw]
    infer_instance
  let _ : IsProbabilityMeasure Q := inferInstance
  have hcoverMinus :
      1 - α ≤ Q.real {x | C.contains x (ate Pminus)} := by
    change 1 - α ≤
      (Measure.pi (fun _ : Fin n => halfOutcomeReleasedLaw H g)).real
        {x | C.contains x (ate Pminus)}
    rw [← hminusComp.releasedLaw]
    exact hHonest.2 Pminus hminusLaw
  have hcoverPlus :
      1 - α ≤ Q.real {x | C.contains x (ate Pplus)} := by
    change 1 - α ≤
      (Measure.pi (fun _ : Fin n => halfOutcomeReleasedLaw H g)).real
        {x | C.contains x (ate Pplus)}
    rw [← hplusComp.releasedLaw]
    exact hHonest.2 Pplus hplusLaw
  have horder : ate Pminus ≤ ate Pplus := by
    rw [← sub_nonneg]
    rw [hgap]
    rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
    exact Finset.sum_nonneg fun r _ => add_nonneg
      (cellAbsoluteDeviation_nonneg H g hOverlap true r)
      (cellAbsoluteDeviation_nonneg H g hOverlap false r)
  have htest := intervalProcedure_twoPoint_expectedLength C Q Q
    (ate Pminus) (ate Pplus) α horder hcoverMinus hcoverPlus
  have htv : Causalean.Stat.tvDist Q Q = 0 := by
    simp [Causalean.Stat.tvDist]
  refine ⟨Pminus, hminusLaw, ?_⟩
  calc
    (1 - 2 * α) * worstCaseAmbiguity H g =
        (ate Pplus - ate Pminus) *
          (1 - 2 * α - Causalean.Stat.tvDist Q Q) := by rw [hgap, htv]; ring
    _ ≤ ∫ x, C.length x ∂Q := htest
    _ = ∫ x, C.length x
          ∂(Measure.pi (fun _ : Fin n => releasedLaw Pminus)) := by
      dsimp [Q, Prel]
      rw [hminusComp.releasedLaw]

/-- Given [the stated mathematical inputs and assumptions](hyp:K,n,C,Q), this result [establishes the stated mathematical conclusion](goal). -/
lemma intervalProcedure_expectedLength_le_two {K n : ℕ}
    (C : IntervalProcedure n K) (Q : Measure (TrialSample n K))
    [IsProbabilityMeasure Q] :
    (∫ x, C.length x ∂Q) ≤ 2 := by
  have hlenMeas : Measurable C.length := C.measurable_hi.sub C.measurable_lo
  have hlenNonneg (x : TrialSample n K) : 0 ≤ C.length x :=
    sub_nonneg.mpr (C.ordered x)
  have hlenBound (x : TrialSample n K) : C.length x ≤ 2 := by
    dsimp [IntervalProcedure.length]
    linarith [C.lower_bound x, C.upper_bound x]
  have hlenInt : Integrable C.length Q := by
    apply Integrable.of_bound hlenMeas.aestronglyMeasurable 2
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hlenNonneg x)]
    exact hlenBound x
  have hmono := integral_mono hlenInt (integrable_const 2) hlenBound
  simpa [probReal_univ] using hmono

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,n,H,g,C,hOverlap,hg,α,hHonest), this result [establishes the stated mathematical conclusion](goal). -/
lemma honestProcedure_worstCaseExpectedLength_lower {ε : ℝ} {K n : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (C : IntervalProcedure n K)
    (hOverlap : Overlap ε) (hg : Measurable g) (α : ℝ)
    (hHonest : (g, C) ∈ honestProcedures n K H α) :
    (1 - 2 * α) * worstCaseAmbiguity H g ≤
      sSup {u : ℝ | ∃ P ∈ CausalLaws H g,
        u = ∫ x, C.length x
          ∂(Measure.pi (fun _ : Fin n => releasedLaw P))} := by
  let U : Set ℝ := {u : ℝ | ∃ P ∈ CausalLaws H g,
    u = ∫ x, C.length x
      ∂(Measure.pi (fun _ : Fin n => releasedLaw P))}
  obtain ⟨P, hP, hlen⟩ :=
    honestProcedure_fairEndpoint_expectedLength_lower H g C hOverlap hg α hHonest
  have hUbd : BddAbove U := by
    refine ⟨2, ?_⟩
    rintro u ⟨Q, hQ, rfl⟩
    let _ : IsProbabilityMeasure Q := hQ.1
    let _ : IsProbabilityMeasure (releasedLaw Q) :=
      @Measure.isProbabilityMeasure_map _ _ _ _ Q hQ.1 _
        (by
          exact (by
            unfold releasedRecord label arm observed
            fun_prop : Measurable (releasedRecord (ε := ε) (J := K))).aemeasurable)
    let _ : IsProbabilityMeasure
        (Measure.pi (fun _ : Fin n => releasedLaw Q)) := inferInstance
    exact intervalProcedure_expectedLength_le_two C _
  exact hlen.trans (le_csSup hUbd ⟨P, hP, rfl⟩)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,hOverlap,hmf,K,hK,H,f,hf,n,α,hα,g,C,hg,hHonest), this result [establishes the stated mathematical conclusion](goal). -/
lemma honestProcedure_finiteLabel_expectedLength_lower {ε : ℝ}
    (mf : ℝ) (hOverlap : Overlap ε) (hmf : 0 < mf)
    (K : ℕ) (hK : 0 < K)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (f : ScoreSpace ε → ℝ) (hf : LowerScoreDensity H f mf)
    (n : ℕ) (α : ℝ) (hα : α ≤ 1 / 2)
    (g : ScoreSpace ε → LabelSpace K) (C : IntervalProcedure n K)
    (hg : Measurable g) (hHonest : (g, C) ∈ honestProcedures n K H α) :
    (1 - 2 * α) *
        (mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K)) ≤
      sSup {u : ℝ | ∃ P ∈ CausalLaws H g,
        u = ∫ x, C.length x
          ∂(Measure.pi (fun _ : Fin n => releasedLaw P))} := by
  have hamb := worstCaseAmbiguity_finiteLabel_lower mf hOverlap hmf
    K hK H f hf g hg
  exact (mul_le_mul_of_nonneg_left hamb (by linarith)).trans
    (honestProcedure_worstCaseExpectedLength_lower H g C hOverlap hg α hHonest)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
