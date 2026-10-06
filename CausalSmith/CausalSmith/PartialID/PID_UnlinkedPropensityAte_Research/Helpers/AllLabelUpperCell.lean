module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelCellScaling
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelCouplingRange
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawEndpointConstruction

/-!
# Universal upper bound for all-label cell endpoint gaps

This file bounds each normalized quantile-product cell range by the
corresponding unnormalized reciprocal-score absolute deviation, including
cells of zero arm mass.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

private lemma allLabel_memLp_id_of_support_Icc
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (b : ℝ) (h : μ (Icc 0 b)ᶜ = 0) : MemLp (fun x : ℝ => x) 2 μ := by
  apply memLp_of_bounded
  · rw [ae_iff]
    exact h
  · fun_prop

private lemma allLabel_centerSet_nonempty {ε : ℝ} (hOverlap : Overlap ε) :
    (Icc ((1 - ε)⁻¹) ε⁻¹).Nonempty := by
  refine ⟨ε⁻¹, ?_, le_rfl⟩
  exact (inv_le_inv₀ (by linarith [hOverlap.2]) hOverlap.1).mpr
    (by linarith [hOverlap.2])

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCell_quantileEndpoint_gap_le_absoluteDeviation {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J) :
    (if hq : 0 < armCellMass H g a r then
        armCellMass H g a r *
          ∫ u in (0 : ℝ)..1,
            generalizedQuantile
                (armCellOutcomeLaw Prel hMass.2.1 a r
                  (by rw [hMass.2.2.2 a r]; exact hq)) u *
              generalizedQuantile
                (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) u
      else 0) -
      (if hq : 0 < armCellMass H g a r then
        armCellMass H g a r *
          ∫ u in (0 : ℝ)..1,
            generalizedQuantile
                (armCellOutcomeLaw Prel hMass.2.1 a r
                  (by rw [hMass.2.2.2 a r]; exact hq)) u *
              generalizedQuantile
                (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) (1 - u)
      else 0) ≤ cellAbsoluteDeviation H g a r := by
  by_cases hq : 0 < armCellMass H g a r
  · simp only [hq, dif_pos]
    let Y := armCellOutcomeLaw Prel hMass.2.1 a r
      (by rw [hMass.2.2.2 a r]; exact hq)
    let W := armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq
    letI : IsProbabilityMeasure H := hMass.1
    letI : IsProbabilityMeasure Prel := hMass.2.1
    letI : IsProbabilityMeasure Y :=
      armCellOutcomeLaw_isProbabilityMeasure Prel a r
        (by rw [hMass.2.2.2 a r]; exact hq)
    letI : IsProbabilityMeasure
        (armCellScoreLaw H hMass.1 g hMass.2.2.1 a r hq) :=
      armCellScoreLaw_isProbabilityMeasure H g hMass.2.2.1 hOverlap a r hq
    letI : IsProbabilityMeasure W := by
      dsimp [W, armCellWeightLaw]
      exact Measure.isProbabilityMeasure_map (by
        cases a <;> simp [armProb] <;> fun_prop)
    have hYsup : Y (Icc 0 1)ᶜ = 0 := by
      dsimp [Y, armCellOutcomeLaw]
      rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
      have hpre : (fun z : Observation J => (z.2.2 : ℝ)) ⁻¹' (Icc 0 1)ᶜ = ∅ := by
        ext z
        exact iff_false_intro (fun hz => hz z.2.2.property)
      rw [hpre]
      simp
    have hWsup : W (Icc 0 ε⁻¹)ᶜ = 0 := by
      dsimp [W, armCellWeightLaw]
      rw [Measure.map_apply (by
        cases a <;> simp [armProb] <;> fun_prop) measurableSet_Icc.compl]
      have hpre : (fun e : ScoreSpace ε => (armProb a e)⁻¹) ⁻¹'
          (Icc 0 ε⁻¹)ᶜ = ∅ := by
        ext e
        apply iff_false_intro
        intro he
        apply he
        have hp : ε ≤ armProb a e := by
          rcases e.property with ⟨he0, he1⟩
          cases a <;> simp [armProb] <;> linarith
        have hpa : 0 < armProb a e := lt_of_lt_of_le hOverlap.1 hp
        exact ⟨inv_nonneg.mpr hpa.le, (inv_le_inv₀ hpa hOverlap.1).mpr hp⟩
      rw [hpre]
      simp
    have hY2 : MemLp (fun y : ℝ => y) 2 Y :=
      allLabel_memLp_id_of_support_Icc Y 1 hYsup
    have hW2 : MemLp (fun w : ℝ => w) 2 W :=
      allLabel_memLp_id_of_support_Icc W ε⁻¹ hWsup
    let C : Set ℝ := Icc ((1 - ε)⁻¹) ε⁻¹
    have hC : C.Nonempty := allLabel_centerSet_nonempty hOverlap
    have hgap := monotoneCoupling_product_gap_le_sInf_absoluteDeviation
      Y W hYsup hY2 hW2 C hC
    rw [product_expectation_comonotoneCoupling_interval Y W hY2 hW2,
      product_expectation_countermonotoneCoupling_interval Y W] at hgap
    have hbelow : BddBelow
        {v : ℝ | ∃ c ∈ C, v = ∫ w, |w - c| ∂W} := by
      refine ⟨0, ?_⟩
      rintro v ⟨c, hc, rfl⟩
      exact integral_nonneg fun _ => abs_nonneg _
    unfold cellAbsoluteDeviation
    apply le_csInf
    · rcases hC with ⟨c, hc⟩
      exact ⟨∫ e in cell g r, |1 - c * armProb a e| ∂H, c, hc, rfl⟩
    · intro v hv
      rcases hv with ⟨c, hc, rfl⟩
      calc
        armCellMass H g a r *
              (∫ u in (0 : ℝ)..1,
                generalizedQuantile Y u * generalizedQuantile W u) -
            armCellMass H g a r *
              (∫ u in (0 : ℝ)..1,
                generalizedQuantile Y u * generalizedQuantile W (1 - u)) =
            armCellMass H g a r *
              ((∫ u in (0 : ℝ)..1,
                  generalizedQuantile Y u * generalizedQuantile W u) -
                ∫ u in (0 : ℝ)..1,
                  generalizedQuantile Y u * generalizedQuantile W (1 - u)) := by ring
        _ ≤ armCellMass H g a r *
              sInf {v : ℝ | ∃ d ∈ C, v = ∫ w, |w - d| ∂W} :=
          mul_le_mul_of_nonneg_left hgap hq.le
        _ ≤ armCellMass H g a r * (∫ w, |w - c| ∂W) :=
          mul_le_mul_of_nonneg_left (csInf_le hbelow ⟨c, hc, rfl⟩) hq.le
        _ = ∫ e in cell g r, |1 - c * armProb a e| ∂H :=
          armCellWeightLaw_absoluteDeviation
            H g Prel hMass hOverlap a r hq c
  · simp [hq]
    unfold cellAbsoluteDeviation
    apply le_csInf
    · rcases allLabel_centerSet_nonempty hOverlap with ⟨c, hc⟩
      exact ⟨∫ e in cell g r, |1 - c * armProb a e| ∂H, c, hc, rfl⟩
    · intro v hv
      rcases hv with ⟨c, hc, rfl⟩
      exact integral_nonneg fun _ => abs_nonneg _

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma muUpper_sub_muLower_le_sum_cellAbsoluteDeviation {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) :
    muUpper H g Prel hMass a - muLower H g Prel hMass a ≤
      ∑ r : LabelSpace J, cellAbsoluteDeviation H g a r := by
  unfold muUpper muLower
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun r _ =>
    armCell_quantileEndpoint_gap_le_absoluteDeviation
      H g Prel hMass hOverlap a r

end
end CausalSmith.PartialID.UnlinkedPropensityAte
