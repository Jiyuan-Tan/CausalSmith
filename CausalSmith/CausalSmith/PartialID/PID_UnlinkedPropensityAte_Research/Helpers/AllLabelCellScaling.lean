module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions

/-! Scaling identity for normalized inverse propensity cell laws. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,r,hq,c), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellWeightLaw_absoluteDeviation {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) (c : ℝ) :
    armCellMass H g a r *
        (∫ w, |w - c| ∂(armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq)) =
      ∫ e in cell g r, |1 - c * armProb a e| ∂H := by
  unfold armCellWeightLaw armCellScoreLaw
  rw [MeasureTheory.integral_map]
  · rw [integral_smul_measure]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hq), one_mul]
    unfold cell
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (by cases a <;> simp [armProb] <;> fun_prop)
      (Filter.Eventually.of_forall fun _ => by finiteness)
      _ (measurableSet_eq_fun hMass.2.2.1 measurable_const)]
    apply integral_congr_ae
    filter_upwards [] with e
    have hp : 0 < armProb a e := by
      rcases e.property with ⟨he0, he1⟩
      cases a <;> simp [armProb] <;> linarith [hOverlap.1]
    rw [ENNReal.toReal_ofReal hp.le]
    simp only [smul_eq_mul]
    rw [abs_sub_comm]
    calc
      armProb a e * |c - (armProb a e)⁻¹| =
          |armProb a e| * |c - (armProb a e)⁻¹| := by rw [abs_of_pos hp]
      _ = |armProb a e * (c - (armProb a e)⁻¹)| := by rw [abs_mul]
      _ = |c * armProb a e - 1| := by
        congr 1
        field_simp
      _ = |1 - c * armProb a e| := abs_sub_comm _ _
  · exact (by cases a <;> simp [armProb] <;> fun_prop)
  · fun_prop

end
end CausalSmith.PartialID.UnlinkedPropensityAte
