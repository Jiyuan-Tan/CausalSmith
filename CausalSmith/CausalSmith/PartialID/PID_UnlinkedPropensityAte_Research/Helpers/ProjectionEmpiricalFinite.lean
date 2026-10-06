module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEmpirical

/-! Finite mass of the empirical submeasures used in the projection. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: empiricalTrialCells_finite
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,x,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma empiricalTrialCells_finite {J n : ℕ} (x : TrialSample n J)
    (a : ArmSpace) (r : LabelSpace J) :
    (empiricalTrialCells x a r) Set.univ < ⊤ := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [empiricalTrialCells]
  unfold empiricalTrialCells
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  apply ENNReal.mul_lt_top
  · simp [Nat.pos_of_ne_zero hn]
  · apply ENNReal.sum_lt_top.mpr
    intro i _
    split_ifs <;> simp

-- @node: empiricalScoreCells_finite
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,g,x,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma empiricalScoreCells_finite {ε : ℝ} {J m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (x : Fin m → ScoreSpace ε)
    (a : ArmSpace) (r : LabelSpace J) :
    (empiricalScoreCells g x a r) Set.univ < ⊤ := by
  classical
  unfold empiricalScoreCells
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  split_ifs
  · simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator, Set.mem_univ, if_pos, Pi.one_apply, smul_eq_mul, mul_one]
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (by
      have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      exact_mod_cast (Nat.ne_of_gt hm))
  · simp

end CausalSmith.PartialID.UnlinkedPropensityAte
