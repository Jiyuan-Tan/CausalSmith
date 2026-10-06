module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalAsymptotics
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalNonfallback

/-!
# Uniform nondegeneracy of the critical variance

Equation (16) of the critical studentization roadmap follows from the survival,
intensity, assignment and endpoint-coefficient bounds. The constants here are
independent of the law, including along arbitrary triangular sequences.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The critical scope supplies all the model-class assumptions. -/
-- @node: CriticalScope.modelClass
lemma CriticalScope.modelClass {c : ClassConstants} {P : SubjectLaw}
    (h : CriticalScope c P) : ModelClass c P :=
  SubcriticalScope.modelClass h

/-- Each treatment probability lies in the overlap band and is at most one. -/
-- @node: modelClass_assignment_probability_bounds
lemma modelClass_assignment_probability_bounds (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) : c.pMin ≤ P.p a ∧ P.p a ≤ 1 := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  refine ⟨hP.treatmentOverlap a, ?_⟩
  rw [← hP.assignmentLaw a]
  exact measureReal_le_one

/-- Every endpoint arm coefficient has a positive uniform floor. -/
-- @node: criticalVariance_arm_lower
lemma criticalVariance_arm_lower (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    Real.exp (-c.dMax) * c.lambdaMin / c.gMax ≤
      survival P a 1 * P.lam a 1 / (P.p a * P.g a) := by
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hl := hP.recurrenceBounds a 1 (by norm_num)
  have hp := modelClass_assignment_probability_bounds c P hP a
  have hg := hP.endpointCoefficientBounds a
  have hp0 := c.pMin_pos.trans_le hp.1
  have hg0 := c.gMin_pos.trans_le hg.1
  have hgmax0 := c.gMin_pos.trans c.gMin_lt
  have hden : P.p a * P.g a ≤ c.gMax :=
    (mul_le_mul_of_nonneg_right hp.2 hg0.le).trans (by simpa using hg.2)
  have hnum : Real.exp (-c.dMax) * c.lambdaMin ≤ survival P a 1 * P.lam a 1 :=
    mul_le_mul hs.1 hl.1 c.lambdaMin_pos.le (Real.exp_pos _).le
  exact div_le_div₀ (mul_nonneg (Real.exp_pos _).le (c.lambdaMin_pos.le.trans hl.1))
    hnum (mul_pos hp0 hg0) hden

/-- Every endpoint arm coefficient has a finite uniform ceiling. -/
-- @node: criticalVariance_arm_upper
lemma criticalVariance_arm_upper (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    survival P a 1 * P.lam a 1 / (P.p a * P.g a) ≤
      c.lambdaMax / (c.pMin * c.gMin) := by
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hl := hP.recurrenceBounds a 1 (by norm_num)
  have hp := hP.treatmentOverlap a
  have hg := (hP.endpointCoefficientBounds a).1
  have hl0 := c.lambdaMin_pos.trans_le hl.1
  have hnum : survival P a 1 * P.lam a 1 ≤ c.lambdaMax :=
    (mul_le_mul_of_nonneg_right hs.2 hl0.le).trans (by simpa using hl.2)
  exact div_le_div₀ (c.lambdaMin_pos.trans c.lambdaMin_lt).le hnum
    (mul_pos c.pMin_pos c.gMin_pos)
    (mul_le_mul hp hg c.gMin_pos.le (c.pMin_pos.trans_le hp).le)

/-- Summing the arm floors gives the explicit positive critical variance floor. -/
-- @node: criticalVariance_uniform_lower
lemma criticalVariance_uniform_lower (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) :
    2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax) ≤
      criticalVariance c P := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => criticalVariance_arm_lower c P hP a)
  have h := mul_le_mul_of_nonneg_left hsum (criticalCoefficient_pos_lt_half c).1.le
  simpa [criticalVariance, Finset.sum_const, mul_assoc, mul_left_comm, mul_comm] using h

/-- Summing the arm ceilings gives the explicit finite critical variance ceiling. -/
-- @node: criticalVariance_uniform_upper
lemma criticalVariance_uniform_upper (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) :
    criticalVariance c P ≤
      2 * criticalCoefficient c * (c.lambdaMax / (c.pMin * c.gMin)) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => criticalVariance_arm_upper c P hP a)
  have h := mul_le_mul_of_nonneg_left hsum (criticalCoefficient_pos_lt_half c).1.le
  simpa [criticalVariance, Finset.sum_const, mul_assoc, mul_left_comm, mul_comm] using h

/-- The critical variance is strictly positive for every member of the model class. -/
-- @node: criticalVariance_pos
lemma criticalVariance_pos (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) : 0 < criticalVariance c P := by
  have hfloor : 0 < 2 * criticalCoefficient c *
      (Real.exp (-c.dMax) * c.lambdaMin / c.gMax) :=
    mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (mul_pos (Real.exp_pos _) c.lambdaMin_pos)
        (c.gMin_pos.trans c.gMin_lt))
  exact hfloor.trans_le (criticalVariance_uniform_lower c P hP)

/-- One pair of strictly positive constants bounds the critical variance uniformly. -/
-- @node: criticalVariance_uniform_non_degenerate
lemma criticalVariance_uniform_non_degenerate (c : ClassConstants) :
    ∃ vmin vmax : ℝ, 0 < vmin ∧ 0 < vmax ∧
      ∀ P : SubjectLaw, CriticalScope c P →
        vmin ≤ criticalVariance c P ∧ criticalVariance c P ≤ vmax := by
  refine ⟨2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax),
    2 * criticalCoefficient c * (c.lambdaMax / (c.pMin * c.gMin)), ?_, ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (mul_pos (Real.exp_pos _) c.lambdaMin_pos)
        (c.gMin_pos.trans c.gMin_lt))
  · exact mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (c.lambdaMin_pos.trans c.lambdaMin_lt) (mul_pos c.pMin_pos c.gMin_pos))
  · intro P hP
    exact ⟨criticalVariance_uniform_lower c P hP.modelClass,
      criticalVariance_uniform_upper c P hP.modelClass⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
