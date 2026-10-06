module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Legality

/-! # ATE target properties of the normalized pair -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier

-- @node: tau_range
/-- A binary-outcome ATE is in the unit interval for every full law. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma tau_range {d : ℕ} (P : FullLaw d) : tau P ∈ Set.Icc (-1) 1 := by
  classical
  have hsum : (∑ w : FullAtom d, fullMass P w) = 1 := by
    unfold fullMass
    rw [← ENNReal.toReal_sum (fun w _ => P.pmf.apply_ne_top w)]
    rw [← tsum_fintype (L := SummationFilter.unconditional (FullAtom d)), P.pmf.tsum_coe]
    norm_num
  have hnonneg (w : FullAtom d) : 0 ≤ fullMass P w := ENNReal.toReal_nonneg
  have hterm (w : FullAtom d) :
      -(fullMass P w) ≤
        fullMass P w * ((if w.Y1 then (1 : ℝ) else 0) -
          (if w.Y0 then 1 else 0)) ∧
      fullMass P w * ((if w.Y1 then (1 : ℝ) else 0) -
          (if w.Y0 then 1 else 0)) ≤ fullMass P w := by
    cases w.Y1 <;> cases w.Y0 <;> simp_all
  unfold tau
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun w _ => (hterm w).1)
    simp only [Finset.sum_neg_distrib, hsum] at h
    exact h
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun w _ => (hterm w).2)
    simpa [hsum] using h

end CausalSmith.Stat.MarNearcompleteFrontier
