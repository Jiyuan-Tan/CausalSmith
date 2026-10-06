module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.FrontierSpecifications

/-! # Algebraic transitions and compact bounds for the frontier

The explicit rate exponents give both radius-transition formulas, with positive
gap and agreement at the numerator elbow. Absolute positive finite constants
also satisfy the compact-uniform conditions. These certificates do not use the
unfinished statistical comparison theorems.
-/
public section
noncomputable section
open scoped ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Below the numerator elbow, the projection exponent is the active branch.](goal) Under [the stated assumptions](hyp:hD,hs). -/
-- @node: exponentA_low_branch
lemma exponentA_low_branch (α β : ℝ) (hD : ExponentDomain α β)
    (hs : α + β ≤ 1 / 2) :
    exponentA α β = 2 * (α + β) / (2 * α + 2 * β + 1) := by
  have hα : 0 < α := hD.1.trans hD.2.2.1
  have hd : 0 < 2 * α + 2 * β + 1 := by linarith [hD.1]
  apply min_eq_right
  apply (div_le_iff₀ hd).mpr
  linarith

/-- [At and above the numerator elbow, the parametric exponent is the active branch.](goal) Under [the stated assumptions](hyp:hD,hs). -/
-- @node: exponentA_high_branch
lemma exponentA_high_branch (α β : ℝ) (hD : ExponentDomain α β)
    (hs : 1 / 2 ≤ α + β) : exponentA α β = 1 / 2 := by
  have hα : 0 < α := hD.1.trans hD.2.2.1
  have hd : 0 < 2 * α + 2 * β + 1 := by linarith [hD.1]
  apply min_eq_left
  apply (le_div_iff₀ hd).mpr
  linarith

/-- [The two radius-transition expressions are exact, positive, and agree on the elbow.](goal) Under [the stated assumptions](hyp:hD). -/
-- @node: frontier_elbow_identities
lemma frontier_elbow_identities (α β : ℝ) (hD : ExponentDomain α β) :
    ElbowIdentities α β := by
  have hα : 0 < α := hD.1.trans hD.2.2.1
  have hd : 0 < 2 * α + 2 * β + 1 := by linarith [hD.1]
  have he : 0 < 4 * β + 1 := by linarith [hD.1]
  have hlow (hs : α + β ≤ 1 / 2) :
      exponentA α β - exponentB β =
        2 * (α - β) / ((2 * α + 2 * β + 1) * (4 * β + 1)) := by
    rw [exponentA_low_branch α β hD hs]
    dsimp only [exponentB]
    rw [div_sub_div _ _ (ne_of_gt hd) (ne_of_gt he)]
    congr 1
    ring
  have hhigh (hs : 1 / 2 ≤ α + β) :
      exponentA α β - exponentB β = (1 - 4 * β) / (2 * (4 * β + 1)) := by
    rw [exponentA_high_branch α β hD hs]
    dsimp only [exponentB]
    field_simp [ne_of_gt he]
    ring
  refine ⟨?_, hlow, hhigh, ?_⟩
  · by_cases hs : α + β ≤ 1 / 2
    · rw [hlow hs]
      exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hD.2.2.1)) (mul_pos hd he)
    · rw [hhigh (le_of_lt (lt_of_not_ge hs))]
      exact div_pos (by linarith [hD.2.1]) (mul_pos (by norm_num) he)
  · intro hs
    exact (hlow hs.le).symm.trans (hhigh hs.ge)

/-- [Saturation at the parametric exponent occurs precisely on and above the elbow.](goal) Under [the stated assumptions](hyp:hD). -/
-- @node: exponentA_parametric_iff
lemma exponentA_parametric_iff (α β : ℝ) (hD : ExponentDomain α β) :
    exponentA α β = 1 / 2 ↔ 1 / 2 ≤ α + β := by
  constructor
  · intro h
    by_contra hs
    have hbelow : α + β < 1 / 2 := lt_of_not_ge hs
    rw [exponentA_low_branch α β hD hbelow.le] at h
    have hd : 0 < 2 * α + 2 * β + 1 := by
      have hα := hD.1.trans hD.2.2.1
      linarith [hD.1]
    have heq := (div_eq_iff (ne_of_gt hd)).mp h
    linarith
  · exact exponentA_high_branch α β hD

/-- [Absolute positive finite constants meet all the compact-uniform requirements.](goal) Under [the stated assumptions](hyp:hc). -/
-- @node: frontier_compact_uniform
lemma frontier_compact_uniform (c C : ℝ) (hc : 0 < c) : CompactUniform c C := by
  intro K hK _ _
  rw [hK.image_const c, hK.image_const (1 : ℕ)]
  simp only [csInf_singleton, csSup_singleton]
  refine ⟨hc, ?_, True.intro⟩
  exact lt_of_le_of_lt (iSup_le fun _ => iSup_le fun _ => le_rfl) ENNReal.ofReal_lt_top

end CausalSmith.Stat.LogoddsLowsmoothFrontier
