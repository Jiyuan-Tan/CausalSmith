import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TSupportRegimeOpenIllegalDichotomy

/-! # Mutual-support illegal-region dichotomy -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

/-- Outside the hinge frontier, the mutual-support divergence ball contains a
stable nonempty open region of binary laws excluded by the SCM mixture class.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hNot), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:open-illegal-dichotomy
theorem open_illegal_dichotomy (e : ℝ) (f : ℝ → ℝ)
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f)
    (hNot : f ∉ hingeClassSet (1 / e)) :
    MutualOpenIllegalDichotomy f e := by
  rcases support_regime_open_illegal_dichotomy e f hPos hf hNot with
    ⟨O, hO, hOne, hSub, hLower, hcase⟩
  refine ⟨O, hO, hOne, hSub, hLower, ?_⟩
  rcases hcase with hnonaffine | haffine
  · left
    refine ⟨hnonaffine.1, ?_⟩
    intro z hz
    exact ⟨hnonaffine.2 z hz |>.2.1, hnonaffine.2 z hz |>.2.2⟩
  · right
    rcases haffine with ⟨b, d, hcd, hzero, hregion⟩
    refine ⟨b, d, hcd, hzero, ?_⟩
    intro z hz
    exact ⟨hregion z hz |>.2.1, hregion z hz |>.2.2⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
