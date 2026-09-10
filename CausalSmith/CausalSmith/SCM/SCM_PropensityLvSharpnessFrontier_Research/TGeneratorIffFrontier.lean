import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Frontier
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BinaryWitness
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TSupportRegimeOpenIllegalDichotomy

/-! # Mutual-support generator exactness frontier -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory

/-- Universal exactness, full-support binary exactness, and hinge-frontier
membership are equivalent in the mutual-support regime.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:generator-iff-frontier
theorem generator_exactness_iff_hinge (e : ℝ) (f : ℝ → ℝ)
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f) :
    (UniversalMutualExact f e ↔ BinaryMutualExact f e) ∧
      (BinaryMutualExact f e ↔ f ∈ hingeClassSet (1 / e)) := by
  have huniv_binary : UniversalMutualExact f e → BinaryMutualExact f e := by
    intro h p hp
    exact h Bool inferInstance inferInstance (binaryLaw p)
      (binaryLaw_isProbabilityMeasure p ⟨hp.1.le, hp.2.le⟩)
  have hhinge_univ : f ∈ hingeClassSet (1 / e) → UniversalMutualExact f e := by
    intro hhinge Z mZ hZ P hP
    let _ : IsProbabilityMeasure P := hP
    exact hinge_mutual_exactAt f e P hPos hhinge
  have hbinary_hinge : BinaryMutualExact f e → f ∈ hingeClassSet (1 / e) := by
    intro hbinary
    by_contra hnot
    obtain ⟨O, hOpen, hOne, hInside, hSide, hcases⟩ :=
      support_regime_open_illegal_dichotomy e f hPos hf hnot
    obtain ⟨z, hz⟩ := hOne
    have hp : z.1 ∈ Set.Ioo (0 : ℝ) 1 := (hInside hz).1
    have hexact := hbinary z.1 hp
    rcases hcases with hslack | hzero
    · have hbad := (hslack.2 z hz).2.1
      rw [hexact] at hbad
      exact hbad.2 hbad.1
    · obtain ⟨b, d, hcd, hg, hbadAll⟩ := hzero
      have hbad := (hbadAll z hz).2.1
      rw [hexact] at hbad
      exact hbad.2 hbad.1
  constructor
  · exact ⟨huniv_binary, fun hb => hhinge_univ (hbinary_hinge hb)⟩
  · exact ⟨hbinary_hinge, fun hh => huniv_binary (hhinge_univ hh)⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
