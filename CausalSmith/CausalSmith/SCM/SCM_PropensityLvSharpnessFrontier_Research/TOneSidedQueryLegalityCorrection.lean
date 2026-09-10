import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BinaryGap
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TOneSidedBowMixtureCompleteness

/-! # One-sided legality correction -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Intersecting the one-sided divergence relaxation with the mixture class is
exact; finite-alphabet cap constraints implement that correction, including
strict gaps for generators outside the frontier.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:one-sided-query-legality-correction
theorem oneSided_query_legality_correction {Y : Type*} [MeasurableSpace Y]
    [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (f : ℝ → ℝ) (hPos : StrictPositivity e) (hf : AdmissibleGenerator f) :
    lawfulCorrectionOneSidedSet f e P = mixtureClassOneSidedSet e P ∧
    mixtureClassOneSidedSet e P = bowCompatibleOneSidedSet a e P ∧
    FiniteAlphabetLegality f e true ∧
    (f ∉ hingeClassSet (1 / e) → SuccessIndicatorLegalityGap f e true) := by
  refine ⟨lawfulCorrectionOneSided_eq_mixtureClassOneSided f e P hPos hf, ?_,
    finiteAlphabetLegality_of_admissible f e hPos hf true, ?_⟩
  · exact (bowCompatibleOneSided_eq_mixtureClassOneSided a e P hPos).1.symm
  · exact oneSided_successIndicatorGap_of_openIllegal e f hPos hf

end CausalSmith.SCM.PropensityLvSharpnessFrontier
