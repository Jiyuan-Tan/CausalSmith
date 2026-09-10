import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.QueryEndpoints
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BinaryGap
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TBowMixtureCompleteness

/-! # Mutual-support legality correction and query endpoints -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- The lawful intersection is the exact bow class, with essential-infimum and
essential-supremum expectation endpoints and the finite-alphabet cap rule.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hmeas,hbounded), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:query-legality-correction
theorem query_legality_correction {Y : Type*} [MeasurableSpace Y]
    [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (f : ℝ → ℝ) (h : Y → ℝ) (hPos : StrictPositivity e)
    (hf : AdmissibleGenerator f)
    (hmeas : Measurable h)
    (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    lawfulCorrectionSet f e P = mixtureClassSet e P ∧
    mixtureClassSet e P = bowCompatibleSet a e P ∧
    sInf {θ : ℝ | ∃ Q ∈ mixtureClassSet e P, θ = ∫ x, h x ∂Q} =
      lowerQueryEndpoint e P h ∧
    sSup {θ : ℝ | ∃ Q ∈ mixtureClassSet e P, θ = ∫ x, h x ∂Q} =
      upperQueryEndpoint e P h ∧
    FiniteAlphabetLegality f e false ∧
    (f ∉ hingeClassSet (1 / e) → SuccessIndicatorLegalityGap f e false) := by
  refine ⟨lawfulCorrection_eq_mixtureClass f e P hPos hf, ?_,
    mixtureClass_integral_sInf P e h hPos hmeas hbounded,
    mixtureClass_integral_sSup P e h hPos hmeas hbounded,
    finiteAlphabetLegality_of_admissible f e hPos hf false, ?_⟩
  · exact (bowCompatible_eq_mixtureClass a e P hPos).1.symm
  · exact mutual_successIndicatorGap_of_openIllegal e f hPos hf
  -- @realizes h(measurable essentially bounded query)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
