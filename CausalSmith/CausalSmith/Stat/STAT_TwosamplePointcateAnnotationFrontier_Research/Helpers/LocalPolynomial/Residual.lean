module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.ResidualPropensity

/-!
# Helpers/LocalPolynomial/Residual

Two-channel point-CATE annotation frontier: Helpers/LocalPolynomial/Residual
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the residual projection bounds conclusion](goal) holds. -/
lemma residual_projection_bounds (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ h J, 0 < h → h ≤ 1/2 → 1 ≤ J →
      (∀ u : PolyIdx d, Real.sqrt (∫ x,
        ((designatedPropensity P hP) x*coarseBasis h x u-projOp d h J (fun y => (designatedPropensity P hP) y*coarseBasis h y u) x)^2 ∂locLaw d h) ≤ C*(h/J)^alpha) ∧
      Real.sqrt (∫ x, ((designatedControl P hP) x-projOp d h J (designatedControl P hP) x)^2 ∂locLaw d h) ≤ C*(h/J)^beta := by
  obtain ⟨Cm, hCm, hm⟩ := control_projection_bounds d alpha beta gamma L eps hdom
  obtain ⟨Ce, hCe, he⟩ := propensity_projection_bounds d alpha beta gamma L eps hdom
  let C := max Ce Cm
  have heC : Ce ≤ C := le_max_left _ _
  have hmC : Cm ≤ C := le_max_right _ _
  refine ⟨C, hCe.trans_le heC, ?_⟩
  intro P hP h J hh hh' hJ
  constructor
  · intro u
    exact (he P hP h J hh hh' hJ u).trans
      (mul_le_mul_of_nonneg_right heC (Real.rpow_nonneg
        (div_nonneg hh.le (Nat.cast_nonneg J)) _))
  · exact (hm P hP h J hh hh' hJ).trans
      (mul_le_mul_of_nonneg_right hmC (Real.rpow_nonneg
        (div_nonneg hh.le (Nat.cast_nonneg J)) _))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
