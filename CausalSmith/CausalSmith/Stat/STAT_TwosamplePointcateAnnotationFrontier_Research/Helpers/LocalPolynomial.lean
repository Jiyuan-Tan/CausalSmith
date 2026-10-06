module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.Basis
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.Residual
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.Taylor

/-!
# Helpers/LocalPolynomial

Two-channel point-CATE annotation frontier: Helpers/LocalPolynomial
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


-- @node: lem:local-polynomial-projection-facts
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the local polynomial projection facts conclusion](goal) holds. -/
lemma local_polynomial_projection_facts (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ h J, 0 < h → h ≤ 1/2 → 1 ≤ J →
      (∃ theta : PolyIdx d → ℝ,
        (∀ x ∈ locCube d h, |tau P hP x - pv h theta x| ≤ C*h^gamma) ∧
        Real.sqrt (∑ u, theta u^2) ≤ C ∧ pv h theta (x0 d) = tau P hP (x0 d) ∧
        (∀ x ∈ locCube d h, pv h theta x = taylorPoly (tau P hP) (Nat.ceil gamma - 1) x)) ∧
      (∀ x ∈ locCube d h, Real.sqrt (∑ u : PolyIdx d, (coarseBasis h x u)^2) ≤ C) ∧
      (∀ x ∈ locCube d h, (∫ xp, |fineKernel d h J x xp| ∂locLaw d h) ≤ C) ∧
      (∫ p, (fineKernel d h J p.1 p.2)^2 ∂(locLaw d h).prod (locLaw d h)) =
        (Fintype.card (PolyIdx d) : ℝ)*(J:ℝ)^d ∧
      (∀ u : PolyIdx d, Real.sqrt (∫ x,
        ((designatedPropensity P hP) x*coarseBasis h x u-projOp d h J (fun y => (designatedPropensity P hP) y*coarseBasis h y u) x)^2 ∂locLaw d h) ≤ C*(h/J)^alpha) ∧
      Real.sqrt (∫ x, ((designatedControl P hP) x-projOp d h J (designatedControl P hP) x)^2 ∂locLaw d h) ≤ C*(h/J)^beta := by
  obtain ⟨Ct, hCt, ht⟩ := taylor_coefficient_bounds d alpha beta gamma L eps hdom
  obtain ⟨Cb, hCb, hb⟩ := kernel_basis_bounds d alpha beta gamma L eps hdom
  obtain ⟨Cr, hCr, hr⟩ := residual_projection_bounds d alpha beta gamma L eps hdom
  let C := max Ct (max Cb Cr)
  have hTC : Ct ≤ C := le_max_left _ _
  have hBC : Cb ≤ C := (le_max_left Cb Cr).trans (le_max_right Ct _)
  have hRC : Cr ≤ C := (le_max_right Cb Cr).trans (le_max_right Ct _)
  refine ⟨C, hCt.trans_le hTC, ?_⟩
  intro P hP h J hh hh' hJ
  obtain ⟨theta, herr, htheta, hcenter, htaylor⟩ := ht P hP h hh hh'
  obtain ⟨hcoarse, hrow, htrace⟩ := hb h J hh hh' hJ
  obtain ⟨he, hmu⟩ := hr P hP h J hh hh' hJ
  have hhgamma : 0 ≤ h ^ gamma := Real.rpow_nonneg hh.le _
  have hdelta : 0 ≤ h / (J : ℝ) := div_nonneg hh.le (Nat.cast_nonneg J)
  refine ⟨⟨theta, ?_, htheta.trans hTC, hcenter, htaylor⟩, ?_, ?_, htrace, ?_, ?_⟩
  · intro x hx
    exact (herr x hx).trans (mul_le_mul_of_nonneg_right hTC hhgamma)
  · intro x hx
    exact (hcoarse x hx).trans hBC
  · intro x hx
    exact (hrow x hx).trans hBC
  · intro u
    exact (he u).trans (mul_le_mul_of_nonneg_right hRC (Real.rpow_nonneg hdelta _))
  · exact hmu.trans (mul_le_mul_of_nonneg_right hRC (Real.rpow_nonneg hdelta _))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
