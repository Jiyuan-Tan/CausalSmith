module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Projection
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-! # Adapter for the public cosine-projection approximation theorem -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Extend a function on the covariate subtype to the real line. Only its
values on `[0,1]` are used by the study definitions. -/
def covariateExtension (f : Covariate → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

/-- [The covariate Extension apply result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:f,x). Under [the stated assumptions](hyp:x). -/
@[simp]
lemma covariateExtension_apply (f : Covariate → ℝ) (x : Covariate) :
    covariateExtension f x = f x := by
  simp [covariateExtension, x.property]
/-- [The covariate Extension continuous On result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:f,hf). Under [the stated assumptions](hyp:hf). -/

lemma covariateExtension_continuousOn {f : Covariate → ℝ} (hf : Continuous f) :
    ContinuousOn (covariateExtension f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert hf using 1
  funext x
  exact covariateExtension_apply f x
/-- [The cosine Basis study result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:x). -/

lemma cosineBasis_study (j : ℕ) (x : Covariate) :
    cosineBasis j x =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineBasis j x := by
  rfl
/-- [The uniform Inner basis eq study result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:f). -/

lemma uniformInner_basis_eq_study (f : Covariate → ℝ) (j : ℕ) :
    uniformInner f (cosineBasis j) =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineCoefficient
        (covariateExtension f) j := by
  unfold uniformInner
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineCoefficient
    uniformLaw
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure
  rw [← integral_subtype_comap measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  rw [covariateExtension_apply, cosineBasis_study]
/-- [The cosine Projection study result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:f,x). Under [the stated assumptions](hyp:x). -/

lemma cosineProjection_study (k : ℕ) (f : Covariate → ℝ) (x : Covariate) :
    cosineProjection k f x =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineProjection
        k (covariateExtension f) x := by
  unfold cosineProjection
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineProjection
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosinePolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [uniformInner_basis_eq_study]
  rfl
/-- [The holder Seminorm study result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:f). -/

lemma holderSeminorm_study (gamma : ℝ) (f : Covariate → ℝ) :
    holderSeminorm gamma f =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.holderSeminorm
        (covariateExtension f) gamma := by
  unfold holderSeminorm
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.holderSeminorm
  congr 1
  funext x
  congr 1
  funext z
  simp only [covariateExtension_apply]
/-- [The uniform L2 Norm study result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:g). -/

lemma uniformL2Norm_study (g : Covariate → ℝ) :
    uniformL2Norm g =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.extendedL2Norm
        (covariateExtension g) := by
  unfold uniformL2Norm
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.extendedL2Norm
    uniformLaw
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure
  congr 1
  rw [← lintegral_subtype_comap measurableSet_Icc]
  apply lintegral_congr
  intro x
  rw [covariateExtension_apply, sq_abs]
/-- [The study extended L2 Norm congr Icc result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:g,h). Under [the stated assumptions](hyp:h,heq). -/

lemma study_extendedL2Norm_congr_Icc {g h : ℝ → ℝ}
    (heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = h x) :
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.extendedL2Norm g =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.extendedL2Norm h := by
  unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.extendedL2Norm
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [heq x hx]

/-- [The public constant-five theorem, transported to the run's subtype and
uniform-design definitions without assuming a finite Hölder seminorm. [the documented result](goal) Under [the stated assumptions](hyp:f,hgamma,hf,hk). -/
lemma cosineProjection_error_le_holderSeminorm
    (gamma : ℝ) (f : Covariate → ℝ)
    (hgamma : HolderExponentDomain gamma) (hf : ContinuousFunctionDomain f)
    (k : ℕ) (hk : 1 ≤ k) :
    uniformL2Norm (fun x => f x - cosineProjection k f x) ≤
      5 * holderSeminorm gamma f * ENNReal.ofReal ((k : ℝ) ^ (-gamma)) := by
  have h :=
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineProjection_error_le_seminorm
    (f := covariateExtension f) (γ := gamma) (k := k)
    (covariateExtension_continuousOn hf) hgamma.1 hgamma.2 hk
  rw [← holderSeminorm_study] at h
  rw [uniformL2Norm_study]
  rw [study_extendedL2Norm_congr_Icc (g := covariateExtension
    (fun x => f x - cosineProjection k f x)) (h := fun x => covariateExtension f x -
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineProjection
        k (covariateExtension f) x) (by
          intro x hx
          simp [covariateExtension, hx]
          exact cosineProjection_study k f ⟨x, hx⟩)]
  exact h

end CausalSmith.Stat.LogoddsLowsmoothFrontier
