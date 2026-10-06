module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-! Helpers — GaussianInjective -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Gaussian convolution is injective on compactly supported signed measures represented by Jordan pairs. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hsigma,hmu1,hmu2,hnu1,hnu2,hconv). -/
-- @node: lem:compact-gaussian-convolution-injective
lemma compact_gaussian_convolution_injective (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (mu1 mu2 nu1 nu2 : Measure ℝ) [IsFiniteMeasure mu1] [IsFiniteMeasure mu2]
    [IsFiniteMeasure nu1] [IsFiniteMeasure nu2]
    (hmu1 : mu1 (Icc (-1/2 : ℝ) (1/2))ᶜ = 0)
    (hmu2 : mu2 (Icc (-1/2 : ℝ) (1/2))ᶜ = 0)
    (hnu1 : nu1 (Icc (-1/2 : ℝ) (1/2))ᶜ = 0)
    (hnu2 : nu2 (Icc (-1/2 : ℝ) (1/2))ᶜ = 0)
    (hconv : mu1.conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) +
      nu2.conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) =
      nu1.conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) +
      mu2.conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma)))) :
    mu1 + nu2 = nu1 + mu2 := by
  -- Combine the Jordan parts before taking characteristic functions.
  have hsum : (mu1 + nu2).conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) =
      (nu1 + mu2).conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) := by
    simpa only [Measure.add_conv] using hconv
  apply Measure.ext_of_charFun
  funext t
  have hfourier := congrArg (fun μ : Measure ℝ => charFun μ t) hsum
  rw [charFun_conv, charFun_conv] at hfourier
  -- The exponential never vanishes, including at zero variance.
  have hgaussian : charFun (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) t ≠ 0 := by
    rw [charFun_gaussianReal]
    exact Complex.exp_ne_zero _
  exact mul_right_cancel₀ hgaussian hfourier

end CausalSmith.Stat.NoisydoseWeakdesignTransition
