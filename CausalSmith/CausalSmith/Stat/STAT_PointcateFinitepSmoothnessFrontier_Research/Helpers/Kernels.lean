module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Centering
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Projections

/-! Finite-moment point-CATE frontier: observable kernels and their Borel structure. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Truncation keeps the original outcome within a public absolute threshold. -/
def trunc (t y : ℝ) : ℝ := if |y| ≤ t then y else 0
/-- Thresholding an original response is Borel. -/
-- @node: measurable_trunc
@[fun_prop] lemma measurable_trunc (t : ℝ) : Measurable (trunc t) := by
  unfold trunc
  first
  | fun_prop
  | exact Measurable.ite
      (measurableSet_le (by fun_prop : Measurable fun y : ℝ => |y|) measurable_const)
      measurable_id measurable_const
/-- The truncated conditional marginal mean combines the two original arm kernels. -/
def truncatedMean (law : ObservedLaw) (t : ℝ) (x : unitInterval) : ℝ :=
  law.e x * (∫ y, trunc t y ∂law.Q true x) + (1-law.e x) * (∫ y, trunc t y ∂law.Q false x) -- @realizes gT(conditional truncated marginal mean)
/-- The multiscale projected treatment field. -/
def projectionField (law : ObservedLaw) (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) (x : unitInterval) : ℝ :=
  projOp h 0 (truncatedMean law (T 0)) x +
    ∑ j : Fin J, bandOp h (j.val+1) (truncatedMean law (T j.succ)) x -- @realizes G(P0*gT0+sum Qj*gTj)
-- @node: def:heavy-kernel
/-- All levels reuse the same outcome record in the heavy bilinear kernel. -/
def heavyKernel (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) (o z : O) : ℝ :=
  (if A o then 1 else 0) / h * (projKernel h 0 (X o) (X z) * trunc (T 0) (Y z) +
    ∑ j : Fin J, bandKernel h (j.val+1) (X o) (X z) * trunc (T j.succ) (Y z)) -- @realizes K(original-record heavy bilinear kernel)
/-- The multiscale kernel is Borel on pairs of original records. -/
-- @node: measurable_heavyKernel
@[fun_prop] lemma measurable_heavyKernel (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) :
    Measurable (fun oz : O × O => heavyKernel h J T oz.1 oz.2) := by
  unfold heavyKernel
  apply Measurable.mul
  · apply Measurable.div_const
    exact (measurable_of_finite (fun a : Bool => if a then (1 : ℝ) else 0)).comp
      (by unfold A; fun_prop)
  · unfold X Y
    fun_prop
/-- The heavy kernel centered under the original product law. -/
def heavyCentered (law : ObservedLaw) (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) : O → O → ℝ :=
  centeredKernel law.P (heavyKernel h J T) -- @realizes Kc(product-law centering)
-- @node: def:local-moments
/-- The untruncated localized covariance numerator. -/
def localNumerator (law : ObservedLaw) (h : ℝ) (J : ℕ) : ℝ :=
  h⁻¹ * ∫ x in window h, law.e x * law.m1 x - projOp h J law.e x * law.g x ∂design -- @realizes N(local numerator)
/-- The untruncated localized treatment variance denominator. -/
def localDenominator (law : ObservedLaw) (h : ℝ) (J : ℕ) : ℝ :=
  h⁻¹ * ∫ x in window h, law.e x - (projOp h J law.e x)^2 ∂design -- @realizes D(local denominator)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
