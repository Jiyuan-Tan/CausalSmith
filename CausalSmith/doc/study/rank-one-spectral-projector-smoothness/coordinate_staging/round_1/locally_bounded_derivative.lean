import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Local boundedness of a continuously differentiable derivative

This module packages the elementary finite-dimensional consequence that a continuously differentiable function has a bounded Fréchet derivative on some neighborhood of each point.  It is independent of the matrix-specific development.
-/

open Filter
open scoped Topology

namespace Causalean.Mathlib.Analysis

/-- Given [a function between real normed vector spaces](hyp:f) and [a point in its domain](hyp:x), [the property of having a locally bounded Fréchet derivative](goal) means that one neighborhood of the point has a uniform nonnegative bound on derivative norms. -/
def HasLocallyBoundedFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : Prop :=
  ∃ U ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ‖fderiv ℝ f y‖ ≤ C

/-- Given [a function between real normed vector spaces](hyp:f), [a point in its domain](hyp:x), and [continuous differentiability at that point](hyp:hf), [the function has a locally bounded Fréchet derivative there](goal). -/
theorem ContDiffAt.hasLocallyBoundedFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) :
    HasLocallyBoundedFDerivAt f x := by
  rcases contDiffAt_one_iff.mp hf with ⟨f', U, hU, hf'cont, hfderiv⟩
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hf'contAt : ContinuousAt f' x :=
    (hf'cont x hxU).continuousAt hU
  have hnorm : ContinuousAt (fun y => ‖f' y‖) x := hf'contAt.norm
  have hbound : {y | ‖f' y‖ < ‖f' x‖ + 1} ∈ 𝓝 x :=
    hnorm (Iio_mem_nhds (lt_add_one ‖f' x‖))
  refine ⟨U ∩ {y | ‖f' y‖ < ‖f' x‖ + 1}, inter_mem hU hbound,
    ‖f' x‖ + 1, by positivity, ?_⟩
  intro y hy
  rw [(hfderiv y hy.1).fderiv]
  exact le_of_lt hy.2

end Causalean.Mathlib.Analysis
