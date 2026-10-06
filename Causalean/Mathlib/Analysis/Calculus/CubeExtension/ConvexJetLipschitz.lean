module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz control of lower intrinsic jets

On a convex set, a bound on the next within-set Fréchet derivative gives a
Lipschitz bound for the preceding jet. This supplies the lower-order modulus
used when a smooth cutoff is multiplied by intrinsic Hölder data.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [a set S is convex](hyp:hconv) and [has unique within-set
derivatives](hyp:huniq), [a function v is m times continuously differentiable
within S](hyp:hv), [j < m](hyp:hj), and [the order-(j + 1) within-S derivative
of v has operator norm at most R throughout S](hyp:hbound), then for [two points
x and y of S](hyp:hx,hy) [the order-j within-S derivatives of v at x and at y
differ in operator norm by at most R·‖x − y‖](goal). -/
theorem norm_iteratedFDerivWithin_sub_le_of_succ_bound
    {d j m : ℕ} {S : Set (Fin d → ℝ)}
    (hconv : Convex ℝ S) (huniq : UniqueDiffOn ℝ S)
    {v : (Fin d → ℝ) → ℝ} (hv : ContDiffOn ℝ m v S)
    (hj : j < m) {R : ℝ}
    (hbound : ∀ z ∈ S, ‖iteratedFDerivWithin ℝ (j + 1) v S z‖ ≤ R)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    ‖iteratedFDerivWithin ℝ j v S x -
      iteratedFDerivWithin ℝ j v S y‖ ≤ R * ‖x - y‖ := by
  have hdiff : DifferentiableOn ℝ (iteratedFDerivWithin ℝ j v S) S :=
    hv.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hj) huniq
  have hderiv : ∀ z ∈ S,
      ‖fderivWithin ℝ (iteratedFDerivWithin ℝ j v S) S z‖ ≤ R := by
    intro z hz
    rw [norm_fderivWithin_iteratedFDerivWithin]
    exact hbound z hz
  exact hconv.norm_image_sub_le_of_norm_fderivWithin_le hdiff hderiv hy hx

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
