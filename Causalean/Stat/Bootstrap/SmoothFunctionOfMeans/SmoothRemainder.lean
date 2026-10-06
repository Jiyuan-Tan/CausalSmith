module

public import Causalean.Stat.Inference.DeltaMethod

/-!
# First-order remainder for smooth transforms

This module isolates the deterministic analytic input to the smooth-function-of-means delta
method: Fréchet differentiability makes the nonlinear remainder little-o of the displacement.
-/

public section

namespace Causalean.Stat

open MeasureTheory Topology

noncomputable section

/-- If [a scalar transform is Fréchet differentiable at a point](hyp:hderiv), [its nonlinear
remainder after subtracting the derivative is little-o of displacement from that point](goal). -/
theorem smoothRemainder_isLittleO {d : ℕ}
    {h : EuclideanSpace ℝ (Fin d) → ℝ}
    {Dh : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {m : EuclideanSpace ℝ (Fin d)} (hderiv : HasFDerivAt h Dh m) :
    (fun z ↦ h z - h m - Dh (z - m)) =o[𝓝 m] (fun z ↦ z - m) := by
  exact hderiv.isLittleO

end

end Causalean.Stat
