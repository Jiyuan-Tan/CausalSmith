module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.BoundaryFacts

/-!
# Extending coordinate derivative bounds to cube faces

Interior estimates for ambient coordinate partials extend to the closed cube
under `C^m` regularity on the cube. The ambient derivative convention is kept:
if a boundary derivative does not exist, Lean's derivative has its default zero
value, which also satisfies a nonnegative bound.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a function that is m times continuously differentiable on the closed normalized
cube](hyp:hu) and [a nonnegative bound B](hyp:hB), if [every coordinate partial of order at most m
is at most B in absolute value throughout the open cube](hyp:hinterior), then [the same bound holds
at every point of the closed cube](goal). -/
theorem interior_coordPartial_bound_extends {d m : ℕ}
    {u : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : ContDiffOn ℝ m u (cube d))
    (hinterior : ∀ j ≤ m, ∀ f : Fin j → Fin d,
      ∀ x ∈ openCube d, |coordPartial j u f x| ≤ B) :
    DerivBound d m B u := by
  intro j hj f x hx
  rcases ambient_jet_zero_or_within hu hj x hx with hzero | hwithin
  · simpa [coordPartial, hzero] using hB
  · simpa only [coordPartial, hwithin] using
      within_coordPartial_bound_extends hu hj f (hinterior j hj f) x hx

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
