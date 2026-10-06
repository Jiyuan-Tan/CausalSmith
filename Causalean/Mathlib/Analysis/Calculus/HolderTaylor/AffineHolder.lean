module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.AffineWithin

/-!
# Hölder data under interval normalization

The top within-interval Hölder modulus transfers to the intrinsic top
coordinate jet on the one-dimensional normalized cube. This supplies the
data expected by the existing fixed-cube interpolation theorem.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
open Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- Pulling a function back from a nondegenerate interval to the closed unit
cube scales its order-`k` within-derivative Hölder constant by the `k+α`
power of the affine slope.
[The interval, derivative-order, function, and regularity inputs](hyp:k,α,a,d,L,hd,f,hf,hholder) yield [the stated affine Hölder transfer](goal). -/
theorem affine_cube_topHolderOn
    (k : ℕ) (α a d L : ℝ) (hd : 0 < d)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ k f (Set.Icc a (a + d)))
    (hholder : ∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
      |iteratedDerivWithin k f (Set.Icc a (a + d)) x -
        iteratedDerivWithin k f (Set.Icc a (a + d)) y| ≤
          L * |x - y| ^ α) :
    TopHolderOn (cube 1) k α
      (L * (d / 2) ^ k * (d / 2) ^ α)
      (fun z : Fin 1 → ℝ => f (a + d / 2 + (d / 2) * z 0)) := by
  intro q x hx y hy
  have hc : 0 < d / 2 := by linarith
  have hmap (z : Fin 1 → ℝ) (hz : z ∈ cube 1) :
      a + d / 2 + (d / 2) * z 0 ∈ Set.Icc a (a + d) := by
    have hz0 := hz 0
    constructor <;> nlinarith [hz0.1, hz0.2]
  have hnorm : ‖x - y‖ = |x 0 - y 0| := by
    simp [Pi.norm_def, Real.norm_eq_abs]
  have hdist :
      |(a + d / 2 + (d / 2) * x 0) -
        (a + d / 2 + (d / 2) * y 0)| = (d / 2) * ‖x - y‖ := by
    rw [hnorm]
    have heq : (a + d / 2 + (d / 2) * x 0) -
        (a + d / 2 + (d / 2) * y 0) = (d / 2) * (x 0 - y 0) := by ring
    rw [heq, abs_mul, abs_of_pos hc]
  rw [affine_cube_coordJetOn k a d hd f hf q x hx,
    affine_cube_coordJetOn k a d hd f hf q y hy]
  calc
    |(d / 2) ^ k * iteratedDerivWithin k f (Set.Icc a (a + d))
        (a + d / 2 + (d / 2) * x 0) -
      (d / 2) ^ k * iteratedDerivWithin k f (Set.Icc a (a + d))
        (a + d / 2 + (d / 2) * y 0)| =
        (d / 2) ^ k *
          |iteratedDerivWithin k f (Set.Icc a (a + d))
            (a + d / 2 + (d / 2) * x 0) -
           iteratedDerivWithin k f (Set.Icc a (a + d))
            (a + d / 2 + (d / 2) * y 0)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hc) _)]
    _ ≤ (d / 2) ^ k *
          (L * |(a + d / 2 + (d / 2) * x 0) -
            (a + d / 2 + (d / 2) * y 0)| ^ α) := by
      exact mul_le_mul_of_nonneg_left
        (hholder _ (hmap x hx) _ (hmap y hy)) (pow_nonneg (le_of_lt hc) _)
    _ = (L * (d / 2) ^ k * (d / 2) ^ α) * ‖x - y‖ ^ α := by
      rw [hdist, Real.mul_rpow (le_of_lt hc) (norm_nonneg _)]
      ring

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
