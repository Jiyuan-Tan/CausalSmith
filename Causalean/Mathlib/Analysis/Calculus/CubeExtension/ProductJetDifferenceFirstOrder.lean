module
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# First-order difference estimate for a product jet

The first-order case isolates the two-point bilinear estimate needed in the
induction for higher within-set product jets.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [a set S has unique within-set derivatives](hyp:huniq), [two functions v
and w are continuously differentiable within S](hyp:hv,hw), and [x and y lie in
S](hyp:hx,hy), then [the first within-S derivatives of the product v·w at x and
at y differ in norm by at most ‖v(x) − v(y)‖·‖Dw(x)‖ + ‖v(y)‖·‖Dw(x) − Dw(y)‖ +
‖Dv(x) − Dv(y)‖·‖w(x)‖ + ‖Dv(y)‖·‖w(x) − w(y)‖](goal), where D denotes the
first within-S derivative; these are the four terms obtained by changing one
factor at a time in the product rule.

Use `fderivWithin_mul` (or the bilinear-map version), rewrite the difference
as two differences of products, and apply the operator-norm bounds. This is
the first nonconstant case of `norm_iteratedFDerivWithin_mul_sub_le`; the
higher-order induction still requires the corresponding bilinear estimates
for multilinear-map-valued factors. -/
theorem norm_iteratedFDerivWithin_mul_sub_le_one
    {d : ℕ} {S : Set (Fin d → ℝ)}
    (huniq : UniqueDiffOn ℝ S)
    {v w : (Fin d → ℝ) → ℝ}
    (hv : ContDiffOn ℝ 1 v S) (hw : ContDiffOn ℝ 1 w S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    ‖iteratedFDerivWithin ℝ 1 (fun z => v z * w z) S x -
      iteratedFDerivWithin ℝ 1 (fun z => v z * w z) S y‖ ≤
      ‖v x - v y‖ * ‖iteratedFDerivWithin ℝ 1 w S x‖ +
      ‖v y‖ * ‖iteratedFDerivWithin ℝ 1 w S x -
        iteratedFDerivWithin ℝ 1 w S y‖ +
      ‖iteratedFDerivWithin ℝ 1 v S x -
        iteratedFDerivWithin ℝ 1 v S y‖ * ‖w x‖ +
      ‖iteratedFDerivWithin ℝ 1 v S y‖ * ‖w x - w y‖ := by
  let M := ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Fin d → ℝ) ℝ
  have hprod (z : Fin d → ℝ) (hz : z ∈ S) :
      iteratedFDerivWithin ℝ 1 (fun t => v t * w t) S z =
        v z • iteratedFDerivWithin ℝ 1 w S z +
          w z • iteratedFDerivWithin ℝ 1 v S z := by
    ext m
    rw [iteratedFDerivWithin_one_apply (huniq.uniqueDiffWithinAt hz)]
    rw [fderivWithin_fun_mul (huniq.uniqueDiffWithinAt hz)
      ((hv.differentiableOn (by norm_num)) z hz)
      ((hw.differentiableOn (by norm_num)) z hz)]
    simp [iteratedFDerivWithin_one_apply (huniq.uniqueDiffWithinAt hz)]
  have hbound (a b c e : ℝ) (A B C D : M) :
      ‖(a • A + c • C) - (b • B + e • D)‖ ≤
        ‖a - b‖ * ‖A‖ + ‖b‖ * ‖A - B‖ +
          ‖C - D‖ * ‖c‖ + ‖D‖ * ‖c - e‖ := by
    have halg : (a • A + c • C) - (b • B + e • D) =
        (a - b) • A + b • (A - B) + c • (C - D) + (c - e) • D := by
      simp only [sub_smul, smul_sub]
      abel
    rw [halg]
    calc
      ‖(a - b) • A + b • (A - B) + c • (C - D) + (c - e) • D‖
          ≤ ‖(a - b) • A‖ + ‖b • (A - B)‖ +
              ‖c • (C - D)‖ + ‖(c - e) • D‖ := by
                calc
                  _ ≤ ‖(a - b) • A + b • (A - B) + c • (C - D)‖ +
                      ‖(c - e) • D‖ := norm_add_le _ _
                  _ ≤ (‖(a - b) • A + b • (A - B)‖ +
                      ‖c • (C - D)‖) + ‖(c - e) • D‖ := by
                        gcongr
                        exact norm_add_le _ _
                  _ ≤ ‖(a - b) • A‖ + ‖b • (A - B)‖ +
                      ‖c • (C - D)‖ + ‖(c - e) • D‖ := by
                        gcongr
                        exact norm_add_le _ _
      _ = ‖a - b‖ * ‖A‖ + ‖b‖ * ‖A - B‖ +
            ‖C - D‖ * ‖c‖ + ‖D‖ * ‖c - e‖ := by
              simp only [norm_smul]
              ring
  rw [hprod x hx, hprod y hy]
  exact hbound (v x) (v y) (w x) (w y)
    (iteratedFDerivWithin ℝ 1 w S x) (iteratedFDerivWithin ℝ 1 w S y)
    (iteratedFDerivWithin ℝ 1 v S x) (iteratedFDerivWithin ℝ 1 v S y)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
