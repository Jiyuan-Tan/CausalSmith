module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.MultiindexTaylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sorted Euclidean Hölder data controls diagonal within jets

Permutation invariance converts a modulus on sorted top-order coordinate
partials into a modulus on every word jet. Multilinearity then gives a
uniform diagonal estimate at arbitrary cube points, including the boundary.
This finite-sum estimate is independent of segment differentiation.
-/

public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- Take [a cube with centre b and side length H](hyp:b,H) that is [positive](hyp:hH), [a real
function u](hyp:u), and [constants L and s](hyp:L,s) with [L nonnegative](hyp:hL) and [s
positive](hyp:hs). Suppose [u is m times continuously differentiable on the cube](hyp:hu) and
[every sorted coordinate partial of total order m, taken within the cube, changes between any two
cube points by at most L times their distance to the power s](hyp:hmod). Then for [two points x and
z and a direction v](hyp:x,z,v) with [both points in the cube](hyp:hx,hz), [the order-m derivative
within the cube, taken m times in the direction v, changes between x and z by at most (d + 1)^m
times L times the distance between the points to the power s times the length of v to the power
m](goal). -/
theorem within_diagonal_topHolder_from_sorted {d m : ℕ}
    (b : EuclideanSpace ℝ (Fin d)) (H : ℝ) (hH : 0 < H)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (L s : ℝ) (hL : 0 ≤ L) (hs : 0 < s)
    (hu : ContDiffOn ℝ m u (centeredCube b H))
    (hmod : ∀ κ : ExactIndex d m, ∀ x ∈ centeredCube b H,
      ∀ z ∈ centeredCube b H,
      |coordinatePartial (centeredCube b H) u κ.1 x -
        coordinatePartial (centeredCube b H) u κ.1 z| ≤ L * ‖x - z‖ ^ s)
    (x z v : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ centeredCube b H) (hz : z ∈ centeredCube b H) :
    |iteratedFDerivWithin ℝ m u (centeredCube b H) x (fun _ => v) -
      iteratedFDerivWithin ℝ m u (centeredCube b H) z (fun _ => v)| ≤
      ((d : ℝ) + 1) ^ m * L * ‖x - z‖ ^ s * ‖v‖ ^ m := by
  classical
  have hsorted (κ : ExactIndex d m) (a : EuclideanSpace ℝ (Fin d)) :
      wordPartialWithin (centeredCube b H) u (sortedWordOfOrder κ) a =
        coordinatePartial (centeredCube b H) u κ.1 a := by
    rcases κ with ⟨κ, hκ⟩
    subst m
    rfl
  have hcount (κ : ExactIndex d m) : coordCount (sortedWordOfOrder κ) = κ.1 := by
    rcases κ with ⟨κ, hκ⟩
    subst m
    exact sortedWord_count κ
  have hword (w : Fin m → Fin d) (a : EuclideanSpace ℝ (Fin d))
      (ha : a ∈ centeredCube b H) :
      wordPartialWithin (centeredCube b H) u w a =
        coordinatePartial (centeredCube b H) u (coordCount w) a := by
    let κ : ExactIndex d m := ⟨coordCount w, coordCount_order w⟩
    calc
      _ = wordPartialWithin (centeredCube b H) u (sortedWordOfOrder κ) a := by
        apply wordPartialWithin_eq_of_count
          (centeredCube b H) u a
          (euclidean_within_jet_perm (uniqueDiffOn_centeredCube b H hH) hu ha
            (centeredCube_subset_closure_interior b H hH ha))
        exact (hcount κ).symm
      _ = _ := hsorted κ a
  -- The finite-sum estimate of CubeInterpolation.topHolder_diagonal_derivative,
  -- using Euclidean coordinate bounds in place of its Pi sup-norm bounds.
  let A : ℝ := L * ‖x - z‖ ^ s
  let B : ℝ := ‖v‖ ^ m
  have hA : 0 ≤ A := mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _)
  have hB : 0 ≤ B := pow_nonneg (norm_nonneg _) _
  have hterm (w : Fin m → Fin d) :
      |(∏ r : Fin m, v (w r)) *
          (wordPartialWithin (centeredCube b H) u w x -
            wordPartialWithin (centeredCube b H) u w z)| ≤ B * A := by
    have hc : |∏ r : Fin m, v (w r)| ≤ B := by
      rw [Finset.abs_prod]
      calc
        (∏ r : Fin m, |v (w r)|) ≤ ∏ _r : Fin m, ‖v‖ := by
          apply Finset.prod_le_prod
          · intro r _; exact abs_nonneg _
          · intro r _; exact (Real.norm_eq_abs _).symm ▸ PiLp.norm_apply_le v (w r)
        _ = B := by simp [B]
    have hm : |wordPartialWithin (centeredCube b H) u w x -
        wordPartialWithin (centeredCube b H) u w z| ≤ A := by
      rw [hword w x hx, hword w z hz]
      exact hmod ⟨coordCount w, coordCount_order w⟩ x hx z hz
    rw [abs_mul]
    exact mul_le_mul hc hm (abs_nonneg _) hB
  rw [within_diagonal_derivative_coordinate_expansion,
    within_diagonal_derivative_coordinate_expansion, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hsum :
      |∑ w : Fin m → Fin d, (∏ r : Fin m, v (w r)) *
          (wordPartialWithin (centeredCube b H) u w x -
            wordPartialWithin (centeredCube b H) u w z)| ≤
        (Fintype.card (Fin m → Fin d) : ℝ) * (B * A) := by
    calc
      _ ≤ ∑ w : Fin m → Fin d, |(∏ r : Fin m, v (w r)) *
          (wordPartialWithin (centeredCube b H) u w x -
            wordPartialWithin (centeredCube b H) u w z)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : Fin m → Fin d, B * A := Finset.sum_le_sum (by
        intro w _; exact hterm w)
      _ = (Fintype.card (Fin m → Fin d) : ℝ) * (B * A) := by simp
  have hcard : (Fintype.card (Fin m → Fin d) : ℝ) ≤ ((d : ℝ) + 1) ^ m := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    gcongr
    exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ (Fintype.card (Fin m → Fin d) : ℝ) * (B * A) := hsum
    _ ≤ ((d : ℝ) + 1) ^ m * (B * A) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hB hA)
    _ = ((d : ℝ) + 1) ^ m * L * ‖x - z‖ ^ s * ‖v‖ ^ m := by
      simp only [A, B]
      ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

