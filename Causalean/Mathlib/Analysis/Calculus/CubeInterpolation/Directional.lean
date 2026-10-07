module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic

/-!
# Coordinate expansion of diagonal derivatives

Finite multilinearity expands a diagonal Fréchet derivative in coordinate directions.
The expansion turns the top coordinate Hölder condition into a bound along any line.
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The order-`m` derivative evaluated repeatedly on one vector is the sum of
its coordinate partials weighted by products of that vector's coordinates. -/
theorem diagonal_derivative_coordinate_expansion {d m : ℕ}
    (u : (Fin d → ℝ) → ℝ) (x h : Fin d → ℝ) :
    iteratedFDeriv ℝ m u x (fun _ => h) =
      ∑ f : Fin m → Fin d,
        (∏ k : Fin m, h (f k)) * coordPartial m u f x := by
  classical
  let F := iteratedFDeriv ℝ m u x
  have hh : (∑ i : Fin d, Pi.single i (h i)) = h := Finset.univ_sum_single h
  calc
    F (fun _ => h) = F (fun _ => ∑ i : Fin d, Pi.single i (h i)) := by rw [hh]
    _ = ∑ f : Fin m → Fin d, F (fun k => Pi.single (f k) (h (f k))) :=
      F.map_sum (fun _ i => Pi.single i (h i))
    _ = ∑ f : Fin m → Fin d, (∏ k : Fin m, h (f k)) * coordPartial m u f x := by
      apply Finset.sum_congr rfl
      intro f _
      have heq : (fun k => Pi.single (f k) (h (f k))) =
          (fun k => h (f k) • Pi.single (f k) (1 : ℝ)) := by
        funext k
        rw [← Pi.single_smul]
        simp
      rw [heq, F.map_smul_univ]
      simp [F, coordPartial]

/-- For [a real function](hyp:u) that satisfies [the top-order Hölder condition on the normalized
cube with exponent s and constant L](hyp:hu), where [L is
nonnegative](hyp:hL), and for [two points x and y and a direction h](hyp:x,y,h) with [both points
in the cube](hyp:hx,hy), [the order-m derivative taken m times in the direction h changes between x
and y by at most (d + 1)^m times L times the distance between the points to the power s times the
length of h to the power m](goal). -/
theorem topHolder_diagonal_derivative {d m : ℕ} {s L : ℝ}
    (u : (Fin d → ℝ) → ℝ) (hL : 0 ≤ L)
    (hu : TopHolder d m s L u) (x y h : Fin d → ℝ)
    (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |iteratedFDeriv ℝ m u x (fun _ => h) -
      iteratedFDeriv ℝ m u y (fun _ => h)| ≤
      ((d : ℝ) + 1) ^ m * L * ‖x - y‖ ^ s * ‖h‖ ^ m := by
  classical
  let A : ℝ := L * ‖x - y‖ ^ s
  let B : ℝ := ‖h‖ ^ m
  have hA : 0 ≤ A := mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _)
  have hB : 0 ≤ B := pow_nonneg (norm_nonneg _) _
  have hterm (f : Fin m → Fin d) :
      |(∏ k : Fin m, h (f k)) *
          (coordPartial m u f x - coordPartial m u f y)| ≤ B * A := by
    have hc : |∏ k : Fin m, h (f k)| ≤ B := by
      rw [Finset.abs_prod]
      calc
        (∏ k : Fin m, |h (f k)|) ≤ ∏ _k : Fin m, ‖h‖ := by
          apply Finset.prod_le_prod
          · intro k _; exact abs_nonneg _
          · intro k _; exact norm_le_pi_norm h (f k)
        _ = B := by simp [B]
    rw [abs_mul]
    exact mul_le_mul hc (hu f x hx y hy) (abs_nonneg _) hB
  rw [diagonal_derivative_coordinate_expansion u x h,
    diagonal_derivative_coordinate_expansion u y h, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hsum :
      |∑ f : Fin m → Fin d,
          (∏ k : Fin m, h (f k)) *
            (coordPartial m u f x - coordPartial m u f y)| ≤
        (Fintype.card (Fin m → Fin d) : ℝ) * (B * A) := by
    calc
      _ ≤ ∑ f : Fin m → Fin d,
          |(∏ k : Fin m, h (f k)) *
            (coordPartial m u f x - coordPartial m u f y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _f : Fin m → Fin d, B * A := Finset.sum_le_sum (by
        intro f _; exact hterm f)
      _ = (Fintype.card (Fin m → Fin d) : ℝ) * (B * A) := by simp
  have hcard : (Fintype.card (Fin m → Fin d) : ℝ) ≤ ((d : ℝ) + 1) ^ m := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    gcongr
    exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ (Fintype.card (Fin m → Fin d) : ℝ) * (B * A) := hsum
    _ ≤ ((d : ℝ) + 1) ^ m * (B * A) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hB hA)
    _ = ((d : ℝ) + 1) ^ m * L * ‖x - y‖ ^ s * ‖h‖ ^ m := by
      simp only [A, B]
      ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
